/*
 * mm.c by Michael Minogue
 * Uses a segregated list implementation of a DMA. Each size class of
 * blocks has its own free list.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

//Initial definitions as required by assignment specification
#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

//Additional concepts that will be useful
#define WSIZE      8 	     	//In bytes
#define DWORD      16 		  //Double word in bytes
#define CHUNKSIZE  (1<<8)	    //Heap extension in bytes
#define MAX_LISTS  16		//Total list count
#define MAX_LIST_SIZE ((1)<<(MAX_LISTS))  //Maximum size class

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//Gets the maximum of 2 arguments
#define MAX(x, y) ((x) > (y) ? (x) : (y))

//Add status bits into a word
#define PACK(size, prev_alloc, alloc)   ((size) | (prev_alloc) | (alloc))

//Read and write at address p
#define GET(p)              (*(size_t *)(p))
#define PUT(p, val)         (*(size_t *)(p) = (size_t)(val))

//Read in the block status fields
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_PREV_ALLOC(p)   (GET(p) & 0x2)
#define GET_ALLOC(p)        (GET(p) & 0x1)

//Change significant block bits
#define CHANGE_SIZE(p, val)  (PUT((p), PACK((val), GET_PREV_ALLOC(p), GET_ALLOC(p))))
#define CHANGE_ALLOC(p, val) (PUT((p), PACK(GET_SIZE(p), GET_PREV_ALLOC(p), (val))))
#define CHANGE_PREV(p, val)  (PUT((p), PACK(GET_SIZE(p), (val), GET_ALLOC(p))))

//Getter functions for the address of the address of the next and prev blocks.
#define NEXT_ADDRESS(ptr)            ((char *)(ptr))
#define PREV_ADDRESS(ptr)            ((char *)(ptr) + WSIZE)

//Getter functions for the address of block footers and headers
#define HDRP(ptr)            ((char *)(ptr) - WSIZE)
#define FTRP(ptr)            ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DWORD)

//Getter functions for the next and previous blocks within a list.
#define NEXT_BLOCK(ptr)       ((char *)(ptr) + GET_SIZE(((char *)(ptr) - WSIZE)))
#define PREV_BLOCK(ptr)       ((char *)(ptr) - GET_SIZE(((char *)(ptr) - DWORD)))

//Getter functions for the next and previous free lists.
#define NEXT_FLIST_ADDRESS(ptr)       ((char *)GET(ptr))
#define PREV_FLIST_ADDRESS(ptr)       ((char *)GET(PREV_ADDRESS(ptr)))

//Getter and setter functions for the first node of each free list
#define GET_ROOT(heap, list)              ((char *)GET((heap) + ((list) * WSIZE)))
#define SET_ROOT(heap, list, new_root)    (PUT((heap) + ((list) * WSIZE), (new_root)))

static void * heap_start;	//Pointer to heap start
static void * free_start;	//Pointer to array of free list starts
static void * heap_prologue; 	//Prologue header pointer
static void * heap_epilogue; 	//Epilogue header pointer

// Relevant helper functions
static int get_list(size_t size);
static void *find_fit(size_t size);
static void add_block(void *ptr);
static void remove_block(void *ptr);
static void *coalesce(void *ptr);
static void *extend_heap(size_t words);
static void *place(void *ptr, size_t size);

//Gets the relevant list based on the size of the block.
static int get_list(size_t size)
{
	short list_check = 0;
	while((size > 0) && (list_check < (MAX_LISTS-1)))
		{
			size = size & ~(1<<list_check);
			list_check++;
		}
	return list_check;
}
//Removes the node from the free list and updates neighboring nodes.
static void remove_block(void *ptr)
{
  char *next_node;
  char *prev_node;

	int list_num = get_list(GET_SIZE(HDRP(ptr)));
	prev_node = PREV_FLIST_ADDRESS(ptr);
	next_node = NEXT_FLIST_ADDRESS(ptr);
  //Case 1: Pointer is the only node in the list.
	if((prev_node == NULL) && (next_node == NULL))
		{
			SET_ROOT(free_start, list_num, NULL);
		}
  //Case 2: Pointer is the last node in the list.
	else if(next_node == NULL)
		{
			PUT(NEXT_ADDRESS(prev_node), NULL);
		}
  //Case 3: Pointer is the first node in the list.
  else if(prev_node == NULL)
  	{
  		SET_ROOT(free_start, list_num, next_node);
  		PUT(PREV_ADDRESS(next_node), NULL);
  	}
  //Case 4: Pointer is a middle node being removed.
	else
		{
      PUT(PREV_ADDRESS(next_node), prev_node);
			PUT(NEXT_ADDRESS(prev_node), next_node);
		}
	//Set current block to null.
  PUT(PREV_ADDRESS(ptr), NULL);
	PUT(NEXT_ADDRESS(ptr), NULL);
}

//Helper function for adding a new block
static void add_block(void *ptr)
{
	int list_num = get_list(GET_SIZE(HDRP(ptr)));
	char* new_ptr = ptr;

  PUT(NEXT_ADDRESS(ptr), NULL);
	PUT(PREV_ADDRESS(ptr), NULL);

	char *root_trace = GET_ROOT(free_start, list_num);
  //Case 1: list is empty
	if(root_trace == NULL)
		{
      //Set the root as the new block
			SET_ROOT(free_start, list_num, ptr);
			return;
		}
  //Case 2: Empty root node, but existing nodes in list.
	else if(root_trace > new_ptr)
		{
      //Set new block as root, point forward to old root.
			SET_ROOT(free_start, list_num, ptr);
			PUT(NEXT_ADDRESS(ptr), root_trace);
			PUT(PREV_ADDRESS(root_trace), ptr);
			return;
		}
  //Case 3: Only root node exists.
	else if(NEXT_FLIST_ADDRESS(root_trace) == NULL)
		{
      //Set new block as next address from root.
      PUT(NEXT_ADDRESS(root_trace), ptr);
			PUT(PREV_ADDRESS(ptr), root_trace);
			return;
		}
    //Iterate until we cannot find a next address or have surpassed pointer
	while(root_trace < new_ptr && NEXT_FLIST_ADDRESS(root_trace) != NULL )
		{
			root_trace = NEXT_FLIST_ADDRESS(root_trace);
		}
  char *next = NEXT_FLIST_ADDRESS(root_trace);
	char *prev = PREV_FLIST_ADDRESS(root_trace);
  //Case 4: We reach the last node in the list.
	if(next == NULL)
		{
			if(new_ptr <= root_trace)
				{
          PUT(PREV_ADDRESS(root_trace), new_ptr);
          PUT(NEXT_ADDRESS(new_ptr), root_trace);
          PUT(PREV_ADDRESS(new_ptr), prev);
          PUT(NEXT_ADDRESS(prev), new_ptr);
				}
			else
				{
          PUT(NEXT_ADDRESS(root_trace), new_ptr);
					PUT(PREV_ADDRESS(new_ptr), root_trace);
				}
		}
  //Case 5: We reach a middle node at some point
	else
		{
			PUT(NEXT_ADDRESS(new_ptr), root_trace);
			PUT(PREV_ADDRESS(new_ptr), prev);
			PUT(NEXT_ADDRESS(prev), new_ptr);
			PUT(PREV_ADDRESS(root_trace), new_ptr);
		}
}
//Attempts to coalesces neighboring free blocks
static void * coalesce(void * ptr)
{
  size_t list_num;
  size_t other_block_size;
	size_t prev_block_alloc;
	size_t next_block_alloc;
	size_t ptr_size;

	char *prev_block;
	char *next_block;

	prev_block_alloc = GET_PREV_ALLOC(HDRP(ptr));
	next_block = NEXT_BLOCK(ptr);
	next_block_alloc = GET_ALLOC(HDRP(next_block));

	ptr_size = GET_SIZE(HDRP(ptr));
	//Case 1: Next block is free, previous is not.
	if(prev_block_alloc && !next_block_alloc)
		{
			ptr_size += GET_SIZE(HDRP(next_block));

			remove_block(next_block);
			PUT(HDRP(ptr), PACK(ptr_size, 2, 0));
			PUT(FTRP(ptr), PACK(ptr_size, 2, 0));
			add_block(ptr);
		}
  //Case 2: previous block not allocated, next block is.
  else if(!prev_block_alloc && next_block_alloc)
    {
      prev_block = PREV_BLOCK(ptr);
      other_block_size = GET_SIZE(HDRP(prev_block));
      ptr_size += other_block_size;

      list_num = get_list(other_block_size);

      //Remove from current list and add to new list if size
      //category changes
      if((1 << list_num) <=  ptr_size)
        {
          remove_block(prev_block);
          ptr = prev_block;
          PUT(HDRP(ptr), PACK(ptr_size, 2, 0));
          PUT(FTRP(ptr), PACK(ptr_size, 2, 0));
          add_block(ptr);
          return ptr;
        }
      else //No size change no need to update list, just pointers
        {
          ptr = prev_block;
          PUT(HDRP(ptr), PACK(ptr_size, 2, 0));
          PUT(FTRP(ptr), PACK(ptr_size, 2, 0));
          return ptr;
        }
    }
    //Case 3: Both blocks in use
  else if(prev_block_alloc && next_block_alloc)
  		{
  			add_block(ptr);
  		}

	//Case 4: Both blocks free
	else
		{
			prev_block = PREV_BLOCK(ptr);
			remove_block(next_block);
			ptr_size += GET_SIZE(HDRP(prev_block)) + GET_SIZE(HDRP(next_block));
			list_num = get_list(GET_SIZE(HDRP(prev_block)));


			if((1 << list_num) > ptr_size)
				{
					ptr = prev_block;
					PUT(HDRP(ptr), PACK(ptr_size, 2, 0));
					PUT(FTRP(ptr), PACK(ptr_size, 2, 0));
					return ptr;
				}
			else{
					remove_block(prev_block);

					ptr = prev_block;
					PUT(HDRP(ptr), PACK(ptr_size, 2, 0));
					PUT(FTRP(ptr), PACK(ptr_size, 2, 0));

					add_block(ptr);
					}
		}
	return ptr;
}

/*
 * Extend heap by the number of words necessary
 */
static void * extend_heap(size_t words)
{
	size_t size;
  char *ptr;
  // Allocate even words for alignment
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	//Get allocation of status of last pre-epilogue block
	size_t end_alloc = GET_PREV_ALLOC(heap_epilogue);

	if((long)(ptr = mem_sbrk(size)) == -1){
		return NULL;
  }
	PUT(HDRP(ptr), PACK(size, end_alloc, 0));
	PUT(FTRP(ptr), PACK(size, end_alloc, 0));
	PUT(HDRP(NEXT_BLOCK(ptr)), PACK(0, 0, 1));
	heap_epilogue = HDRP(NEXT_BLOCK(ptr));

	//Add new block. If last block was free, coalesce first.
	if(end_alloc)
		{
      add_block(ptr);
			return ptr;
		}
	else
		{
      return coalesce(ptr);
		}
}

//Searches all lists to find a fit for malloc
static void * find_fit(size_t size)
{
	int list_num = get_list(size);
	char *ptr;

	while(list_num < MAX_LISTS)
		{
			ptr = GET_ROOT(free_start, list_num);
			while(ptr != NULL)
				{
					if(size <= GET_SIZE(HDRP(ptr))){
						return ptr;
          }
					ptr = NEXT_FLIST_ADDRESS(ptr);
				}
					list_num++;
		}
    return NULL;
}

/*
 * place - updates flags and headers and splits the block if needed
 */
static void * place(void *ptr, size_t size)
{
  size_t old_size;
  size_t frag_count;
	size_t next_block_size;
  char *split_block;
	char *next_block;

	next_block = NEXT_BLOCK(ptr);
	next_block_size = GET_SIZE(HDRP(next_block));

	old_size = GET_SIZE(HDRP(ptr));
	frag_count = old_size - size;

	remove_block(ptr);
  //If the fragmentation is bad, split the blocks.
	if(frag_count > (1<<6))
		{
			PUT(HDRP(next_block), PACK(next_block_size, 0, 1));
			PUT(HDRP(ptr), PACK(size, 2, 1));
			//Split the block and update headers
			split_block = NEXT_BLOCK(ptr);
			PUT(HDRP(split_block), PACK(frag_count, 2, 0));
			PUT(FTRP(split_block), PACK(frag_count, 2, 0));
			add_block(split_block);
		}
  //Case if the block does not need to be split
	else
		{
			PUT(HDRP(next_block), PACK(next_block_size, 2, 1));
			PUT(HDRP(ptr), PACK(old_size, 2, 1));
		}
	return ptr;
}

/*
 * mm_init - Allocates memory to the heap and begins list of free lists.
 */
int mm_init(void)
{
	//Verify memory allocation
	if((heap_prologue = mem_sbrk((MAX_LISTS + 3) * WSIZE)) == (void *)-1 ){
		return -1;
  }
	//Set the start of the free list array to the beginning of the heap
	free_start = heap_prologue;
	heap_prologue += ((MAX_LISTS + 1) * WSIZE);
  //Create word space.
	int i = 0;
	while(i < MAX_LISTS)
		{
			PUT(free_start + (i * WSIZE), NULL);
			i++;
		}
	PUT(HDRP(heap_prologue), PACK(DWORD, 2, 1));
	PUT(FTRP(heap_prologue), PACK(DWORD, 2, 1));
	heap_epilogue = HDRP(NEXT_BLOCK(heap_prologue));
	PUT(heap_epilogue, PACK(0, 2, 1));           /* Epilogue footer */

	if((heap_start = extend_heap(CHUNKSIZE/WSIZE)) == NULL){
		return -1;
  }
	return 0;
}

/*
 * mm_malloc - Increment the pointer by size to allocate a block.
 */
void *mm_malloc(size_t size)
{
	if(size == 0){ //No point in allocating an empty block!
		return NULL;
  }
	size_t extend_size;
	char *ptr;
  if(size <= 32) //32 bytes is our minimum block size. This verifies at least minimum
		{
			size = 2 * 32;
		}
	else
		{
			size = DWORD * ((size + (DWORD) + (DWORD-1)) / DWORD);
		}

	//Use find_fit helper function to find a free block
	if((ptr = find_fit(size)) != NULL )
		{
			place(ptr, size);
			return ptr;
		}
	//If nothing is found, we will need to extend a current block.
	extend_size = MAX(size, CHUNKSIZE);
	if((ptr = extend_heap(extend_size/WSIZE)) == NULL ){
		return NULL;
  }
	place(ptr, size);
	return ptr;
}

/*
 * mm_free - Works via immediate coalescing.
 */
void mm_free(void *ptr)
{
  size_t prev_block_alloc;
  size_t next_block_size;
  size_t next_block_alloc;
	size_t ptr_size;
	char *next_block;

	ptr_size = GET_SIZE(HDRP(ptr));
	next_block = NEXT_BLOCK(ptr);

	prev_block_alloc = GET_PREV_ALLOC(HDRP(ptr));
	next_block_size = GET_SIZE(HDRP(next_block));
	next_block_alloc = GET_ALLOC(HDRP(next_block));

	PUT(HDRP(ptr), PACK(ptr_size, prev_block_alloc, 0));
	PUT(FTRP(ptr), PACK(ptr_size, prev_block_alloc, 0));
	PUT(HDRP(next_block), PACK(next_block_size, 0, next_block_alloc));

	if(!next_block_alloc){
		PUT(FTRP(next_block), PACK(next_block_size, 0, 0));
  }
	coalesce(ptr); //After freeing, coalesce.
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	char *split_ptr;

	if(ptr == NULL){
		return mm_malloc(size);
  }
	if(size == 0)
		{
			mm_free(ptr);
			return NULL;
		}

	void *new_ptr = ptr;
	size_t old_size = GET_SIZE(HDRP(ptr));
	size_t old_prev_alloc = GET_PREV_ALLOC(HDRP(ptr));
  if(size <= 32) //32 bytes is our minimum block size. This verifies at least minimum
		{
			size = 2 * 32;
		}
	else
		{
			size = DWORD * ((size + (DWORD) + (DWORD-1)) / DWORD);
		}
	void *next_ptr = NEXT_BLOCK(ptr);
	size_t next_alloc = GET_ALLOC(HDRP(next_ptr));
	size_t next_size = GET_SIZE(HDRP(next_ptr));
  //Case 1: No change in size
	if(size == old_size){
		return ptr;
  }
  //Case 2: Larger size. Block will grow.
  else if(size > old_size)
    {
      if(!next_alloc && (next_size + old_size) > size)
        {
          remove_block(next_ptr);
          PUT(HDRP(ptr), PACK((next_size + old_size), old_prev_alloc, 1));
          next_ptr = NEXT_BLOCK(ptr);
          next_size = GET_SIZE(HDRP(next_ptr));
          PUT(HDRP(NEXT_BLOCK(ptr)), PACK(next_size, 2, 1));
        }
      else
        {
          new_ptr = mm_malloc(size);
          if(new_ptr == NULL){
            return NULL;
          }
          memcpy(new_ptr, ptr, size);
          mm_free(ptr);
          return new_ptr;
        }
    }
  //Case 3: Smaller size. Block will be split.
  else if((0) && !next_alloc)
    {
      if((old_size - size) >(1<<30))
        {
          PUT(HDRP(ptr), PACK(size, GET_PREV_ALLOC(HDRP(ptr)), 1));
          split_ptr = NEXT_BLOCK(ptr);
          PUT(HDRP(split_ptr), PACK((old_size - size), 2, 1));
          mm_free(split_ptr);
        }
    }
	return new_ptr;
}
