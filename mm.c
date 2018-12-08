/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "IT",
    /* First member's full name */
    "Jiawei Zhang",
    /* First member's email address */
    "jiaweizhang2021@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Ignacio de Osma",
    /* Second member's email address (leave blank if none) */
    "ignaciodeosma2019@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//newly defined macros
#define WSIZE = 4 //word and header/footer size
#define DSIZE = 8 //double size
#define CHUNKSIZE (1<<6)
#define LISTCOUNT = 20
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) > (y) ? (y) : (x))
#define blockInfo(size, alloc) ((size) | (alloc)) //put the size and allocated bit into a word

//read and write at the address
#define READ(p) (*(unsigned int *)(p))
#define WRITE(p, val) (*(unsigned int *)(p) = val)

//read the size field at the address
#define READ_SIZE(p) (READ(p) & ~0x7)

//read the allocated field at the address
#define READ_ALLOC(p) (READ(p) & 0x1)

//get header and footer address of a given block address
#define getHeader(p) ((char *)(p) - WSIZE)
#define getFooter(p) ((char *)(p) + READ_SIZE(getHeader(p)) - DSIZE)

//get the next block
#define next_block(p) ((char *)(p) + READ_SIZE(((char *)(p) - WSIZE)))

//get the previous block
#define prev_block(p) ((char *)(p) - READ_SIZE(((char *)(p) - DSIZE)))





//prepare the segList Variables

//global variables
static void *segregatedListPtr;
static char *heapListPtr = 0; 

//set the prev and next field of p to address new pointer
//HOW SO?????

#define insert_ptr(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

//get the address of the prev field of a free block in the segList
#define prevField(p) ((char *)p)

//get the address of the next field of a free block in the segList
#define nextField(p) ((char *)(p) + WSIZE)

//get the actual address of the prev block in the seglist
#define seg_prevBlock(p) (*(char **)p)

//get the actual address of the next block in the seglist
#define seg_nextBlock(p) (*(char **)(nextField(p)))


//get the pointer at the index of the seglist 
#define seg_getIndex(ptr, index)  (*((char **)ptr + index))



//helper function declaration
static void* coalesce(void *p); //finished Tony
static void* extendHeap(size_t words);  //finished Tony
static void* findFit(size_t sizeNeeded); // working Tony
static void* place(void *p, size_t size);
static void  insertFreeBlock(void *p, size_t blockSize);
static void  removeFreeBlock(void *p);
static int mm_check(void); //what does this do?


/*
 * findFit: return the smallest block that can hold the requested data size
 * scanning from the head of each list, which always holds the biggest data block in this list
 */

static void* findFit(size_t sizeNeeded){
	size_t size = sizeNeeded;
	int listIndex = 0;
	void* listPtr = null;

	while(listIndex < LISTCOUNT){
		if(listIndex == LISTCOUNT - 1 || (size <= 1 && (seg_getIndex(segregatedListPtr, listIndex) != NULL)))
		{
			listPtr = seg_getIndex(segregatedListPtr, listIndex);

			//we are at a specific sized list, now we traverse the list
			while((listPtr != NULL) && (sizeNeeded > READ_SIZE(getHeader(listPtr)))){
				listPtr = seg_prevBlock(listPtr); 
				//techinically going down the list, but because of the way the memory is structured,
				//we call prevBlock.
			}

			//found the location
			if(listPtr != NULL){
				break;
			}
		}
		listIndex++; //move along the sizes list
		size = size >> 1; //track size and if it fits

	}

	return listPtr;

} 

/*
 * removeFreeBlock: remove a free block from the seg_list and update its pre, next pointer
 */

static void removeFreeBlock(void* p){
  int listIndex = 0;


}

/*
 * coalesce: join the freed block with its previous and next ones
                check the four scenarios!
 */

static void* coalesce(void* p){
    size_t prev_alloc_flag = READ_ALLOC(getHeader(prev_block(p)));
    size_t next_alloc_flag = READ_ALLOC(getHeader(next_block(p)));

    size_t totalSize = READ_SIZE(getHeader(p)); 


    //case 1: allocated | just freed | allocated , so coalesce is possible
    if(prev_alloc_flag && next_alloc_flag){
      return p;
    }
    //case 2: allocated | just freed | free, so coalesce with the next block
    else if(prev_alloc_flag && !next_alloc_flag){
      removeFreeBlock(p);
      removeFreeBlock(next_block(p));
      totalSize += READ_SIZE(getHeader(next_block(p))); //read the size of the next block (free)
      WRITE(getHeader(p), blockInfo(size, 0)); //write the header field of this block and mark it free
      WRITE(getFooter(p), blockInfo(size, 0)); //similar to up there
    }
    //case 3: free | just freed | allocated, so coalesce with the previous block and then move the pointer to
    //the previous block address
    else if(!prev_alloc_flag && next_alloc_flag){
    	removeFreeBlock(p);
    	removeFreeBlock(prev_block(p));
    	totalSize += READ_SIZE(getHeader(prev_block(p)));
    	WRITE(getFooter(p), blockInfo(totalSize, 0)); //change the curr block's footer (size, free)
    	WRITE(getHeader(prev_block(p)), blockInfo(totalSize, 0)); 

    	p = prev_block(p); //move the free block pointer to the previous block
    }
    //case 4: free| just freed | free, so coalesce with both of them
    else{
    	removeFreeBlock(prev_block(p));
    	removeFreeBlock(p);
    	removeFreeBlock(next_block(p));
    	totalSize += READ_SIZE(getHeader(prev_block(p))) + READ_SIZE(getHeader(next_block(p)));
    	WRITE(getFooter(next_block(p)), blockInfo(totalSize, 0)); //write the footer at the next free block
    	WRITE(getHeader(prev_block(p)), blockInfo(totalSize, 0)); //write the header at the prev free block

    	p = prev_block(p);
    }
    //put the block pointer back into the free seg list
    insertFreeBlock(p, totalSize);

    return p;
    
}


/*
 * extendHeap: extend the heap hby requestin block of CHUNKSIZE byte
 */ 

static void* extendHeap(size_t words){
    char* blockPtr;

    size_t size; 

    //make sure the the size allocated is an even number
    if(words % 2 == 1){
        size = (words + 1) * WSIZE;
    }
    else{
        size = words * WSIZE;
    }

    if((long)(blockPtr = mem_sbrk(size)) == -1)
        return NULL;

    //initialize the free block header/footer and the epilogue header
    WRITE(getHeader(blockPtr), blockInfo(size, 0)); //free block header
    WRITE(getFooter(blockPtr), blockInfo(size, 0)); //free block footer
    WRITE(getHeader(next_block(blockInfo)), blockInfo(0, 1));
    insertFreeBlock(blockPtr, size);

    return coalesce(blockPtr); //coalesce just in case the last block is a free block
}

/* 
 * mm_init - initialize the malloc package. Tony Finished
 */
int mm_init(void)
{
  int listIndex;
  segregatedListPtr = mem_sbrk(LISTCOUNT * WSIZE);


  //initialize the list and set all blocks to null
  for(listIndex = 0; listIndex < listIndex; listIndex++){
    seg_getIndex(segregatedListPtr, listIndex);
  }

  //create the heap

  if((heapListPtr = mem_sbrk(4 * WSIZE)) == (void *) - 1){
    return -1;
  }

  WRITE(heapListPtr, 0); //alignment padding, intentionally left blank
  WRITE(heapListPtr + (1 * WSIZE), blockInfo(DSIZE, 1)); //prologue header
  WRITE(heapListPtr + (2 * WSIZE), blockInfo(DSIZE, 1)); //prologue footer
  WRITE(heapListPtr + (3 * WSIZE), blockInfo(0, 1)); //epilogue header

  heapListPtr += (2 * WSIZE); //move heap pointer in between the header and footer?

  if(extendHeap(CHUNKSIZE/WSIZE) == NULL){
    return -1;
  }

  return 0;

}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














