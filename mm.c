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
    "TI",
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

//newly defined macros
#define WSIZE 4 //word and header/footer size
#define DSIZE 8 //double size
#define CHUNKSIZE (1<<6)
#define EXTENDCHUNKSIZE (1 << 12)
#define LISTCOUNT 20
#define REALLOC_BUFFER (1 << 7)
#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(X, Y) ((x) > (y) ? (y) : (x))
#define blockInfo(size, alloc) ((size) | (alloc)) //put the size and allocated bit into a word

//read and WRITE at the address
#define READ(p) (*(unsigned int *)(p))
#define WRITE(p, val) (*(unsigned int *)(p) = (val))

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
void* segregatedListPtr[LISTCOUNT];
// static char* heapListPtr = 0;


#define insert_ptr(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

//get the address of the prev field of a free block in the segList
#define prevField(p) ((char *)p)

//get the address of the next field of a free block in the segList
#define nextField(p) ((char *)(p) + WSIZE)

//get the actual address of the prev block in the seglist
#define seg_prev_block(p) (*(char **)p)

//get the actual address of the next block in the seglist
#define seg_next_block(p) (*(char **)(nextField(p)))


//get the pointer at the index of the seglist
#define seg_getIndex(ptr, index)  *((char **)ptr + index)



//helper function declaration
static void* coalesce(void *p); //finished Tony checked
static void* extendHeap(size_t words);  //finished Tony //checked
static void* place(void *p, size_t size); //finished Tony check
static void  insertFreeBlock(void *p, size_t blockSize); //checked
static void  removeFreeBlock(void *p); //check
//static int mm_check(void); //basically a debugger, wont call during the acutal submission, for style points

/*
 * place: mark the size at pointer as used, if the payload is smaller than the free block, coalesce the free block
 * with the adjacent blocks
 */


/*
 * extendHeap: extend the heap hby requestin block of CHUNKSIZE byte
 */

static void* extendHeap(size_t size){
    void* blockPtr;
    size_t alignedSize;

    alignedSize = ALIGN(size);

    if((blockPtr = mem_sbrk(alignedSize)) == (void*)-1)
        return NULL;

    //initialize the free block header/footer and the epilogue header
    WRITE(getHeader(blockPtr), blockInfo(alignedSize, 0)); //free block header
    WRITE(getFooter(blockPtr), blockInfo(alignedSize, 0)); //free block footer
    WRITE(getHeader(next_block(blockPtr)), blockInfo(0, 1));
    insertFreeBlock(blockPtr, size);

    //mm_check();
    return coalesce(blockPtr); //coalesce just in case the last block is a free block
}


static void insertFreeBlock(void *p, size_t blockSize) {
  void *ptr = NULL;
  void *insertPtr = NULL;
  int listIndex = 0;

  /* find list index of block we want to insert - same idea as with removeFreeBlock */
  while((listIndex < (LISTCOUNT - 1)) && (blockSize > 1)){
    blockSize = blockSize >> 1;
    listIndex++;
  }

  ptr = segregatedListPtr[listIndex];
  /* find location to insert, making sure list is sorted by block size */
  while ((ptr != NULL) && (blockSize > READ_SIZE(getHeader(ptr)))) {
    insertPtr = ptr;
    ptr = seg_prev_block(ptr);
  }


  if(ptr != NULL){
    if(insertPtr != NULL){
      insert_ptr(prevField(p), ptr);
      insert_ptr(nextField(ptr), p);
      insert_ptr(nextField(p), insertPtr);
      insert_ptr(prevField(insertPtr), p);
    }
    else{
      insert_ptr(prevField(p), ptr);
      insert_ptr(nextField(ptr), p);
      insert_ptr(nextField(p), NULL);
      segregatedListPtr[listIndex] = p;
    }
  }
  else{
    if(insertPtr != NULL){
      insert_ptr(prevField(p), NULL);
      insert_ptr(nextField(p), insertPtr);
      insert_ptr(prevField(insertPtr), p);
    }
    else{
      insert_ptr(prevField(p), NULL);
      insert_ptr(nextField(p), NULL);
      segregatedListPtr[listIndex] = p; 
    }
  }
  return; 
}




/*
 * removeFreeBlock: remove a free block from the seg_list and update its pre, next pointer
 */


static void removeFreeBlock(void* p){
  int listIndex = 0;
  size_t blockSize = READ_SIZE(getHeader(p));

  while(listIndex < LISTCOUNT - 1 && blockSize > 1){
    blockSize >>= 1;
    listIndex++;
  }

  if(seg_prev_block(p) != NULL){
    if(seg_next_block(p) != NULL){
      insert_ptr(nextField(seg_prev_block(p)), seg_next_block(p));
      insert_ptr(prevField(seg_next_block(p)), seg_prev_block(p));
    }
    else{
      insert_ptr(nextField(seg_prev_block(p)), NULL);
      segregatedListPtr[listIndex] = seg_prev_block(p);
    }
  }
  else{
    if(seg_next_block(p) != NULL){
      insert_ptr(prevField(seg_next_block(p)), NULL);
    }
    else{
      segregatedListPtr[listIndex] = NULL;
    }
  }

  return; 
}

/*
 * coalesce: join the freed block with its previous and next ones
                check the four scenarios!
 */

static void* coalesce(void* p){
    size_t prev_alloc_flag = READ_ALLOC(getHeader(prev_block(p)));
    size_t next_alloc_flag = READ_ALLOC(getHeader(next_block(p)));

    size_t totalSize = READ_SIZE(getHeader(p));


    //case 1: allocated | just freed | allocated , so coalesce is impossible
    if(prev_alloc_flag && next_alloc_flag){
      return p;
    }
    //case 2: allocated | just freed | free, so coalesce with the next block
    else if(prev_alloc_flag && !next_alloc_flag){
      removeFreeBlock(p);
      removeFreeBlock(next_block(p));
      totalSize += READ_SIZE(getHeader(next_block(p))); //read the size of the next block (free)
      WRITE(getHeader(p), blockInfo(totalSize, 0)); //WRITE the header field of this block and mark it free
      WRITE(getFooter(p), blockInfo(totalSize, 0)); //similar to up there
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
      removeFreeBlock(p);
      removeFreeBlock(prev_block(p));
      removeFreeBlock(next_block(p));
      totalSize += READ_SIZE(getHeader(prev_block(p))) + READ_SIZE(getHeader(next_block(p)));
      WRITE(getFooter(next_block(p)), blockInfo(totalSize, 0)); //WRITE the footer at the next free block
      WRITE(getHeader(prev_block(p)), blockInfo(totalSize, 0)); //WRITE the header at the prev free block
      p = prev_block(p);
    }
    //put the block pointer back into the free seg list
    insertFreeBlock(p, totalSize);
    //mm_check();
    return p;

}
static void* place(void* p, size_t size){

	size_t blockSize = READ_SIZE(getHeader(p));
	size_t sizeDiff = blockSize - size;
	//break the current block pointed by p from the segregated list
  
	removeFreeBlock(p);
//if the difference between block size and payload size is bigger than the min-block size => 2 * DSIZE
  //then coalesce
  if(sizeDiff <= DSIZE * 2){
    WRITE(getHeader(p), blockInfo(size, 1));
    WRITE(getFooter(p), blockInfo(size, 1));
  }
	else if(size >= 100){ //200 is subject to change
		//we will store the payload at the end and have the beginning as free block
    //prepare the free space
    WRITE(getHeader(p), blockInfo(sizeDiff, 0));
    WRITE(getFooter(p), blockInfo(sizeDiff, 0));
		//WRITE the payload data
		WRITE(getHeader(next_block(p)), blockInfo(size, 1));
		WRITE(getFooter(next_block(p)), blockInfo(size, 1));
		//insert the free leftover into the seglist
		insertFreeBlock(p, sizeDiff);
    return next_block(p);
	}
  
	else{
    WRITE(getHeader(p), blockInfo(size, 1));
    WRITE(getFooter(p), blockInfo(size, 1));
		WRITE(getHeader(next_block(p)), blockInfo(sizeDiff, 0));
		WRITE(getFooter(next_block(p)), blockInfo(sizeDiff, 0));
		insertFreeBlock(next_block(p), sizeDiff);
	}
	
  //mm_check();
	return p;
}



 /*
 * mm_check: checks heap consistency. 0 => normal, -1 => error
 */

/*
static int mm_check(void){
	int errorCode = 0;
	int listIndex;
	void* blockPtr = NULL;
	void* nextPtr = NULL;
	void* tempPtr = NULL;

	//traverse the entire seg list
	for(listIndex = 0; listIndex < LISTCOUNT; listIndex++){
		blockPtr = seg_getIndex(segregatedListPtr, listIndex);
		//check if every block is marked free
		while(blockPtr != NULL){
			if(READ_ALLOC(getHeader(blockPtr))){
				//different from peter, didnot use getheader
				printf("block is not marked as free");
				errorCode = -1;
			}
			blockPtr = seg_prev_block(blockPtr);
		}
	}

	//traverse the entire heap
	blockPtr = heapListPtr;
	nextPtr = NULL;

	while(READ_ALLOC(getHeader(blockPtr)) != 1 && READ_SIZE(getHeader(blockPtr)) != 1){

		nextPtr = next_block(blockPtr);

		//check alignment, if the blockPtr is not 8-byte aligned, retun -1;
		if((unsigned int)blockPtr % DSIZE){
			errorCode = -1;
			printf("block is not 8-byte aligned");
		}

		//check the footer and header matches
		if(READ_SIZE(getFooter(blockPtr)) != READ_SIZE(getHeader(blockPtr))){
			printf("header size and footer size dont match");
			errorCode = -1;
		}

		if(READ_ALLOC(getFooter(blockPtr)) != READ_SIZE(getHeader(blockPtr))){
			printf("allocation flag of header and footer dont match");
		}


		//check if two free blocks are together (not coalesced)
		if(! (READ_ALLOC(getHeader(blockPtr)) || READ_ALLOC(getHeader(nextPtr)))){
			errorCode = -1;
			printf("two free blocks are not coalesced");
		}

		//check if every free block is in the segList
		if(!READ_ALLOC(getHeader(blockPtr))){
			int listIndex;
			//iterate the sizes seglist
			for(listIndex = 0; listIndex < LISTCOUNT; listIndex++){
				tempPtr = seg_getIndex(segregatedListPtr, listIndex);
				//now iterate all free blocks in this list
				while(tempPtr != NULL){
					if(tempPtr == blockPtr){
						break; //good its in the list
					}
					tempPtr = seg_prev_block(tempPtr);
				}
			}

			if(tempPtr != blockPtr){
				errorCode = -1;
				printf("free block not in segList");
			}
		}

		blockPtr = seg_prev_block(blockPtr);
	}
	return errorCode; 

}
*/

/*
 * mm_init - initialize the malloc package. Tony Finished
 */
int mm_init(void)
{
  
  int listIndex;
  char* heap_start; //potiner to the heap
  //segregatedListPtr = mem_sbrk(LISTCOUNT * WSIZE);


  //initialize the list and set all blocks to null
  for(listIndex = 0; listIndex < LISTCOUNT; listIndex++){
    segregatedListPtr[listIndex] = NULL;
  }

  //create the heap

  if((long)(heap_start = mem_sbrk(WSIZE * 4)) == -1){
    return -1;
  }

  WRITE(heap_start, 0); //alignment padding, intentionally left blank
  WRITE(heap_start + (1 * WSIZE), blockInfo(DSIZE, 1)); //prologue header
  WRITE(heap_start + (2 * WSIZE), blockInfo(DSIZE, 1)); //prologue footer
  WRITE(heap_start + (3 * WSIZE), blockInfo(0, 1)); //epilogue header

  if(extendHeap(CHUNKSIZE) == NULL){
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
    size_t finalSize;
    size_t heapExtend;
    size_t searchSize;
    int listIndex = 0;
    char* tempPtr = NULL;
    void* result;

    //edge case
    if(size == 0){
    	return NULL;
    }

    //adjust the size to fit the paddling and alignment, bc the min-block size is 4 * WSIZE
   	if(size <= DSIZE){
   		finalSize = DSIZE * 2;
   	}
   	else{
   		finalSize = ALIGN(size + DSIZE);
   	}

 	  //try to find a spot to fit the block
    searchSize = finalSize;

    while(listIndex < LISTCOUNT){
      if((listIndex == LISTCOUNT - 1) || ((searchSize <= 1) && (segregatedListPtr[listIndex] != NULL))){
        tempPtr = segregatedListPtr[listIndex];
        while((tempPtr != NULL) && (finalSize > READ_SIZE(getHeader(tempPtr)))){
          tempPtr = seg_prev_block(tempPtr);
        //techinically going down the list, but because of the way the memory is structured,
        //we call prev_block.
        }
        if(tempPtr != NULL)
          break; 
      }
      searchSize >>= 1;
      listIndex++; 
    }

   	if(tempPtr != NULL){ //different from peter
   		result = place(tempPtr, finalSize);
   		return result;
   	}
   	else{
   		heapExtend = MAX(finalSize, EXTENDCHUNKSIZE);
   		tempPtr = extendHeap(heapExtend);
   		if(tempPtr == NULL){
   			return NULL;
   		}
   		result = place(tempPtr, finalSize);
   		return result;
   	}
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
	size_t size = READ_SIZE(getHeader(ptr));

	//mark the free bit
	WRITE(getHeader(ptr), blockInfo(size, 0));
	WRITE(getFooter(ptr), blockInfo(size, 0));

	insertFreeBlock(ptr, size);

	coalesce(ptr);

  //mm_check();

  return; 
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	void* oldPtr = ptr;
	void* newPtr;
	void* nextPtr;
	size_t alignedSize, nextSize;
	size_t oldSize = READ_SIZE(getHeader(oldPtr));

	//check edge cases
	//check if the oldPtr is null, if so just allocate size from scratch
	if(oldPtr == NULL){
		newPtr = mm_malloc(size);
		return newPtr;
	}

	//if the new size is 0, then free the old allocated space and return;
	if(size == 0){
		mm_free(oldPtr);
		return NULL;
	}


	//ajust the size for alignment
	alignedSize = ALIGN(size);

	//CASE ZERO, the new allocation size = old size, so just return oldPtr and WRITE over it
	if(oldSize - DSIZE == alignedSize){
		newPtr = oldPtr;
		return newPtr; //just WRITE over it since the size requirement is identical
	}


	/* Three Cases Below for Realloc */


	/* CASE ONE
	 * When newSize < Oldsize, so overWRITE and free the blocks after it
	 */

	if(alignedSize < oldSize){
		//check the remaining size
		if(oldSize - alignedSize < DSIZE << 2){
			//too small to even be the smallest size block so just return the oldPtr
      //mm_check();

			return oldPtr;
		}

		//now allocate the smaller space for new size
		WRITE(getHeader(oldPtr), blockInfo(alignedSize + DSIZE, 1));
		WRITE(getFooter(oldPtr), blockInfo(alignedSize + DSIZE, 1));

		//swap the pointers so the newPtr can use this array
		newPtr = oldPtr;
		oldPtr = next_block(newPtr);
		//clear the space of behind the payload
		WRITE(getHeader(oldPtr), blockInfo(oldSize - DSIZE - alignedSize, 0));
		WRITE(getFooter(oldPtr), blockInfo(oldSize - DSIZE - alignedSize, 0));
		insertFreeBlock(oldPtr, READ_SIZE(getHeader(oldPtr)));
		coalesce(oldPtr);

    //mm_check();
		return newPtr;
	}

  /* Case 2: when newSize > oldSize, we have two scenarios: we must find a new block
  or takes space of the next block */
  nextPtr = next_block(oldPtr);
  if(nextPtr != NULL && !READ_ALLOC(getHeader(nextPtr))){
    nextSize = READ_SIZE(getHeader(nextPtr));
    if(nextSize + oldSize - DSIZE >= alignedSize){
      removeFreeBlock(nextPtr);
    }
    if(nextSize + oldSize - DSIZE - alignedSize <= DSIZE) {
      WRITE(getHeader(oldPtr), blockInfo(alignedSize + DSIZE, 1));
      WRITE(getFooter(oldPtr), blockInfo(alignedSize + DSIZE, 1));
      newPtr = oldPtr;
      oldPtr = next_block(newPtr);
      WRITE(getHeader(oldPtr), WRITE(oldSize + nextSize, 1));
      WRITE(getFooter(oldPtr), WRITE(oldSize + nextSize, 1));

      //mm_check();
      return oldPtr;
    }
    else {
      WRITE(getHeader(oldPtr), WRITE(alignedSize + DSIZE, 1));
      WRITE(getFooter(oldPtr), WRITE(alignedSize + DSIZE, 1));
      newPtr = oldPtr;
      oldPtr = next_block(newPtr);
      WRITE(getHeader(oldPtr), blockInfo(oldSize - DSIZE - alignedSize - alignedSize + nextSize, 0));
      WRITE(getFooter(oldPtr), blockInfo(oldSize - DSIZE - alignedSize - alignedSize + nextSize, 0));
      insertFreeBlock(oldPtr, READ_SIZE(getHeader(oldPtr)));
      coalesce(oldPtr);



      //mm_check();
      return newPtr;
    }
  }

  /* Case 3: We exahusted cases one and two so the only remaning option is to allocated
  a completely new bock to fit the requested size */
  newPtr = mm_malloc(size);
  if(newPtr == NULL){ return NULL; }
  memcpy(newPtr, oldPtr, oldSize - DSIZE - alignedSize);
  mm_free(oldPtr);


  //mm_check();
  return newPtr;
}
