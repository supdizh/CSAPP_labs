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
    "heramalloc",
    /* First member's full name */
    "Di",
    /* First member's email address */
    "sjtuzxd@foxmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) //size of a int, 4 here

#define WSIZE 4
#define DSIZE 8
#define C4K (1<<12)
#define OVERHEAD 8

#define MAX(x,y) ((x)>(y)? (x):(y))


/* Macros for implcit list with hdr/ft */
#define PACK(size, alloc)   ((size)|(alloc))
#define GET(p)              (*(size_t*)(p))  /*get or put as a int*/
#define PUT(p,val)          (*(size_t*)(p) = (val))
#define GET_SIZE(p)         (GET(p) & ~0x7)  /*0x7 = 0111  ~0x7 = x000 mutiples of 8*/
#define GET_ALLOC(p)        (GET(p) & 0x1)

#define HDRP(bp)            ((char*)(bp) - WSIZE)
#define FTRP(bp)            ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp)       ((char*)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)       ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE))



static char *heap_listp;

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void Exam_list();


static void *extend_heap(size_t words){
    //printf("\ncall a extend for %dbyte\n",words*WSIZE);
    char *bp;
    size_t size;

    size = (words%2)?(words+1)*WSIZE : words*WSIZE;
    if((int)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));/*next block does not exsist, but the header of it does, the epiloge*/
    /*Initialize */
    //printf("bp from exh %x\n",bp);
    return coalesce(bp);
}

/*
 * place - place the size into this chunck, split if necessary
 */

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    if((csize-asize) >= (DSIZE + OVERHEAD)){ /*then split needed*/
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize,0));
        PUT(FTRP(bp), PACK(csize-asize,0));
    }else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    
}

/*
 * coalesce the previous block-curent block-next block
    IF handled corrected, each free will call this method, and no two consecutive freed block would exsist.
 */
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc)
        return bp;

    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        return bp;
    }else if(!prev_alloc && next_alloc){
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        return PREV_BLKP(bp);
    }else{
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        return PREV_BLKP(bp);
    }
}

static void *find_fit(size_t asize){
    void *bp,*rec = NULL;
    size_t bsize = 0;
    size_t nbsize;
    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        nbsize = GET_SIZE(HDRP(bp));
        if( !GET_ALLOC(HDRP(bp)) && (asize <= nbsize)){
            if(bsize == 0 || nbsize <= bsize ){
                bsize = nbsize;
                rec = bp;
            }
        }
    }
    return rec;
}

static void Exam_list(){
    void *bp;
    printf("\n-------mem list----------\n");
    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        printf("block %x:%x of realsize:%d %d \n",bp,bp+GET_SIZE(HDRP(bp)),GET_SIZE(HDRP(bp)),GET_ALLOC(HDRP(bp)));
    }   
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp+WSIZE, PACK(OVERHEAD,1));
    PUT(heap_listp+DSIZE, PACK(OVERHEAD,1));
    PUT(heap_listp+WSIZE+DSIZE, PACK(0,1));
    heap_listp += DSIZE;

    if(extend_heap(C4K/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    /*asize = overrall size with overhead + alignment*/
    size_t extendsize;
    char *bp;

    //printf("malloc called with %d\n",size);
    //Exam_list();

    if(size <= 0)
        return NULL;

    if(size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    else
        asize = ALIGN(size + OVERHEAD);

    if((bp = find_fit(asize)) != NULL){
        place(bp,asize);
        //printf("returning bp %x\n",bp);
        return bp;
    }
    extendsize = MAX(asize,C4K);

    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);

    //Exam_list();
    return bp;
}



/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    //printf("free called upon %x\n",ptr);
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr), PACK(size,0));
    coalesce(ptr);
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
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














