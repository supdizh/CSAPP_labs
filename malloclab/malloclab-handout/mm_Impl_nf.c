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
/* p = handling pointers to ft/hdr*/
#define PACK(size, alloc)   ((size)|(alloc))
#define GET(p)              (*(size_t*)(p))
#define GET_SIZE(p)         (GET(p) & ~0x7)  /*0x7 = 0111  ~0x7 = x000 mutiples of 8*/
#define GET_ALLOC(p)        (GET(p) & 0x1)

/*GET ALLOC from previous using bit in this block*/
#define GET_PREV_ALLOC(p)   (GET(p) & 0x2)

/*PUT without changing the prev_alloc bit
#define PUT(p,val)          (GET(p) = GET_PREV_ALLOC(p)|val)
*/
#define PUT(p,val)         (GET(p) = (val))


/*macros with bp = handling pointers to pay load*/
#define HDRP(bp)            ((char*)(bp) - WSIZE)
#define FTRP(bp)            ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp)       ((char*)(bp) + GET_SIZE(HDRP(bp)))

/*PREV_BLKP works with footer*/
#define PREV_BLKP(bp)       ((char*)(bp) - GET_SIZE((char*)(bp) - DSIZE))

/*SET UNSET the prev_alloc in next block*/
#define SET_PALLOC(bp)      (GET(HDRP(NEXT_BLKP(bp))) = GET(HDRP(NEXT_BLKP(bp))) | 0x2)
#define UNSET_PALLOC(bp)    (GET(HDRP(NEXT_BLKP(bp))) = GET(HDRP(NEXT_BLKP(bp))) & ~0x2)


static char *heap_listp;
static char *rover;

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void Exam_list(int asize);
/*GET ALLOC from previous using bit in this block*/
//#define DEBUG

#ifdef DEBUG

static int mCnt = 0;
static int exCnt = 0;
#endif

static void *extend_heap(size_t words){
#ifdef DEBUG
    printf("call a extend[%d] for %dbyte\n",++exCnt,words*WSIZE);
#endif
    char *bp;
    size_t size;

    size = (words%2)?(words+1)*WSIZE : words*WSIZE;
    if((int)(bp = mem_sbrk(size)) == -1)
        return NULL;
#ifdef DEBUG
    printf("tot heapsize = %d\n",(char*)bp-heap_listp+size+DSIZE);
#endif
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
    }else if(!prev_alloc && next_alloc){
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }else{
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    if((rover > (char*)bp) && (rover < NEXT_BLKP(bp)))
        rover = bp;

    return bp;
}

static void *find_fit(size_t asize){
    char *oldrover = rover;

    for(; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover)){
        if( !GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))){
            //printf("hit\n");
            return rover;
        }
    }
    for(rover = heap_listp; rover != oldrover; rover = NEXT_BLKP(rover)){
        if( !GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))){
            //printf("hit\n");
            return rover;
        }
    }    
    return NULL;
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

    rover = heap_listp;

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
#ifdef DEBUG
    printf("[%d] malloc called with %d\n",++mCnt,size);
#endif

    if(size <= 0)
        return NULL;
    if(size <= WSIZE)
        printf("<WISZE\n");

    if(size <= DSIZE)
        asize = DSIZE + OVERHEAD;
    else
        asize = ALIGN(size + OVERHEAD);

    if((bp = find_fit(asize)) != NULL){
#ifdef DEBUG
        printf("find a slot at %d \n",bp-heap_listp);
#endif
        place(bp,asize);
        return bp;
    }
    //Exam_list(asize);
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
#ifdef DEBUG
    printf("free called upon %x\n",(char*)ptr-heap_listp);
#endif
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



static void Exam_list(int asize){
    void *bp;
    int csize;
    if(!asize){
        printf("\n-------mem list----------\n");
        for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
            printf("block %x:%x of realsize:%d %d \n",bp,bp+GET_SIZE(HDRP(bp)),GET_SIZE(HDRP(bp)),GET_ALLOC(HDRP(bp)));
        }
    }else{
        printf("\n------mem size[%d]----------\n",asize);
        for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
            csize = GET_SIZE(HDRP(bp));
            if(!GET_ALLOC(HDRP(bp))){
                if(csize<asize)printf("%d \t",csize);
                else printf("\033[42;30m%d\033[0m \t",csize);
            }
        }
    }
}











