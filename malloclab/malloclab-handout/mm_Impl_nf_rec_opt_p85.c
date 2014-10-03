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
#define C16K (1<<14)
#define C4K (1<<12)
#define C64 (1<<6)
#define OVERHEAD 8

//#define DEBUG

#define MAX(x,y) ((x)>(y)? (x):(y))
#define MIN(x,y) ((x)<(y)? (x):(y))

/* Macros for implcit list with hdr/ft */
/* p = handling pointers to ft/hdr*/
#define PACK(size, alloc)   ((size)|(alloc))
#define GET(p)              (*(size_t*)(p))
#define GET_SIZE(p)         (GET(p) & ~0x7)  /*0x7 = 0111  ~0x7 = x000 mutiples of 8*/
#define GET_ALLOC(p)        (GET(p) & 0x1)

/*GET ALLOC from previous using bit in this block*/
#define GET_PREV_ALLOC(p)   (GET(p) & 0x2)

/*PUT without changing the prev_alloc bit*/
#define PUT(p,val)          (GET(p) = GET_PREV_ALLOC(p)|val)
#define APUT(p,val)         (GET(p) = (val))


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
static void fPerror(const char* str,void* bp);
static void check_heap();
static void dump_heap(int req);
static void check_payload(char *a, char *b);
static void fPerror2(const char* str,void* bp);

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
    APUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));/*next block does not exsist, but the header of it does, the epiloge*/
    return coalesce(bp);
}

/*
 * coalesce the previous block-curent block-next block
    IF handled corrected, each free will call this method, and no two consecutive freed block would exsist.
 */
static void *coalesce(void *bp){

    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(GET_ALLOC(HDRP(bp)))
        return bp;
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
            return rover;
        }
    }
    for(rover = heap_listp; rover != oldrover; rover = NEXT_BLKP(rover)){
        if( !GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))){
            return rover;
        }
    }    
    return NULL;
}

/*
 * place - place the size into this chunck, split if necessary
 */

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    if((csize-asize) >= DSIZE+OVERHEAD){ /*then split needed*/
        PUT(HDRP(bp), PACK(asize, 1));
        /*optimizing  combine SET_PALLOC + PUT*/
        bp = NEXT_BLKP(bp);
        APUT(HDRP(bp), PACK(csize-asize,2));
        APUT(FTRP(bp), PACK(csize-asize,0));
        UNSET_PALLOC(bp);
        /*the block called into place is not necessarily free*/
    }else{
        PUT(HDRP(bp), PACK(csize, 1));
        SET_PALLOC(bp);
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
    PUT(heap_listp+2*WSIZE, PACK(OVERHEAD,1));
    PUT(heap_listp+3*WSIZE, PACK(0,1));
    heap_listp += 2*WSIZE;
    SET_PALLOC(heap_listp);

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
        asize = DSIZE; /*less of equal to 4bytes,need 8byte*/
    else
        asize = ALIGN(size + WSIZE);


    if((bp = find_fit(asize)) != NULL){
#ifdef DEBUG
        printf("find a slot at %p \n",bp);
#endif
        place(bp,asize);
        return bp;
    }
    extendsize = MAX(asize,C4K);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}



/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
#ifdef DEBUG
    printf("free called upon %p \n",ptr);
#endif
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size,0));
    APUT(FTRP(ptr), PACK(size,0));
    UNSET_PALLOC(ptr);
    coalesce(ptr);
}


void *mm_realloc(void *bp, size_t size)
{
#ifdef DEBUG
    printf("realloc %p with size=%d\n",bp,size);
    dump_heap(0);
#endif
    char *newbp;
    int oldsize,next_alloc;
    int asize,nsize;
    /*size = 0, free the oldptr*/
    if(size == 0){
        mm_free(bp);
        return NULL;
    }
    /*bp = NULL, malloc a new block*/
    if(bp == NULL)
        return mm_malloc(size);

    oldsize = GET_SIZE(HDRP(bp));
    next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    if(size <= WSIZE)
        asize = DSIZE; /*less of equal to 4bytes,need 8byte*/
    else
        asize = ALIGN(size + WSIZE);

    if(oldsize >= asize){
        place(bp,asize);
#ifdef DEBUG
        printf("REALLOC: oldsize >= asize\n");
#endif

        return bp;
    }else{
        nsize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        //printf("old+next=%d,aisze=%d\n",nsize,asize);
        /* next+current suffice*/
        if(!next_alloc && nsize >= asize ){
            if(rover == NEXT_BLKP(bp)) rover = bp;
            PUT(HDRP(bp),nsize);
            place(bp,asize);
#ifdef DEBUG
            printf("REALLOC: oldsize+next >= asize\n");
#endif
            return bp;
        }
    }
#ifdef DEBUG
        printf("REALLOC: freed and malloc\n");
#endif
    if(!GET_PREV_ALLOC(HDRP(bp))){
        rover = PREV_BLKP(bp);
        nsize = GET_SIZE(FTRP(PREV_BLKP(bp)));
        if(nsize >= asize){
            memmove(rover, bp,oldsize);
            place(rover,asize);
            mm_free(bp);
            return rover;
        }
        nsize += oldsize;
        if(nsize >= asize){
            PUT(HDRP(rover),nsize);
            memmove(rover, bp,oldsize);
            place(rover,asize);
            coalesce(NEXT_BLKP(rover));
            return rover;
        }
        nsize += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if(nsize >= asize && !GET_ALLOC(NEXT_BLKP(bp))){
            PUT(HDRP(rover),nsize);
            memmove(rover, bp,oldsize);
            place(rover,asize);
            return rover;
        }
    }
    newbp = mm_malloc(size);
    memmove(newbp, bp, oldsize);
    mm_free(bp);
    return newbp;
}

static void dump_heap(int asize){
    void *bp;
    int csize;
    if(!asize){
        printf("\n-------mem list----------\n");
        for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
            printf("block %p:%p of realsize:%d alloc:%d prev_alloc:%d\n",bp,bp+GET_SIZE(HDRP(bp)),GET_SIZE(HDRP(bp)),
                                                                                GET_ALLOC(HDRP(bp)),GET_PREV_ALLOC(HDRP(bp)));
        }
        printf("epilogue %p:%p of realsize:%d alloc:%d prev_alloc:%d\n",bp,bp+GET_SIZE(HDRP(bp)),GET_SIZE(HDRP(bp)),
                                                                                GET_ALLOC(HDRP(bp)),GET_PREV_ALLOC(HDRP(bp)));
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

/*
check the heap from heap_listp
1, all colasced
2, check prev_allocated
3, if free block, hdr size = ft size
*/
static void check_heap(){
    void *bp;
    int alloc,prev_alloc = 0,size;
    for(bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)){
        alloc = GET_ALLOC(HDRP(bp));
        size = GET_SIZE(HDRP(bp));
        if(prev_alloc != GET_PREV_ALLOC(HDRP(bp))){
            printf("%d %d\n",prev_alloc,GET_PREV_ALLOC(HDRP(bp)));
            fPerror("prev_alloc inconsistant",bp);
            dump_heap(0);
            exit(-1);
        }
        if(!alloc){
            if(size != GET_SIZE(FTRP(bp))){
                fPerror("footer size inconsistant",bp);
                dump_heap(0);
                exit(-1);
            }else if(!prev_alloc){
                fPerror("continual free block",bp);
                dump_heap(0);
                exit(-1);
            }
        }
        prev_alloc = alloc?2:0;
    }
    if(prev_alloc != GET_PREV_ALLOC(HDRP(bp))){
        fPerror("epilogue prev_alloc inconsis",bp);
        dump_heap(0);
        exit(-1);
    }
}

static void fPerror(const char* str,void* bp){
    printf("\033[41;30m%s @ %p\033[0m \n",str,bp);
}

static void fPerror2(const char* str,void* bp){
    printf("\033[42;30m%s @ %p\033[0m \n",str,bp);
}


static void check_payload(char *a, char *b){
    int sizea = GET_SIZE(HDRP(a));
    int sizeb = GET_SIZE(HDRP(b));
    printf("check_payload for [%p]:[%p] to [%p]:[%p]\n",a,FTRP(a),b,FTRP(b));
    if(sizea != sizeb){
        fPerror("check_payload fail size differ",0);
    }
    sizea -= WSIZE;
    while(sizea--){
        if(*a != *b){
            fPerror("check_payload fail data differ",a);
        }else{
            fPerror2("check_payload byte match",a);
        }
        a++;b++;
    }

}











