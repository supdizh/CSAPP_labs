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

#define verbose 1
#define silent 0
 
//#define DEBUG
#define Cnt_Prof

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

/*GET/SET PREV/NEXT BLK adress IN THE Freelist*/
#define GET_PREV_FL(bp)     ((char*)(GET(bp)))
#define GET_NEXT_FL(bp)     ((char*)(GET((char*)(bp)+WSIZE)))



#ifdef DEBUG
static int mCnt = 0;
static int exCnt = 0;
#endif

#ifdef Cnt_Prof
static int blkCnt = 0;
#endif


static char *heap_listp;
static char *blist_top;

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void fPerror(const char* str,void* bp);
static void check_heap();
static void dump_heap(int req);
static void dump_blist();
static void check_payload(char *a, char *b);
static void fPerror2(const char* str,void* bp);
static void check_blist(int req);
static int check_inblist_heap(char* bp);

/*#define SET_PREV_FL(bp,val) PUT(bp,val)*/
static inline void SET_PREV_FL(char *bp,char* val){
    if(bp)APUT(bp,(size_t)val);
}
/*#define SET_NEXT_FL(bp,val) PUT((char*)bp+WSIZE,val)*/
static inline void SET_NEXT_FL(char *bp,char* val){
    if(bp)APUT(bp+WSIZE,(size_t)val);
    else
        blist_top = val;
}

/*on lists operation*/
static inline void insert_blist(char* bp){
#ifdef DEBUG
    printf("inserting %p #$%d\n",bp,GET_SIZE(HDRP(bp)));
    dump_blist();
#endif
#ifdef Cnt_Prof
    blkCnt++;
#endif

    if(!blist_top){
        blist_top = bp;
        SET_PREV_FL(bp,0);
        SET_NEXT_FL(bp,0);
        return;

    }else{
        int size = GET_SIZE(HDRP(bp));
        if(size <= GET_SIZE(HDRP(blist_top))){ /*at head*/
            SET_NEXT_FL(bp,blist_top);
            SET_PREV_FL(bp,0);
            SET_PREV_FL(blist_top,bp);
            blist_top = bp;
            return;
        }
        char* next = GET_NEXT_FL(blist_top);
        char* prev = blist_top;
        while(next){
            if(size <= GET_SIZE(HDRP(next))){
                SET_NEXT_FL(bp,next);
                SET_PREV_FL(bp,prev);
                SET_NEXT_FL(prev,bp);
                SET_PREV_FL(next,bp);
                return;
            }
            prev = next;
            next = GET_NEXT_FL(next);
        }
        /*at tail*/
        SET_NEXT_FL(prev,bp);
        SET_PREV_FL(bp,prev);
        SET_NEXT_FL(bp,0);
        return;
    }
}

static inline void remove_blist(char* bp){
#ifdef Cnt_Prof
    blkCnt--;
#endif
    SET_NEXT_FL(GET_PREV_FL(bp),GET_NEXT_FL(bp));
    SET_PREV_FL(GET_NEXT_FL(bp),GET_PREV_FL(bp));
}

static inline void shift_head_blist(char* from,char* to){
    SET_PREV_FL(to,GET_PREV_FL(from));
    SET_NEXT_FL(to,GET_NEXT_FL(from));       
    SET_PREV_FL(GET_NEXT_FL(to),to);
    SET_NEXT_FL(GET_PREV_FL(to),to);
}



static void *extend_heap(size_t words){
#ifdef DEBUG
    printf("call a extend[%d] for %dbyte\n",++exCnt,words*WSIZE);
    dump_heap(0);
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

/*  coalesce
 *  1 coalesce the previous block-curent block-next block
    2 insert new node into the freelist
    so it should be called "coalesce in heap and insert in list"
    Caution 1: when we coalesce on *bp , *bp is not in the free list

    IF handled corrected, each free will call this method, and no two consecutive freed block would exsist.
 */
static void *coalesce(void *bp){
    void *next_blk = NEXT_BLKP(bp),*pre_blk;
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(next_blk));
    size_t size = GET_SIZE(HDRP(bp));

    /*only works on newly "free" block that is not in freelist*/
    if(GET_ALLOC(HDRP(bp)))
        return bp;

    if(prev_alloc && next_alloc){
        insert_blist(bp);
        return bp;
    }

    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(next_blk));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        shift_head_blist(next_blk,bp);
        remove_blist(next_blk);
        insert_blist(bp);
    }else if(!prev_alloc && next_alloc){
        pre_blk = PREV_BLKP(bp);   
        size += GET_SIZE(FTRP(pre_blk));
        PUT(HDRP(pre_blk), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = pre_blk;
        remove_blist(bp);
        insert_blist(bp);
    }else{
        pre_blk = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(next_blk)) + GET_SIZE(FTRP(pre_blk));
        remove_blist(pre_blk);
        remove_blist(next_blk);
        PUT(HDRP(pre_blk), PACK(size, 0));
        PUT(FTRP(next_blk), PACK(size, 0));
        bp = pre_blk;
        insert_blist(pre_blk);
    }
    
    return bp;
}

static void *find_fit(size_t asize){
    char *fblk = blist_top;
#ifdef Cnt_Prof
    int iCnt = 0;
#endif
    while(fblk){
#ifdef Cnt_Prof
        iCnt++;
#endif
        if(asize <= GET_SIZE(HDRP(fblk)))break;
        else fblk = GET_NEXT_FL(fblk);
    }
#ifdef Cnt_Prof
    printf("%d/%d, %f\n",iCnt,blkCnt,((float)iCnt)/blkCnt);
#endif
    return fblk;
}

/*
 * place - place the size into this chunck, split if necessary, and maintain the free list
 */

static void place(void *bp, size_t asize){
#ifdef DEBUG
    printf("place %p with %d\n",bp,asize);
    dump_heap(0);
#endif
    size_t csize = GET_SIZE(HDRP(bp));
    void *next_blk;
    if((csize-asize) >= DSIZE+OVERHEAD){ /*then split needed*/
        PUT(HDRP(bp), PACK(asize, 1));
        /*optimizing  combine SET_PALLOC + PUT*/
        next_blk = NEXT_BLKP(bp);
        APUT(HDRP(next_blk), PACK(csize-asize,2));
        APUT(FTRP(next_blk), PACK(csize-asize,0));
        UNSET_PALLOC(next_blk);
        remove_blist(bp);
        insert_blist(next_blk);
        /*the block called into place is not necessarily free*/
    }else{
        PUT(HDRP(bp), PACK(csize, 1));
        SET_PALLOC(bp);
        remove_blist(bp);
    }
#ifdef DEBUG
    printf("aflter place %p with %d\n",bp,asize);
    dump_heap(0);
#endif  
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

    blist_top = 0;
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
    dump_heap(0);
    dump_blist();
    check_blist(1);
    check_heap();
#endif

    if(size <= 0)
        return NULL;

    if(size <= 3*WSIZE)
        asize = 2*DSIZE;
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
    dump_heap(0);
#endif
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size,0));
    APUT(FTRP(ptr), PACK(size,0));
    UNSET_PALLOC(ptr);
    coalesce(ptr);
#ifdef DEBUG
    printf("after free %p \n",ptr);
    dump_heap(0);
    check_heap();
#endif
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
    /*size policy*/
    if(size <= 3*WSIZE)
        asize = 2*DSIZE;
    else
        asize = ALIGN(size + WSIZE);

    if(oldsize >= asize){
#ifdef DEBUG
        printf("REALLOC: oldsize >= asize\n");
#endif
        if((oldsize-asize) >= 2*DSIZE){
            PUT(HDRP(bp),PACK(asize,1));
            newbp = NEXT_BLKP(bp);
            APUT(HDRP(newbp), PACK(oldsize-asize,3));
            APUT(FTRP(newbp), PACK(oldsize-asize,1));
            mm_free(newbp);
        }
        return bp;
    }else{
        nsize = oldsize + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        //printf("old+next=%d,aisze=%d\n",nsize,asize);
        /* next+current suffice*/
        if(!next_alloc && (nsize-asize) >= 2*DSIZE ){
#ifdef DEBUG
            printf("REALLOC: oldsize+next >= asize\n");
#endif
            newbp = NEXT_BLKP(bp);
            if((nsize-asize) >= 2*DSIZE){
                PUT(HDRP(bp),PACK(asize,1));
                remove_blist(newbp);
                newbp = NEXT_BLKP(bp);
                APUT(HDRP(newbp), PACK(nsize-asize,2));
                APUT(FTRP(newbp), PACK(nsize-asize,0));
                insert_blist(newbp);
            }else{
                PUT(HDRP(bp),PACK(nsize,1));
                remove_blist(newbp);
                SET_PALLOC(bp);
            }
            return bp;
        }
    }

#ifdef DEBUG
    printf("REALLOC: new malloc\n");
#endif
    newbp = mm_malloc(size);
    if(size < oldsize)
        oldsize = size;
    memcpy(newbp, bp, oldsize);
    mm_free(bp);
    return newbp;
}


void *mm_realloc2(void *ptr, size_t size)
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
    check_blist(1);
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
            }else if(!check_inblist_heap(bp)){
                fPerror("free blk not in list",bp);
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


/*
    check the explicit free block list for
    1 is every blk in free list mrked free
    2 is pointers in them point to free blk
    3 is every free blk in free list

*/

static char* validate_inheap_blist(char* bp){
    char *hrover = heap_listp;
    for(; GET_SIZE(HDRP(hrover)) > 0; hrover = NEXT_BLKP(hrover))if(hrover==bp){
        return bp;
    }
    return 0;
}

static int check_inblist_heap(char* bp){
    char *fblk = blist_top;
    while(fblk){
        if(fblk == bp) return 1;
        else fblk = GET_NEXT_FL(fblk);
    }
    return 0;
}

static void dump_blist(){
    printf("dump_blist------------\n");
    printf("blist_top = %p\n",blist_top);
    char *bp = blist_top;
    while(bp){
        printf("block %p:%p of realsize:%d alloc:%d prev_alloc:%d\n",bp,bp+GET_SIZE(HDRP(bp)),GET_SIZE(HDRP(bp)),
                                                                                GET_ALLOC(HDRP(bp)),GET_PREV_ALLOC(HDRP(bp)));
        bp = GET_NEXT_FL(bp);
    }  
}


static void check_blist(int req){
    if(req)printf("blist_top = %p\n",blist_top);
    char *fblk = blist_top;
    int size = 0;
    while(fblk){
        if(validate_inheap_blist(fblk)){
            if(!GET_ALLOC(fblk) && req){
                printf("%p[%p:%p]#%d\t",fblk,GET_PREV_FL(fblk),GET_NEXT_FL(fblk),GET_SIZE(HDRP(fblk)));
            }else if(GET_ALLOC(fblk)){
                fPerror2("allocated blk in free list",fblk);
            }
        }else{
            fPerror2("error heap location",fblk);
        }
        if(GET_SIZE(HDRP(fblk)) < size){
            fPerror2("block size not ascending",fblk);
            dump_blist();
            exit(-1);
        }
        size = GET_SIZE(HDRP(fblk));
        fblk = GET_NEXT_FL(fblk);
    }
    if(req)printf("\n");
}









