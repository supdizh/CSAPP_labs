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



#define BIN_LEVEL 12

#define C32K    (1<<15)
#define C16K    (1<<14)
#define C8K     (1<<13)
#define C4K     (1<<12)
#define C2K     (1<<11)
#define C1K     (1<<10)
#define C512    (1<<9)
#define C256    (1<<8)
#define C128    (1<<7)
#define C64     (1<<6)
#define C32     (1<<5)
#define DSIZE   8
#define WSIZE   4

#define verbose 1
#define silent 0
 
//#define DEBUG
//#define Cnt_Prof

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

static char *heap_listp = 0;
static char *heap_epiheader = 0;
static char *blist_tbl = 0;


static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void init_blist_table();
static inline void insert_blist(size_t lvl,char* bp);
static inline void remove_blist(size_t lvl,char* bp);
static inline void SET_PREV_FL(char *bp,char* val);
static inline void SET_NEXT_FL(char *bp,char* val);
static inline int GET_LEVEL(int size);
static inline char** GET_BLIST_HEAD(size_t lvl);
static inline char** GET_BLIST_TAIL(size_t lvl);

/*debug tools*/
static void fPerror(const char* str,void* bp);
static void check_heap();
static void dump_heap(int req);
static void dump_blist();
static void check_payload(char *a, char *b);
static void fPerror2(const char* str,void* bp);
static int check_blist(int req);
static int check_inblist_heap(char* bp);
static char* validate_inheap_blist(char* bp);


/*segregated list manipulation*/
static inline void SET_PREV_FL(char *bp,char* val){
    APUT(bp,(size_t)val);
}
static inline void SET_NEXT_FL(char *bp,char* val){
    APUT(bp+WSIZE,(size_t)val);
}
static inline int GET_LEVEL(int size){
    if(size<=C32)return 0;
    else if(size<=C64)return 1;
    else if(size<=C128)return 2;
    else if(size<=C256)return 3;
    else if(size<=C512)return 4;
    else if(size<=C1K)return 5;
    else if(size<=C2K)return 6;
    else if(size<=C4K)return 7;
    else if(size<=C8K)return 8;
    else if(size<=C16K)return 9;
    else if(size<=C32K)return 10;
    else return 11;
}

/*get pointer to the adress in the heap recording the adress of a lvl
 or a pointer to pointer
*/
static inline char** GET_BLIST_HEAD(size_t lvl){
    char *bp = blist_tbl + lvl*DSIZE;
    return (char**)(bp);
}

static inline char** GET_BLIST_TAIL(size_t lvl){
    char *bp = blist_tbl + lvl*DSIZE + WSIZE;
    return (char**)(bp);
}

static void init_blist_table(){
    memset(blist_tbl, 0, BIN_LEVEL * DSIZE);
}

static inline void insert_blist(size_t lvl, char* bp){
    /*adress order insert*/
#ifdef DEBUG
    //printf("inserting %p #$%d\n",bp,GET_SIZE(HDRP(bp)));
    //dump_blist();
#endif
    char **blist_head = GET_BLIST_HEAD(lvl);
    char **blist_tail = GET_BLIST_TAIL(lvl);
    if(!(*blist_head)){
        /*empty level list*/
        *blist_head = bp;
        *blist_tail = bp;
        SET_PREV_FL(bp,0);
        SET_NEXT_FL(bp,0);
    }else{
        int size = GET_SIZE(HDRP(bp));
        if(size <= GET_SIZE(HDRP(*blist_head))) {
            /*insert at head*/
            SET_PREV_FL(*blist_head,bp);
            SET_NEXT_FL(bp,*blist_head);
            SET_PREV_FL(bp,0);
            *blist_head = bp;
        }
        else if(GET_SIZE(HDRP(*blist_tail)) <= size ){
            /*insert in tail*/
            SET_NEXT_FL(*blist_tail,bp);
            SET_PREV_FL(bp,*blist_tail);
            SET_NEXT_FL(bp,0);
            *blist_tail = bp;
        }
        else{
            /*insert in mid*/
            char *it = *blist_head;
            while(GET_SIZE(HDRP(it)) < size) it = GET_NEXT_FL(it);
            SET_NEXT_FL(GET_PREV_FL(it),bp);
            SET_PREV_FL(bp,GET_PREV_FL(it));
            SET_PREV_FL(it,bp);
            SET_NEXT_FL(bp,it);
        }
    }
}

static inline void remove_blist(size_t lvl, char* bp){
    char **blist_head = GET_BLIST_HEAD(lvl);
    char **blist_tail = GET_BLIST_TAIL(lvl);
    if(bp == *blist_head){
        /*remove the head*/
        *blist_head = GET_NEXT_FL(bp);
        if(*blist_head){/*if not NULL,set prev*/
            SET_PREV_FL(*blist_head,0);
        }else{ /*if NULL,set tail*/
            *blist_tail = 0;
        }
    }else if(bp == *blist_tail){
        *blist_tail = GET_PREV_FL(bp);
        if(*blist_tail){
            SET_NEXT_FL(*blist_tail,0);
        }else{
            *blist_head = 0;/*unlikely to happen*/
        }
    }else{
        SET_NEXT_FL(GET_PREV_FL(bp),GET_NEXT_FL(bp));
        SET_PREV_FL(GET_NEXT_FL(bp),GET_PREV_FL(bp));
    }
}



static void *extend_heap(size_t words){
#ifdef DEBUG
    printf("call a extend[%d] for %dbyte\n",++exCnt,words*WSIZE);
    //dump_heap(0);
#endif
    char *bp;
    size_t size;

    size = (words%2)?(words+1)*WSIZE : words*WSIZE;
    if((int)(bp = mem_sbrk(size)) == -1)
        return NULL;
#ifdef DEBUG
    //printf("tot heapsize = %d\n",(char*)bp-heap_listp+size+DSIZE);
#endif
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));  
    SET_PREV_FL(bp,0);
    SET_NEXT_FL(bp,0);
    heap_epiheader = HDRP(NEXT_BLKP(bp));
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

    /*only works on newly "free" block that is not in freelist
    caused seg fault when not*/
    if(GET_ALLOC(HDRP(bp))){
        fPerror("coalescing allocated block",bp);
    }
    if(prev_alloc && next_alloc){
        /**/
    }
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(next_blk));
        remove_blist(GET_LEVEL(GET_SIZE(HDRP(next_blk))),next_blk);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){
        pre_blk = PREV_BLKP(bp);   
        size += GET_SIZE(FTRP(pre_blk));
        remove_blist(GET_LEVEL(GET_SIZE(HDRP(pre_blk))),pre_blk);
        PUT(HDRP(pre_blk), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = pre_blk;
    }
    else{
        pre_blk = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(next_blk)) + GET_SIZE(FTRP(pre_blk));
        remove_blist(GET_LEVEL(GET_SIZE(HDRP(next_blk))),next_blk);
        remove_blist(GET_LEVEL(GET_SIZE(HDRP(pre_blk))),pre_blk);
        PUT(HDRP(pre_blk), PACK(size, 0));
        PUT(FTRP(next_blk), PACK(size, 0));
        bp = pre_blk;
    }
    insert_blist(GET_LEVEL(size),bp);
    return bp;
}

static void *find_fit(size_t asize){
    /*first fit and adress ordered list*/
    char *bp = NULL;
    char *blist_head;

    int lvl = GET_LEVEL(asize);

    while(lvl < BIN_LEVEL){
        blist_head = *(GET_BLIST_HEAD(lvl));
        for( bp = blist_head;bp; bp = GET_NEXT_FL(bp)){
            if(asize <= GET_SIZE(HDRP(bp))){
                return bp;
            }
        }
        lvl++;
    }
    return NULL;
}

/*
 * place - place the size into this chunck, split if necessary, and maintain the free list
    let's assume place all called upon freed space
 */

static void place(void *bp, size_t asize){
#ifdef DEBUG
    printf("place %p with %d\n",bp,asize);
    //dump_heap(0);
#endif
    size_t csize = GET_SIZE(HDRP(bp));
    void *next_blk;
    if((csize-asize) >= 2*DSIZE){ /*then split needed*/
        remove_blist(GET_LEVEL(csize),bp);
        PUT(HDRP(bp), PACK(asize, 1));
        next_blk = NEXT_BLKP(bp);
        APUT(HDRP(next_blk), PACK(csize-asize,2));
        APUT(FTRP(next_blk), PACK(csize-asize,0));
        insert_blist(GET_LEVEL(csize-asize),next_blk);
    }else{
        remove_blist(GET_LEVEL(csize),bp);
        PUT(HDRP(bp), PACK(csize, 1));
        SET_PALLOC(bp);
    }
#ifdef DEBUG
    printf("aflter place %p with %d\n",bp,asize);
    //dump_heap(0);
#endif  
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE + BIN_LEVEL*DSIZE)) == NULL)
        return -1;
    blist_tbl = heap_listp;
    init_blist_table();
    heap_listp += BIN_LEVEL*DSIZE;
    APUT(heap_listp, 0);
    APUT(heap_listp+WSIZE, PACK(DSIZE,1)); /*prologue heading*/
    APUT(heap_listp+2*WSIZE, PACK(DSIZE,1));
    APUT(heap_listp+3*WSIZE, PACK(0,3));
    heap_listp += 2*WSIZE;
    heap_epiheader = heap_listp + 3*WSIZE;

    if(NULL == extend_heap(C4K/WSIZE)){
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
    size_t asize;/*asize = overrall size with overhead + alignment*/
    size_t extendsize;
    char *bp;

#ifdef DEBUG
    printf("[%d] malloc called with %d\n",++mCnt,size);
    //dump_heap(0);
    //dump_blist();
    //check_blist(1);
    //check_heap();
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
#ifdef DEBUG
    printf("didn't find any for [%d],we have[%d]\n",asize,check_blist(1));
    dump_heap(0);
#endif
    extendsize = MAX(asize,C4K);
    if(!GET_PREV_ALLOC(heap_epiheader)){
        extendsize = MAX(extendsize-GET_SIZE(heap_epiheader-WSIZE),16);
    }
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
    //printf("free called upon %p \n",ptr);
    //dump_heap(0);
#endif
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size,0));
    APUT(FTRP(ptr), PACK(size,0));
    UNSET_PALLOC(ptr);
    coalesce(ptr);
#ifdef DEBUG
    //printf("after free %p \n",ptr);
    //dump_heap(0);
    //check_heap();
#endif
}


void *mm_realloc(void *bp, size_t size)
{
#ifdef DEBUG
    printf("realloc %p with size=%d\n",bp,size);
    //dump_heap(0);
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
                remove_blist(GET_LEVEL(GET_SIZE(HDRP(newbp))),newbp);
                PUT(HDRP(bp),PACK(asize,1));
                newbp = NEXT_BLKP(bp);/*the newly splited block*/
                APUT(HDRP(newbp), PACK(nsize-asize,2));
                APUT(FTRP(newbp), PACK(nsize-asize,0));
                insert_blist(GET_LEVEL(nsize-asize),newbp);
            }else{
                remove_blist(GET_LEVEL(GET_SIZE(HDRP(newbp))),newbp);
                PUT(HDRP(bp),PACK(nsize,1));
                SET_PALLOC(bp);
            }
            return bp;
        }
        /* malloc at the tail of heap ,extend necessary amount of mem as needed*/
        if(heap_epiheader < NEXT_BLKP(bp)){
#ifdef DEBUG
            printf("REALLOC: extend at tail: [now,epi]\n");
#endif
            nsize = MAX((asize-oldsize),16);
            newbp = extend_heap(nsize/WSIZE);
            remove_blist(GET_LEVEL(nsize),newbp);
            PUT(HDRP(bp),PACK(oldsize+nsize,1));
            SET_PALLOC(bp);     
            return bp;
        }
        if(!next_alloc && heap_epiheader < NEXT_BLKP(NEXT_BLKP(bp))){
#ifdef DEBUG
            printf("REALLOC: extend at tail: [now,free,epi]\n");
#endif      
            int extra = MAX((asize-nsize),16);      
            newbp = extend_heap(extra/WSIZE);
            remove_blist(GET_LEVEL(extra),newbp);
            PUT(HDRP(bp),PACK(nsize+extra,1));
            SET_PALLOC(bp);
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

/*DEBUG FUNCTION IMPLEMENT*/

static void dump_heap(int asize){
    void *bp;
    int csize;
    if(!asize){
        printf("\n-------mem list----------\n");
        printf("bp = %p,HDRP =%p,size = %d\n",heap_listp,HDRP(heap_listp),GET_SIZE(HDRP(heap_listp)));
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
    for(; GET_SIZE(HDRP(hrover)) > 0; hrover = NEXT_BLKP(hrover)){
        if(hrover==bp){
            return bp;
        }
    }
    return 0;
}


static int check_inblist_heap(char* bp){
    int lvl = 0;
    char *fblk;

    while(lvl < BIN_LEVEL){
        for(fblk = (*GET_BLIST_HEAD(lvl));fblk;fblk = GET_NEXT_FL(fblk)){
            if(fblk == bp)return 1;
        }
        lvl++;
    }
    return 0;
}

static void dump_blist(){
    printf("dump_blist------------\n");
    int lvl = 0;
    char *fblk;
    while(lvl < BIN_LEVEL){
        for(fblk = (*GET_BLIST_HEAD(lvl));fblk;fblk = GET_NEXT_FL(fblk)){
            printf("block %p:%p of realsize:%d alloc:%d prev_alloc:%d at lvl:%d\n",fblk,fblk+GET_SIZE(HDRP(fblk)),GET_SIZE(HDRP(fblk)),
                                                                                GET_ALLOC(HDRP(fblk)),GET_PREV_ALLOC(HDRP(fblk)),lvl);
        }
        lvl++;
    }
}

/*return the biggest one*/
static int check_blist(int req){
    int lvl = 0,size = 0;
    char *fblk;
    while(lvl < BIN_LEVEL){
        for(fblk = (*GET_BLIST_HEAD(lvl));fblk!=0;fblk = GET_NEXT_FL(fblk)){
            //printf("for block %p at lvl %d\n",fblk,lvl);
            if(validate_inheap_blist(fblk)){
                if(!GET_ALLOC(fblk) && req){
                    printf("%p[%p:%p]#%d at lvl:%d\n",fblk,GET_PREV_FL(fblk),GET_NEXT_FL(fblk),GET_SIZE(HDRP(fblk)),lvl);
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
        }
        lvl++;
    }
    if(req)printf("\n");
    return size;
}









