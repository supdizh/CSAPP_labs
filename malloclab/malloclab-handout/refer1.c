#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <time.h>

#include "mm.h"
#include "memlib.h"
//#include "memlib.c"
/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "HaHaHa",
    /* First member's full name */
    "he yiwei",
    /* First member's email address */
    "541915846@qq.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* size of address */
#define ASIZE (sizeof(void *))

/* smallest size of block */
#define MINBLOCK (DSIZE + 2 * ASIZE)

/* Word and header/footer size (bytes) */
#define WSIZE 4
#define DSIZE 8

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define MAX(x,y) ((x)>(y)?(x):(y))

/* Pack a size and allocated bit into a word */
#define PACK(size,alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *) (p))
#define PUT(p,val) (*(unsigned int *)(p) = (val))

/* Read and write a pointer at address p */
#define GET_PTR(p) (*(unsigned long *) (p))
#define PUT_PTR(p,val) (*(unsigned long *) (p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) -WSIZE)
#define FTRP(bp) ((char *)(bp) +GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp,compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given free block ptr p,computer address of next and previous free blocks*/
#define NEXT_FB(p) ( ((char *)p + WSIZE) ) 
#define PREV_FB(p) ( ((char *)p + WSIZE + ASIZE) )

/* 使用分离适配的方式，定义16个大小类 */
#define SIZE1 (1<<5)
#define SIZE2 (1<<6)
#define SIZE3 (1<<7)
#define SIZE4 (1<<8)
#define SIZE5 (1<<9) 
#define SIZE6 (1<<10)      /* 1KB */
#define SIZE7 (1<<11)
#define SIZE8 (1<<12)
#define SIZE9 (1<<13)
#define SIZE10 (1<<14)
#define SIZE11 (1<<15)
#define SIZE12 (1<<16)
#define SIZE13 (1<<17)
#define SIZE14 (1<<18)
#define SIZE15 (1<<19)
#define SIZE16 (1<<20)     /* 1MB */

void *free_head;
void mm_check();

/* 
 * mm_init - initialize the malloc package.
 * 一个首块和一个结尾块，16个链表头位置放在首块中
 */
int mm_init(void)
{
	int i;
	char *bp;
	if((free_head = mem_sbrk(16 * ASIZE + 4 * WSIZE + WSIZE)) == (void *)-1)
		return -1;
	free_head = (char *) free_head + WSIZE;
	bp = (char *)free_head + WSIZE;
	/* 修改首块的头部和尾部 */
	PUT(HDRP(bp), PACK(16 * ASIZE + 2 * WSIZE, 1));
	PUT(FTRP(bp), PACK(16 * ASIZE + 2 * WSIZE, 1));

	/* 初始化首块中的16个链表头指向NULL */
	for(i = 0; i < 16; i++){
		PUT_PTR( (char *)free_head + WSIZE + i * ASIZE, NULL);
	}

	/* 修改尾块的头部和首部 */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(2 * WSIZE, 1));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(2 * WSIZE, 1));
	
	return 0;
}

int get_list_offset(size_t asize){
	if(asize <= SIZE1)
		return 0;
	else if (asize <= SIZE2)
		return 1;
	else if (asize <= SIZE3)
		return 2;
	else if (asize <= SIZE4)
		return 3;
	else if (asize <= SIZE5)
		return 4;
	else if (asize <= SIZE6)
		return 5;
	else if (asize <= SIZE7)
		return 6;
	else if (asize <= SIZE8)
		return 7;
	else if (asize <= SIZE9)
		return 8;
	else if (asize <= SIZE10)
		return 9;
	else if (asize <= SIZE11)
		return 10;
	else if (asize <= SIZE12)
		return 11;
	else if (asize <= SIZE13)
		return 12;
	else if (asize <= SIZE14)
		return 13;
	else if (asize <= SIZE15)
		return 14;
	else if (asize <= SIZE16)
		return 15;
	else
		return 15;
}

/* 再指定链表中查找可用块 */
static void *free_fit(void *list_head, size_t asize){
	void *p = list_head;
	while(p){
		if(GET_SIZE(p) >= asize)
			return (char *)p + WSIZE;
		else 
			p = GET_PTR(NEXT_FB(p));
	}
	return NULL;		
}


/* find the first free_block , return bp */
static void *find_fit(size_t asize){
	char *bp = NULL;
	int offset = get_list_offset(asize);
	for( ; offset <= 15; offset++){
		bp = free_fit( (void *) (GET_PTR((char *)free_head + WSIZE + offset * ASIZE)), asize );
		if(bp)
			return bp;
	}
	return NULL;
}

/* 将空闲块插入到合适的链表中 */
void insert_list(void *bp){
	size_t asize = GET_SIZE(HDRP(bp));
	int offset = get_list_offset(asize);
	void *p = GET_PTR((char *)free_head + WSIZE + offset * ASIZE);
	if(p){
		PUT_PTR((char *)free_head + WSIZE + offset * ASIZE, HDRP(bp));
		PUT_PTR(PREV_FB(HDRP(bp)), NULL);
		PUT_PTR(NEXT_FB(HDRP(bp)), p);
		PUT_PTR(PREV_FB(p), HDRP(bp));
	}
	else{
		PUT_PTR((char *)free_head + WSIZE + offset * ASIZE, HDRP(bp));
		PUT_PTR(PREV_FB(HDRP(bp)), NULL);
		PUT_PTR(NEXT_FB(HDRP(bp)), NULL);
	}
}

/* 将空闲块从链表中删除 */
void delete_list(void *bp){
	void *prev = GET_PTR(PREV_FB(HDRP(bp)));
	void *next = GET_PTR(NEXT_FB(HDRP(bp)));
	size_t asize = GET_SIZE(HDRP(bp));
	int offset = get_list_offset(asize);
	if(prev && next){
		PUT_PTR(NEXT_FB(prev),next);
		PUT_PTR(PREV_FB(next),prev);
	}
	else if (!prev && next){
		PUT_PTR(free_head + WSIZE + offset * ASIZE, next);
		PUT_PTR(PREV_FB(next), NULL);
	}
	else if (prev && !next){
		PUT_PTR(NEXT_FB(prev), NULL);
	}
	else if (!prev && !next){
		PUT_PTR((char *)free_head + WSIZE + offset * ASIZE, NULL);
	}
}


/* 填充空闲块(从链表中删除)，并进行分割 */
void place(void *bp, size_t asize){
	size_t oldsize,newsize;

	oldsize = GET_SIZE(HDRP(bp));
	newsize = oldsize - asize;
	delete_list(bp);
	if(newsize >= MINBLOCK){
		PUT(HDRP(bp),PACK(asize,1));
		PUT(FTRP(bp),PACK(asize,1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp),PACK(newsize,0));
		PUT(FTRP(bp),PACK(newsize,0));
		insert_list(bp);
	}
	else{
		PUT(HDRP(bp),PACK(oldsize,1));
		PUT(FTRP(bp),PACK(oldsize,1));
	}
}



/* 空闲块合并 */
static void *coalesce(void *bp){
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if(prev_alloc && next_alloc){
		;
	}

	else if(prev_alloc && !next_alloc){
		delete_list(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size,0));
		PUT(FTRP(bp), PACK(size,0));
	}
	
	else if(!prev_alloc && next_alloc){
		delete_list(PREV_BLKP(bp));
		size +=	GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	else{
		delete_list(PREV_BLKP(bp));
		delete_list(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
		bp = PREV_BLKP(bp);
	}
	insert_list(bp);
	return bp;
}	

static void *extend_heap(size_t asize){
	void *p;
	char *bp;
	
	if( (p = mem_sbrk(asize)) == (void *)-1)
		return NULL;
	bp = (char *)p - GET_SIZE((char *)p - WSIZE) + WSIZE;

	PUT(HDRP(bp), PACK(asize,0));
	PUT(FTRP(bp), PACK(asize,0));

	PUT(HDRP(NEXT_BLKP(bp)), PACK(2*WSIZE,1));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(2*WSIZE,1));
	return coalesce(bp);

}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
	size_t extendsize;
	size_t asize;
	if(size == 0)
		return NULL;
	
	if( size <= 2 * ASIZE)
		asize = MINBLOCK;
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    char *bp;
	if((bp = find_fit(asize)) != NULL){   /*查找适合的空闲块*/
		place(bp,asize);                  /*进行分配以及分割*/
		return bp;
	}
	
	extendsize = asize;    /*没找到，扩展堆*/
	if((bp = extend_heap(extendsize)) == NULL)  /* 扩展部分返回一个空闲块  */
		return NULL;
	place(bp,asize);
	
	return bp;
}


void mm_free(void *ptr)
{
	if(ptr == NULL)
		return;
	char *bp = ptr;
	size_t size = GET_SIZE(HDRP(bp));

	PUT(HDRP(bp), PACK(size,0));
	PUT(FTRP(bp), PACK(size,0));
	coalesce(bp);
}



/*  有以下几种情况：
 *  1. size为0，则等于free
 *  2. ptr为null,则等于malloc
 *  3. ptr不为null,原size大于现size,直接缩小,分割
 *  4. ptr不为null,原size小于现size,free之后再malloc，然后搬运
 */

void *mm_realloc(void *ptr, size_t size)
{
	size_t oldsize,asize,newsize;
	char *oldptr;

	if(size == 0){
		mm_free(ptr);
		return NULL;
	}
	
	if(ptr == NULL){
		return mm_malloc(size);
	}
	
	oldsize = GET_SIZE(HDRP(ptr));

	if( size <= 2 * ASIZE)
		asize = MINBLOCK;
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);


	if(oldsize >= asize){
		/* 缩小 */
		newsize = oldsize - asize;
		
		if(newsize >= MINBLOCK){
			PUT(HDRP(ptr),PACK(asize,1));
			PUT(FTRP(ptr),PACK(asize,1));
			ptr = NEXT_BLKP(ptr);
			PUT(HDRP(ptr),PACK(newsize,0));
			PUT(FTRP(ptr),PACK(newsize,0));
			insert_list(ptr);
			ptr = PREV_BLKP(ptr);
		}
	}
	else{
		oldptr = ptr;
		ptr = mm_malloc(size);	
		memmove(ptr,oldptr,oldsize - 2 * WSIZE);
		mm_free(oldptr);
	}
	return ptr;
}



