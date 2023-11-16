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
    "4",
    /* First member's full name */
    "Cho Yunhee",
    /* First member's email address */
    "kkjsn6687@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};
/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE 4400 // 90점
#define MAX(x, y) ((x) > (y)? (x) : (y))
/* PACK은 size와 alloc여부를 or연산하여 나타내줍니다*/
#define PACK(size, alloc) ((size) | (alloc))
/* GET과 PUT 은 각각 주소 p에 있는 값을 읽거나, 값을 저장해줍니다.*/
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
/* GET_SIZE, GET_ALLOC은 각각 p의 size와 할당여부비트를 가져옵니다*/
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/* HDRP와 FTRP는 각각 헤더와 푸터를 가리키는 포인터를 리턴합니다.*/
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/*각각 다음 블록과 이전 블록에 해당하는 포인터를 리턴합니다.*/
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)HDRP(bp))))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/*
 * mm_init - initialize the malloc package.
 */
static void *heap_listp;
static char *last_bp;
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); // 패딩
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그푸터
    PUT(heap_listp + (3*WSIZE), PACK(0,1));      // 에필로그 헤더
    heap_listp += (2*WSIZE); //할당기는 한개의 프롤로그를 가리키는 전역변수를 가져야함.
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    last_bp = (char *)heap_listp;
    return 0;
}
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    /*alignment를 유지하기 위해*/
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    /*프리블럭 헤더 푸터, 그리고  맨 마지막으로는 에필로그가 와야지*/
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    /*이전 블록이 free이면 합체시킴*/
    return coalesce(bp);
}
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) {
        last_bp = PREV_BLKP(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    last_bp = PREV_BLKP(bp);
    return bp;
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    if (size == 0)
        return NULL;
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE *((size + (DSIZE) + (DSIZE-1)) / DSIZE); //
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        last_bp = bp;
        return bp;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    last_bp = bp;
    return bp;
}
static void *find_fit(size_t asize)
{
    /* next-fit*/
    char *bp = last_bp;
    if (bp == NULL) {
        bp = heap_listp;
    }
    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }  // 여기서 안되면 아래서 첨부터 돌리자.
    bp = heap_listp;
    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }
    return NULL;
}
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    size_t oldSize = GET_SIZE(HDRP(bp));
    size_t newSize = size + (2 * WSIZE);
    // if (bp == NULL)
    //     return mm_malloc(size);
    // if (size == 0) {
    //     mm_free(bp);
    //     return NULL;
    // }
    if (newSize <= oldSize) {
        // if ((oldSize - newSize) >= 2 * DSIZE && newSize > 2*DSIZE) {
        //     //printf("들어옴?\n");
        //     //void *want = bp;
        //     PUT(HDRP(bp), PACK(newSize, 1));
        //     PUT(FTRP(bp), PACK(newSize, 1));
        //     //memmove(bp, want, newSize);
        //     bp = NEXT_BLKP(bp);
        //     PUT(HDRP(bp), PACK(oldSize - newSize, 1));
        //     PUT(FTRP(bp), PACK(oldSize - newSize, 1));
        //     mm_free(bp);
        //     return
        // }
        return bp;
    }
    else {
        size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = oldSize + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size_t current_size2 = oldSize + GET_SIZE(HDRP(PREV_BLKP(bp)));
        size_t current_size3 = current_size + GET_SIZE(HDRP(PREV_BLKP(bp)));
        if (!next_alloc && prev_alloc && (current_size >= newSize)) {
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        else if (!prev_alloc && next_alloc && (current_size2 >= newSize)) {
            void *want = bp;
            bp = PREV_BLKP(bp);
            PUT(HDRP(bp), PACK(current_size2, 1));
            PUT(FTRP(bp), PACK(current_size2, 1));
            memmove(bp, want, oldSize);
            return bp;
        }
        else if (!next_alloc && !prev_alloc && current_size3 >= newSize) {
            void *want = bp;
            bp = PREV_BLKP(bp);
            PUT(HDRP(bp), PACK(current_size3, 1));
            PUT(FTRP(bp), PACK(current_size3, 1));
            memmove(bp, want, oldSize);
            return bp;
        }
        else {
            void *new_bp = mm_malloc(newSize);
            place(new_bp, newSize);
            memcpy(new_bp, bp, newSize);
            mm_free(bp);
            return new_bp;
        }
    }
}