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
    "4 team",
    /* First member's full name */
    "Cho Yunhee",
    /* First member's email address */
    "y0c0y@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12) //초기 가용 블록과 힙 확장을 위한 기본 크기

#define MAX(x, y) ((x) > (y) ?(x) : (y))

/* Pack a size and allocated bit into a word*/
#define PACK(size, alloc) ((size) |(alloc)) // pack매크로 : 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값 리턴

/*Read and write a word at address P*/
#define GET(p) ((*(unsigned int *)(p)))
#define PUT(p, val) ((*(unsigned int *)(p)) = (val))

/*Read the size and allocated fields from address P*/
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/*Given block ptr bp, compute address of its header and footer*/
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp, compute address of next and previous sand footer */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define MIN_HEAP_SIZE 24

#define PRED_FREE(bp) (*(void**)(bp))
#define SUCC_FREE(bp) (*(void**)(bp + WSIZE))

// Declaration

static void *heap_listp;
static char *last_bp;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t adjusted_size);
static void place(void *bp, size_t a_size);


static void *find_fit(size_t adjusted_size) {
    char *bp = last_bp;

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size) {
            last_bp = bp;
            return bp;
        }
    }

    bp = heap_listp;
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size) {
            last_bp = bp;
            return bp;
        }
    }

    return NULL;
}


static void place(void *bp, size_t adjusted_size) {
    size_t current_size = GET_SIZE(HDRP(bp));

    if ((current_size - adjusted_size) >= (2 * (DSIZE))) {
        // 요청 용량 만큼 블록 배치
        PUT(HDRP(bp), PACK(adjusted_size, 1));
        PUT(FTRP(bp), PACK(adjusted_size, 1));
        
        bp = NEXT_BLKP(bp);
        // 남은 블록에 header, footer 배치
        PUT(HDRP(bp), PACK(current_size - adjusted_size, 0));
        PUT(FTRP(bp), PACK(current_size - adjusted_size, 0));
    }
    else {      // csize와 aszie 차이가 네 칸(16byte)보다 작다면 해당 블록 통째로 사용
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
    }
}


static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 이전 블록과 다음 블록이 모두 할당된 경우
    if (prev_alloc && next_alloc) {
        last_bp = bp;
        return bp;
    }

    // 이전 블록이 할당되고 다음 블록이 가용인 경우
    if (!next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // 이전 블록이 가용하고 다음 블록이 할당된 경우
    if (!prev_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    last_bp = bp;
    return bp;
}


static void* extend_heap(size_t words)
{
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    size = MAX(size, MIN_HEAP_SIZE);
    if((long)(bp = mem_sbrk(size)) == -1) return NULL;

    /*Initialize free block header/footer and the epilpgue header*/
    PUT(HDRP(bp), PACK(size, 0)); // free block header
    PUT(FTRP(bp), PACK(size, 0)); // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    /*Coalesce if the previous block was free*/
    return coalesce(bp);
}



/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // Create the initial empty heap
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {  // heap_listp가 힙의 최댓값 이상을 요청한다면 fail
        return -1;
    }

    PUT(heap_listp, 0);                             // Alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // Prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // Prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // Epilogue header
    heap_listp += (2*WSIZE);

    // Extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    last_bp = (char *)heap_listp;   // heap_listp는 void였기 때문에 last_bp에 맞게 char형으로 변환
    return 0;
}

void *mm_malloc(size_t size) {
    size_t adjusted_size;       // adjusted block szie
    size_t extend_size;         // Amount to extend heap if no fit
    char *bp;

    // Ignore spurious requests
    if (size == 0) {
        return NULL;
    }

    // Adjust block size to include overhead and alignment reqs
    if (size <= DSIZE) {    // 2words 이하의 사이즈는 4워드로 할당 요청 (header 1word, footer 1word)
        adjusted_size = 2*DSIZE;
    }
    else {                  // 할당 요청의 용량이 2words 초과 시, 충분한 8byte의 배수의 용량 할당
        adjusted_size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    // Search the free list for a fit
    if ((bp = find_fit(adjusted_size)) != NULL) {   // 적당한 크기의 가용 블록 검색
        place(bp, adjusted_size);                   // 초과 부분을 분할하고 새롭게 할당한 블록의 포인터 반환
        last_bp = bp;
        return bp;
    }

    // NO fit found. Get more memory and place the block
    extend_size = MAX(adjusted_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size/WSIZE)) == NULL) {    // 칸의 개수
        return NULL;
    }
    place(bp, adjusted_size);
    last_bp = bp;
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) {
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE);   // 2*WISE는 헤더와 풋터

    // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
    if (new_size <= old_size) {
        return bp;
    }
    // new_size가 old_size보다 크면 사이즈 변경
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

    // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 그거 바로 합쳐서 쓰기
    if (!next_alloc && current_size >= new_size) {
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
        return bp;
    }
        // 아니면 새로 block 만들어서 거기로 옮기기
    else {
        void *new_bp = mm_malloc(new_size);
        place(new_bp, new_size);
        memcpy(new_bp, bp, new_size);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
        mm_free(bp);
        return new_bp;
    }
}