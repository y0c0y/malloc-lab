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
    "kkjsn6687@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/*define 변수*/
#define ALIGNMENT 8 // 8바이트 정렬


/*define 함수*/
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // 8의 배수로 반올림
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t의 크기를 8의 배수로 반올림

//Segregated free list : 가용 블록을 크기별(2의 지수승)로 분류하여 관리하는 방법

#define WSIZE 4 // word size
#define DSIZE 8 // double word size // 헤더와 푸터의 크기

#define CHUNKSIZE ( 1<<12 ) // 초기 힙 사이즈와 확장 힙 사이즈
#define INITCHUNKSIZE ( 1<<6 ) // 초기 힙 사이즈

// #define LISTLIMIT 20 // segregated list의 크기 

#define MAX(x,y) ((x) > (y) ? (x) : (y)) // 두 값 중 큰 값 반환

// size와 alloc을 할당 할때도 쓰고, 할당 한것을 쓰기 위해서 사용(Read | Write)
#define PACK(size, alloc) ((size) | (alloc)) // size: 블록 크기, 0 : free, 1 : allocated 

#define GET(p) (*(unsigned int *)(p)) // p가 가리키는 word를 읽어옴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p가 가리키는 word에 val을 씀

#define GET_SIZE(p) (GET(p) & ~0x7) // p가 가리키는 블록의 크기를(8의 배수로) 반환 => 32bit/64bit를 기준으로해야 메모리 단편화를 줄일 수 있음
// 32bit : 4byte, 64bit : 8byte
//우리가 현재 쓰고 있는 코어가 i7이므로 64bit를 기준으로 해야함.

#define GET_ALLOC(p) (GET(p) & 0x1) // p가 가리키는 블록의 할당 여부를 반환

#define HDRP(bp) ((char *)(bp) - WSIZE) // 블록의 헤더 포인터를 반환
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록의 푸터 포인터를 반환

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 포인터를 반환, header 사이즈를 빼줘야함
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 포인터를 반환, footer 사이즈를 빼줘야함

/* Declaration*/
static void* heap_listp; // 힙의 시작을 가리키는 포인터

static void *extend_heap(size_t words); // 힙을 사이즈만큼 확장하는 함수
static void *coalesce(void *bp); // free 블록을 합치는 함수
static void *find_fit(size_t asize); // free 블록을 찾는 함수
static void place(void *bp, size_t asize); // free 블록을 할당하는 함수
// static void *find_list(size_t asize); // segregated list에서 free 블록을 찾는 함수
// static void insert_list(void *bp); // segregated list에 free 블록을 삽입하는 함수
// static void delete_list(void *bp); // segregated list에서 free 블록을 삭제하는 함수


static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // Allocate an even number of words to maintain alignment
    // 8의 배수로 맞춰주기 위해 1 word를 더 할당
    size = ALIGN(words);
    if((bp = mem_sbrk(size)) == (void*)-1) // 오류 처리
        return NULL;
    
    // Initialize free block header/footer and the epilogue header
    // 헤더와 푸터를 초기화
    PUT(HDRP(bp), PACK(size, 0)); // free block header
    PUT(FTRP(bp), PACK(size, 0)); // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // New epilogue header

    // 이전 블록이 free 블록이면 coalesce
    return coalesce(bp);
}

// free 블록을 합치는 함수
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당 여부
    size_t size = GET_SIZE(HDRP(bp));// 헤드 포인터 포함 전체 사이즈

    if(prev_alloc && next_alloc) return bp; // 이전 블록과 다음 블록이 모두 할당되어 있는 경우
    else if(prev_alloc && !next_alloc) // 이전 블록만 할당되어 있고 다음 블록만 free 블록인 경우
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 헤더 사이즈를 더해줌
        PUT(HDRP(bp), PACK(size,0)); // 헤더를 새로운 사이즈로 업데이트
        PUT(FTRP(bp), PACK(size,0)); // 푸터를 새로운 사이즈로 업데이트
    }
    else if(!prev_alloc && next_alloc) // 이전 블록이 free 블록이고 다음 블록만 할당되어 있는 경우
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 헤더 사이즈를 더해줌
        PUT(FTRP(bp), PACK(size,0)); // 푸터를 새로운 사이즈로 업데이트
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0)); // 이전 블록의 헤더를 새로운 사이즈로 업데이트
        bp =  PREV_BLKP(bp);// 이전 블록의 포인터를 대입
    }
    else // 이전 블록 및 다음 블록 모두 free 블록인 경우
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));// 이전 블록의 헤더 사이즈와 다음 블록의 푸터 사이즈를 더해줌
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0)); // 이전 블록의 헤더를 새로운 사이즈로 업데이트
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 푸터를 새로운 사이즈로 업데이트
        bp = PREV_BLKP(bp); // 이전 블록의 포인터를 대입
    }
    return bp; // coalesce한 블록의 포인터를 반환
}

// free 블록을 찾는 함수 : first fit
static void *find_fit(size_t asize){ // first fit 검색을 수행
    void *bp;
    for (bp= heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ // init에서 쓴 heap_listp를 쓴다. 처음 출발하고 그 다음이 regular block 첫번째 헤더 뒤 위치네.
        // for문이 계속 돌면 epilogue header까기 간다. epilogue header는 0이니까 종료가 된다.
        if (!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp)))){ // 이 블록이 가용하고(not 할당) 내가 갖고있는 asize를 담을 수 있으면
            return bp; // 내가 넣을 수 있는 블록만 찾는거니까, 그게 나오면 바로 리턴.
        }
    }
    return NULL;  // 종료 되면 null 리턴. no fit 상태.
}

// bp가 가리키는 free 블록을 asize만큼 할당하는 함수
static void place(void *bp, size_t asize)
{
     size_t csize = GET_SIZE(HDRP(bp)); // 현재 있는 블록의 사이즈.

    if ( (csize-asize) >= (2*DSIZE)){ // 현재 블록 사이즈안에서 asize를 넣어도 2*DSIZE(헤더와 푸터를 감안한 최소 사이즈)만큼 남으면 다른 data를 넣을 수 있음.
        PUT(HDRP(bp), PACK(asize,1)); // 헤더위치에 asize만큼 넣고 1(alloc)로 상태변환. 원래 헤더 사이즈에서 지금 넣으려고 하는 사이즈(asize)로 갱신.(자르는 효과)
        PUT(FTRP(bp), PACK(asize,1)); //푸터 위치도 변경.
        bp = NEXT_BLKP(bp); // regular block만큼 하나 이동해서 bp 위치 갱신.
        PUT(HDRP(bp), PACK(csize-asize,0)); // 나머지 블록은(csize-asize) 다 가용하다(0)하다라는걸 다음 헤더에 표시.
        PUT(FTRP(bp), PACK(csize-asize,0)); // 푸터에도 표시.
    }
    else{
        //작으면 해제해 줄 수 없음.
        // asize만 csize에 들어갈 수 있음.
        PUT(HDRP(bp), PACK(csize,1)); 
        PUT(FTRP(bp), PACK(csize,1));
    }
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) // 초기화
{
    //empty heap
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) // 힙을 확장
        return -1;
    PUT(heap_listp, 0); // alignment padding
    //메모리를 연결할 때 가장자리 조건을 만족시키기 위한 트릭
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // epilogue header
    heap_listp += (2*WSIZE); 

    /*
    빈 힙을 chuncksize 만큼 확장시킴
    extend_heap은 워드 사이즈 만큼 확장시키기 때문에 CHUNKSIZE/WSIZE를 인자로 넘겨줌
    만약 NULL이 나오면 공간이 없다는 뜻이므로 -1을 반환
    */
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)// 할당
{
    size_t adjusted_size; // 8의 배수로 맞춰준 사이즈
    size_t extend_size; // 힙을 확장시킬 사이즈
    char *bp;

    if(size == 0) // 사이즈가 0이면 할당하지 않음
        return NULL;
    if(size <= DSIZE) // 사이즈가 8보다 작으면 16으로 맞춰줌
        adjusted_size = 2*DSIZE;
    else // 사이즈가 8보다 크면 8의 배수로 맞춰줌
    {
        adjusted_size = ALIGN(size + DSIZE);
    } 
    
    if((bp = find_fit(adjusted_size)) != NULL) // free 블록을 찾음
    {
        place(bp, adjusted_size); // free 블록을 할당
        return bp;
    }

    extend_size = MAX(adjusted_size, CHUNKSIZE); // 힙을 확장시킬 사이즈를 정함
    if((bp = extend_heap(extend_size/WSIZE)) == NULL) // 힙을 확장
        return NULL;
    place(bp, adjusted_size); // free 블록을 할당

    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)//해제
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size,0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    size_t oldSize = GET_SIZE(HDRP(bp));
    size_t newSize = size + (2 * WSIZE);
    if (newSize <= oldSize) {
        // if ((oldSize - newSize) >= (2*DSIZE)) {
        //     void *want = bp;
        //     PUT(FTRP(bp), PACK(oldSize, 0));
        //     PUT(HDRP(bp), PACK(newSize, 1));
        //     PUT(FTRP(bp), PACK(newSize, 1));
        //     PUT(FTRP(bp) + WSIZE, PACK(oldSize, 0));
        //     // bp = NEXT_BLKP(bp);
        //     // PUT(HDRP(bp), PACK(oldSize - newSize, 0));
        //     // PUT(FTRP(bp), PACK(oldSize - newSize, 0));
        //     // bp = PREV_BLKP(bp);
        //     memcpy(bp, want, newSize);
        // }
        return bp;
    }
    else {
        size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = oldSize + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size_t current_size2 = oldSize + GET_SIZE(HDRP(PREV_BLKP(bp)));
        size_t current_size3 = current_size + GET_SIZE(HDRP(PREV_BLKP(bp)));
        if (!next_alloc && !prev_alloc && current_size3 >= newSize) {
            void *want = bp;
            bp = PREV_BLKP(bp);
            PUT(HDRP(bp), PACK(current_size3, 1));
            PUT(FTRP(bp), PACK(current_size3, 1));
            memmove(bp, want, oldSize);
            return bp;
        }
        else if (!next_alloc && current_size >= newSize) {
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        else if (!prev_alloc && current_size2 >= newSize) {
            void *want = bp;
            bp = PREV_BLKP(bp);
            PUT(HDRP(bp), PACK(current_size2, 1));
            PUT(FTRP(bp), PACK(current_size2, 1));
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
