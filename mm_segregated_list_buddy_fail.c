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
    "6team",
    /* First member's full name */
    "wschoi",
    /* First member's email address */
    "ghkdgo8686@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본 상수 및 매크로 */
#define WSIZE 4 /* Word 및 header/footer 크기(바이트) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* 이 양(바이트)만큼 힙을 확장합니다 */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* 크기와 할당된 비트를 워드로 묶음 */
#define PACK(size, alloc) ((size) | (alloc))

/* 주소 p에서 워드를 읽고 쓴다 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소 p에서 크기와 할당된 필드를 읽습니다 */
#define GET_SIZE(p) (GET(p) & ~0x7) // 메모리 블록의 세자리 비트를 제외한 나머지 정보를 반환
#define GET_ALLOC(p) (GET(p) & 0x1) // 메모리 블록의 마지막 한자기 비트(얼로케이트) 정보를 반환

/* 블록 ptr bp가 주어지면 헤더와 푸터의 주소를 계산합니다 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
// #define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 ptr bp가 주어지면 다음 블록과 이전 블록의 주소를 계산합니다 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소

// 가용 리스트의 개수
#define SEGREGATED_SIZE (20) 

// 해당 가용 리스트의 루트
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

void *heap_listp;

static void *next_fit_sbp = NULL; // search block pointer

static void *coalesce(void *bp);
static void *find_fit( size_t asize, size_t flag );
static void place(void *bp, size_t asize);
static void *extend_heap(size_t words);
// 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수
static void splice_free_block(void *bp);
// 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수
static void add_free_block(void *bp);


static size_t find_fit_flag = 1;

static void *extend_heap(size_t words)
{
    // printf("extend_heap\n");
    char *bp; // 블록 포인터 생성
    size_t size;

    /* 워드의 정렬을 유지하기 위해 짝수개로 할당한다. */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* 프리 블록의 헤더, 푸터 및 에필로그 헤더 초기화 */
    PUT(HDRP(bp), PACK(size,0)); // 가용 블록 헤더

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // 새 에필로그 헤더

    if(find_fit_flag == 2){
        next_fit_sbp = NEXT_BLKP(bp);
    }

    // 이전 블록이 가용 블록인 경우 병합
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    add_free_block(bp);                                      // 현재 블록을 free list에 추가
    size_t csize = GET_SIZE(HDRP(bp));                       // 반환할 사이즈
    void *root = heap_listp + (SEGREGATED_SIZE + 1) * WSIZE; // 실제 메모리 블록들이 시작하는 위치
    void *left_buddyp;                                       // 왼쪽 버디의 bp
    void *right_buddyp;                                      // 오른쪽 버디의 bp
    
    while (1)
    {
        // 좌우 버디의 bp 파악
        if ((bp - root) & csize) // 현재 블록에서 힙까지의 메모리 합(bp - root)과 csize가 중복되는 비트가 있다면 현재 블록은 오른쪽 버디에 해당
        {
            left_buddyp = bp - csize;
            right_buddyp = bp;
        }
        else
        {
            right_buddyp = bp + csize;
            left_buddyp = bp;
        }

        // 양쪽 버디가 모두 가용 상태이고, 각 사이즈가 동일하면 (각 버디가 분할되어있지 않으면)
        if (!GET_ALLOC(HDRP(left_buddyp)) && !GET_ALLOC(HDRP(right_buddyp)) && GET_SIZE(HDRP(left_buddyp)) == GET_SIZE(HDRP(right_buddyp)))
        {
            splice_free_block(left_buddyp); // 양쪽 버디를 모두 가용 리스트에서 제거
            splice_free_block(right_buddyp);
            csize <<= 1;                            // size를 2배로 변경
            PUT(HDRP(left_buddyp), PACK(csize, 0)); // 왼쪽 버디부터 size만큼 가용 블록으로 변경
            add_free_block(left_buddyp);            // 가용 블록으로 변경된 블록을 free list에 추가
            bp = left_buddyp;
        }
        else
            break;
    }
    return bp;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{   
    /* 초기화된 빈 힙 생성 */
    if ((heap_listp = mem_sbrk((SEGREGATED_SIZE+4)*WSIZE)) == (void *)-1) { // 8워드 크기의 힙 생성,
    // heap_listp의 힙의 시작 주소값 할당(가용 블록만 추적함)
        return -1;
    }
    PUT(heap_listp, 0); // 초기 패딩 삽입
    PUT(heap_listp + (1*WSIZE), PACK((SEGREGATED_SIZE + 2)* WSIZE, 1)); // 프롤로그 블록의 헤더 삽입

    for (int i = 0; i < SEGREGATED_SIZE; i++)
    {
        PUT(heap_listp+ ((2+i) * WSIZE), NULL);
    }
    PUT(heap_listp + ((SEGREGATED_SIZE + 2) * WSIZE), PACK((SEGREGATED_SIZE + 2) * WSIZE, 1));  // 프롤로그 블록의 푸터 삽입    

    PUT(heap_listp + ((SEGREGATED_SIZE + 3) * WSIZE), PACK(0, 1));  // 에필로그 블록의 헤더 삽입
    
    /* 여기까지 했을때 전체 힙의 모양은 
        빈공간 + 프롤로그 헤더 + 프롤로그 푸터 + 가용 블록 + 에필로그 헤더가 된다. */
    heap_listp += (2 * WSIZE); // 첫 가용 블록의 bp
    
    if(find_fit_flag == 2){
        next_fit_sbp = heap_listp;
    }

    if (extend_heap(4) == NULL)
        return -1;
    /* 청크 사이즈의 가용 블록으로 빈 힙을 확장한다. */
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    
    return 0;
}

size_t getAsize(size_t size){
    size_t asize;
        /* 오버헤드 및 정렬 요구 사항을 포함하도록 블록 크기를 조정합니다. */
    if(size <= DSIZE){
        asize = 2*DSIZE; // 왜 16바이트인가... 헤더 1블록 4바이트, 푸터 1블록 4바이트, 데이터는 정렬 조건을 맞추기 위해 2블록 이상 필요
    }else{
        asize = DSIZE * (( size + (DSIZE) + (DSIZE-1) ) / DSIZE);
    }
    return asize;    
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    // printf("malloc\n");
    size_t asize = 16; /* 조정된 블록 사이즈 */ 
    size_t extendsize; /* 적합하지 않을 때 힙을 확장할 용량  */
    char *bp; // 블록 포인터

    /* 유효하지 않은 요청 무시 */    
    if(size == 0){
        return NULL;
    }
    
    /* 오버헤드 및 정렬 요구 사항을 포함하도록 블록 크기를 조정합니다. */
    /*
        (find_fit과 splice_free_block, add_free_block 함수는 Segregated-fits와 동일하다.)
        요청 받은 size에 헤더와 푸터 크기인 8bytes를 더하고 나서 2의 n승이 되도록 올림 처리한 후 크기에 맞는 가용 블록을 탐색한다.
    */
    /* 사이즈 조정 */
    while (asize < size + DSIZE) // 요청받은 size에 8(헤더와 푸터 크기)를 더한 값을 2의 n승이 되도록 올림
    {
        asize <<= 1;
    }

    // printf("작동 시작");
    /* 적합한 가용영역 검색 */
    if ((bp = find_fit(asize, find_fit_flag)) != NULL){
        place(bp, asize);
        return bp;
    }

    /* 적합한 가용 용량이 없을 때 메모리 확보 후 데이터 배치한다. */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;

}


static void *find_fit( size_t asize, size_t flag )
{   
    int class = get_class(asize);
    void *bp = GET_ROOT(class);

    if (flag == 1){ // first fit
        while (class < SEGREGATED_SIZE) // 현재 탐색하는 클래스가 범위 안에 있는 동안 반복
        {
            bp = GET_ROOT(class);
            while (bp != NULL)
            {
                if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
                    return bp;
                bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
            }
            class += 1;
        }
        
    }else if(flag == 2){ // next fit
       
        for (bp = (char*)next_fit_sbp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
            if ((asize <= GET_SIZE(HDRP(bp)))) {
        // printf("1차 값 갱신\n");
                next_fit_sbp = NEXT_BLKP(bp); // 다음 탐색 위치 갱신
                return bp;
            }
        }
        // 다음 fit을 위해 처음부터 다시 탐색
        for (bp = (char*)heap_listp; bp != next_fit_sbp; bp = NEXT_BLKP(bp)) {
            if ((asize <= GET_SIZE(HDRP(bp))) ) {
        // printf("2차 값 갱신\n");
                next_fit_sbp = NEXT_BLKP(bp); // 다음 탐색 위치 갱신
                return bp;
            }
        }

    }else if(flag == 3){ // best fit
        void *bp_temp = NULL;
        // printf(" bp_temp %d \n", GET_SIZE(HDRP(bp_temp)));
        for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
            if((asize <= GET_SIZE(HDRP(bp)))){
                // printf("in for ..  bp_temp %d bp .. %d\n", GET_SIZE(HDRP(bp_temp)),GET_SIZE(HDRP(bp)));
                if (bp_temp != NULL){
                    if ( GET_SIZE(HDRP(bp_temp)) > GET_SIZE(HDRP(bp)) ){
                        bp_temp = bp;
                    }
                }else{
                    bp_temp = bp;
                }
            }
        }
        return bp_temp;
        
    }else{ // first fit
        while (class < SEGREGATED_SIZE) // 현재 탐색하는 클래스가 범위 안에 있는 동안 반복
        {
            bp = GET_ROOT(class);
            while (bp != NULL)
            {
                if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
                    return bp;
                bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
            }
            class += 1;
        }
    }



    return NULL;
}

static void place( void *bp, size_t asize )
{      
    /*
     * 할당할 블록을 탐색할 때는 Segregated-fits와 동일하게 크기에 맞는 가용 리스트에서 탐색을 진행하고, 블록이 존재하지 않는다면 다음 가용 리스트로 이동해서 탐색을 이어나간다.
     * 선택한 블록의 크기가 할당하려는 size와 다르다면 필요한 사이즈의 블록이 될 때까지 반으로 나누고 사용하지 않는 부분은 나눠진 크기에 적합한 가용 리스트에 추가한다.
    */
    splice_free_block(bp);             // free_list에서 해당 블록 제거
    size_t csize = GET_SIZE(HDRP(bp)); // 사용하려는 블록의 크기

    while (asize != csize) // 사용하려는 asize와 블록의 크기 csize가 다르면
    {
        csize >>= 1;                           // 블록의 크기를 반으로 나눔
        PUT(HDRP(bp + csize), PACK(csize, 0)); // 뒷부분을 가용 블록으로 변경
        add_free_block(bp + csize);            // 뒷부분을 가용 블록 리스트에 추가
    }
    PUT(HDRP(bp), PACK(csize, 1)); // 크기가 같아지면 해당 블록 사용 처리
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{   
    // printf("free\n");
    size_t size = GET_SIZE(HDRP(ptr)); // 블록 포인터의 헤더에서 크기정보와 주소를 읽는다.

    PUT(HDRP(ptr), PACK(size,0)); // 해당 블록 포인터의 헤더와 푸터를 할당 해제 해준다.
    
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // printf("realloc\n");
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    size_t asize;
    // printf("사이즈가 더 큼?");
    if (ptr == NULL){
        newptr = mm_malloc(size);
        return newptr;
    } 
    if (size == 0){
        mm_free(ptr);
        return NULL;
    }

    int now_size = GET_SIZE(HDRP(oldptr));
    int prev_is_alloc = GET_ALLOC(HDRP(PREV_BLKP( oldptr )));
    int prev_size = GET_SIZE(HDRP(PREV_BLKP(oldptr )));
    int next_is_alloc = GET_ALLOC(HDRP(NEXT_BLKP( oldptr )));
    int next_size = GET_SIZE(HDRP(NEXT_BLKP( oldptr )));
    
    // if( prev_is_alloc && next_is_alloc ){ // 앞뒤 블록이 할당 되있는 경우
    //     // 가독성 향상을 위해 코드 위치 변경
    // }
    // else 
    if ( prev_is_alloc && !next_is_alloc ){ // 앞 블록이 할당 되있는 경우
        asize = getAsize(size);
        if( (now_size + next_size) <= asize ){
            oldptr = coalesce( oldptr );
            place(oldptr, asize);
            return oldptr;
        }
    }
    else if ( !prev_is_alloc && next_is_alloc ){ // 뒤 블록이 할당 되있는 경우
        asize = getAsize(size);
        if( (now_size + prev_size) <= asize ){
            oldptr = coalesce( oldptr );
            place(oldptr, asize);
            return oldptr;
        }
    }
    else{ // 둘다 할당 안되있는 경우
        asize = getAsize(size);
        if( (prev_size + now_size + next_size) <= asize ){
            oldptr = coalesce( oldptr );
            place(oldptr, asize);
            return oldptr;
        }    
    }
    // 케이스에 해당하지 않는 경우
    newptr = mm_malloc(size);
    if (newptr == NULL){
        return NULL;
    }
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize){
        copySize = size;
    }
    memmove(newptr, oldptr, copySize);// 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 copySize만큼의 문자를 new_bp로 복사해라)
    mm_free(oldptr);
    return newptr;

}

// 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수
static void splice_free_block(void *bp)
{
    int class = get_class(GET_SIZE(HDRP(bp)));
    if (bp == GET_ROOT(class)) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        GET_ROOT(class) = GET_SUCC(GET_ROOT(class)); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}
 // 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수
static void add_free_block(void *bp)
{
    GET_SUCC(bp) = heap_listp;     // bp의 SUCC은 루트가 가리키던 블록
    if (heap_listp != NULL)        // free list에 블록이 존재했을 경우만
        GET_PRED(heap_listp) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    heap_listp = bp;               // 루트를 현재 블록으로 변경
}
// 적합한 가용 리스트를 찾는 함수
int get_class(size_t size)
{
    int next_power_of_2 = 1;
    int class = 0;
    while (next_power_of_2 < size && class + 1 < SEGREGATED_SIZE)
    {
        next_power_of_2 <<= 1;
        class ++;
    }

    return class;
}