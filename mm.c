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
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

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
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 ptr bp가 주어지면 다음 블록과 이전 블록의 주소를 계산합니다 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;
static void *coalesce(void *bp);
static char *find_fit( size_t asize );
static void place(void *bp, size_t asize);

static void *extend_heap(size_t words)
{
    char *bp; // 블록 포인터 생성
    size_t size;

    /* 워드의 정렬을 유지하기 위해 짝수개로 할당한다. */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* 프리 블록의 헤더, 푸터 및 에필로그 헤더 초기화 */
    PUT(HDRP(bp), PACK(size,0)); // 가용 블록 헤더
    PUT(FTRP(bp), PACK(size,0)); // 가용 블록 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // 새 에필로그 헤더

    // 이전 블록이 가용 블록인 경우 병합
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 크기 반환 
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 크기 반환
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기 반환

    if( prev_alloc && next_alloc ){ // 이전 블록과 다음 블록이 할당되었다면 case 1
        return bp; // 현재 블록 포인터만 반환
    }

    else if( prev_alloc && !next_alloc ){ /* 앞 블록은 할당되어있고 뒤 블록은 할당 안되어 있다면 case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 뒤 블록의 사이즈를 bp 블록 사이즈와 더해준다.
        PUT(HDRP(bp), PACK(size, 0)); // 합쳤으니까, 현재 블록의 헤더는 메모리 할당을 해제하며, 뒤 블록과 합친 사이즈를 사이즈에 할당해준다.
        // printf("%s %s^_^^_^^_^^_^^_^^_^^_^", FTRP(bp),FTRP(NEXT_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0)); // 마찬가지로 푸터는 헤더의 복사본이브로 같은 처리
        // 위에 것이 맞다. 그 이유는 FTRP에서 푸터의 주소를 찾는 방법이 헤더에 정의된 사이즈를 기반으로 찾기 때문이다.
        // PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 마찬가지로 푸터는 헤더의 복사본이브로 같은 처리 
    }

    else if( !prev_alloc && next_alloc ){ /* 앞 블록은 할당 안되어 있고 뒤 블록은 할당되어 있다면 case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 사이즈를 bp 블록 사이즈와 더해줌
        PUT(FTRP(bp), PACK(size, 0)); // 푸터는 메모리 할당 해제하고 크기를 재할당.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 헤더는 이전 블록의 
        bp = PREV_BLKP(bp); 
    }

    else{ // 둘다 할당 안된 경우 case 4
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp); 
    }
    return bp;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{   
    // printf("^_^^_^^_^^_^^_^^_^^_^");
    /*
        할당기는 힙을 하나의 커다란 바이트 배열과, 이 배열의 첫 바이트를 가리키는 포인터 p로 구성할 수 있다.
        size 바이트를 할당하기 위해서 malloc은 현재 p 값을 스택에 저장하고, p를 size 만큼 증가시키며, p의 이전 값을 호출자에게 리턴한다.
    */
    /* 초기화된 빈 힙 생성 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
        return -1;
    PUT(heap_listp, 0); // 초기 패딩 삽입
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 블록의 헤더 삽입
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));  // 프롤로그 블록의 푸터 삽입
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));  // 에필로그 블록의 헤더 삽입
    /* 여기까지 했을때 전체 힙의 모양은 
        빈공간 + 프롤로그 헤더 + 프롤로그 푸터 + 에필로그 헤더가 된다. */
    heap_listp += (2*WSIZE); // 힙 가용 리스트 포인터의 위치를 프롤로그 블록과 에필로그 블록의 사이로 한다.

    /* 청크 사이즈의 가용 블록으로 빈 힙을 확장한다. */
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* 조정된 블록 사이즈 */ 
    size_t extendsize; /* 적합하지 않을 때 힙을 확장할 용량  */
    char *bp; // 블록 포인터

    /* 유효하지 않은 요청 무시 */    
    if(size == 0)
        return NULL;
    
    /* 오버헤드 및 정렬 요구 사항을 포함하도록 블록 크기를 조정합니다. */
    if(size <= DSIZE){
        asize = 2*DSIZE; // 왜 16바이트인가... 헤더 1블록 4바이트, 푸터 1블록 4바이트, 데이터는 정렬 조건을 맞추기 위해 2블록 이상 필요
    }else{
        asize = DSIZE * (( size + (DSIZE) + (DSIZE-1) ) / DSIZE);
    }
    // printf("작동 시작");
    /* 적합한 가용영역 검색 */
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    /* 적합한 가용 용량이 없을 때 메모리 확보 후 데이터 배치한다. */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

}

static char *find_fit( size_t asize )
{   
    // char *temp = heap_listp; // 템프 받음
    // 맨땅 코드 
    // while (NEXT_BLKP(temp) != NULL && GET_SIZE(NEXT_BLKP(temp)) != 0) // 다음블록이 없거나, 다음 블록의 사이즈가 0일때 == 에필로그 블록일 경우
    // {
    //     if ( GET_ALLOC(HDRP(temp))){ // 메모리가 할당 되어 있다면?
    //         temp = NEXT_BLKP(temp); // 다음 블록 확인
    //         continue;
    //     }else{ // 할당이 안되어 있다면? 
    //         if ( GET_SIZE(HDRP(temp)) >= asize ){ // 사이즈 확인
    //             return temp; // 사이즈가 적당하다? 바로 리턴
    //         }else{ // 아니다?
    //             temp = NEXT_BLKP(temp); // 다음 블록 확인
    //         }
    //     }
            
    // }
    // 1차 최적화-답지
    // 분기가 적어서? 
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }

    return NULL;
}

static void place( void *bp, size_t asize )
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 빈 공간의 크기 저장

    if((csize - asize) >= (2*DSIZE)){ // 현재 빈 공간에서 할당할 공간을 뺀 합이 16 바이트 보다 크다면
        PUT(HDRP(bp), PACK(asize,1)); // 데이터 공간 할당
        PUT(FTRP(bp), PACK(asize,1)); // 데이터 공간 할당
        bp = NEXT_BLKP(bp); // 다음 블록으로 이동
        PUT(HDRP(bp), PACK(csize-asize,1)); // 이동한 블럭의 헤더를 설정해 준다.
        PUT(FTRP(bp), PACK(csize-asize,1)); // 푸터를설정해 주어 가용 데이터 블록을 분할한다.
    }else{ // 16바이트 보다 작다면 그냥 할당
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr)); // 블록 포인터의 헤더에서 크기정보와 주소를 읽는다.

    PUT(HDRP(ptr), PACK(size,0)); // 해당 블록 포인터의 헤더와 푸터를 할당 해제 해준다.
    PUT(FTRP(ptr), PACK(size,0)); // 해당 블록 포인터의 헤더와 푸터를 할당 해제 해준다.
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
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);// 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 copySize만큼의 문자를 new_bp로 복사해라)
    mm_free(oldptr);
    return newptr;
}