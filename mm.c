/*
 * mm.c
 * 
 * Name: RedElephant Andrew Id: shiweid
 *
 * This project is a malloc package using segregated list with first fit
 * policy. In this package, it includes functions such as malloc, free
 * realloc and calloc.
 * 
 * This package also includes a robust heap checker!
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>

#include "mm.h"
#include "memlib.h"

/* If you want to debug, define the debug macro*/ 
/*#define DEBUG*/
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* Configuration macros*/ 
#define LIFO /* The list organize policy*/ 

/* Notice: NUM_LINEAR and NUM_INF should be in power of 2*/ 
#define NUM_LINEAR 1  /*The number of linear seg list*/ 
#define NUM_INF 2048  /*Infinite threshold of seg list*/ 
#define NUM_LIST 12

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE 64  /* Extend heap by this amount (bytes) */ 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word 
 * Alloc:0 unallocated Alloc:1 allocated 
 * Alloc:2 unallocated previous allocated
 * Alloc:3 allocated previous allocated
 * */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given free block ptr bp, compute address or address pointer of the
 * next and previous blocks */ 
#define NEXT_FBLKP(bp)  ((char*)(bp)) 
#define PREV_FBLKP(bp)  ((char*)(bp + WSIZE))

/*
 * Return true if address is valid with 0x8XXXXXXXX format
 */
static inline int is_addr(void *bp) {
    return (((unsigned long long)bp >> 32) == 0x8);
}

/* 
 * To store a double word size address in a wsize space
 * If value is an addr, then store the address
 * Elseware the value should be a list number of segregated list
 */ 
static inline void put_addr(void *bp, void *value) {
    if(is_addr(value)) /* Truncate the value into wsize(8 bytes)*/ 
        *(unsigned int*)bp = (unsigned int)(size_t)value;
    else
        *(int*)bp = (int)(long)value; 
}

/*
 * Get address(8 bytes) from a word size(4 bytes) space
 * return 0x8xxxxxxxx if it is a valid address
 * else return the list number since it should be at the begining of a list
 */ 
static inline void *get_addr(void *bp) {
    if(*(int*)bp > 0)
        return (void *)(((unsigned long long)0x8<<32) | *(unsigned int*)bp);
    else
        return (void *)((long)(-(*(int*)bp))); /*the list num was stored as a negative number*/ 
}

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */ 
static char **seg_listp;      /* The segregated list pointer*/ 
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/*Function prototypes for internal help routines*/
static void *extend_heap(size_t words);
static void *coalesce(void* bp);
static void place(void* bp, size_t asize);
static void *find_fit(size_t asize);
static int find_list(size_t asize);
static int find_list_fit(size_t asize);
static void printblock(void* bp);
static void checkblock(void* bp);
static int checkfreelist(void *flist, int verbose);
static int init_seglist();
static inline void insert(int list_num, void* bp);
static inline void delete(void* bp);

/* An interupt handler function for debugging*/ 
void fl_timeout()
{
    printf("check free list timeout, may have a loop!\n");
    exit(1);
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    
    if(init_seglist() == -1) {
        printf("fail to init seg list!\n");
        return -1;
    }

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 3));     /* Epilogue header */
    heap_listp += 2*WSIZE;

#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;

    return 0;
}

/*
 * Initialize the segregated list, Return -1 on error
 * Return 1 on success
 */
static int init_seglist(){

    dbg_printf("the number of list is %d\n", NUM_LIST);

    if ((seg_listp = mem_sbrk(2*WSIZE * NUM_LIST)) == (void *)-1)
        return -1;

    for (int i = 0; i < NUM_LIST; i++){
        seg_listp[i] = 0;
    }

    return 1;
}

/*
 * malloc: Allocate blocks of memory, return the pointer to 
 * the allocated space. Return NULL if failed
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    dbg_printf("starting malloc(%d)\n", (int)size);
    if (heap_listp == 0){
        mm_init();
    }

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= (DSIZE + WSIZE))                     
        asize = 2*DSIZE;                  
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) { 
        dbg_printf("start to place at 0x%lx with size %d\n", (long)bp, (int)asize);
        place(bp, asize);                
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);  
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                   
    place(bp, asize);                 
    return bp;
}

/*
 * free: free the memory pointed by ptr
 */
void free (void *ptr) {
    dbg_printf("starting free %p\n", ptr);

    if(ptr == 0) 
        return;

    size_t size = GET_SIZE(HDRP(ptr));

    if (heap_listp == 0){
        mm_init();
    }

    /* The free blocks have footer and header. However, allocated blocks
     * only have a header with the previous allocation information in the
     * excess bit in the headr*/ 
    PUT(HDRP(ptr), PACK(size, GET_PREV_ALLOC(HDRP(ptr))));
    PUT(FTRP(ptr), PACK(size, GET_PREV_ALLOC(HDRP(ptr))));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(NEXT_BLKP(ptr))), 
                GET_ALLOC(HDRP(NEXT_BLKP(ptr))) & 1));
    
    int list_num = find_list(size);
    insert(list_num, ptr);

    coalesce(ptr);
}

/*
 * realloc - realloc the memory space from oldptr
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

    dbg_printf("It's in realloc !!\n");

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    return newptr;
}

/*
 * calloc - allocate memory with initial value 0
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap: check if the heap is correct
 * 1. Check boudaries
 * 2. Check blocks information
 * 3. Check free lists correctness
 * 4. Check free block number
 * 5. Check consecutive free blocks
 */
void mm_checkheap(int verbose) {
    char *bp = heap_listp;
    int fbcnt = 0;
    int fbcnt2 = 0;
    int ct_fb = 0;   /*a flag to know if there are two consecutive free blocks*/ 

    if (verbose == 3)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose == 3) 
            printblock(bp);
        checkblock(bp);
        if(GET_ALLOC(HDRP(bp)) == 0) {
            fbcnt2++;
            if(ct_fb == 1){
                printf("Coalesce Error: two consecutive free blocks!\n");
            }
            ct_fb = 1;
        }
        else
            ct_fb = 0;
    }

    for (int i = 0; i < NUM_LIST; i++){
        if (verbose == 4)
            printf("Segregated list: %d\n", i);
        fbcnt += checkfreelist(seg_listp[i], verbose);
    }

    if (fbcnt2 != fbcnt) {
        printf("The free blocks in the free lists: %d doesn't mactched that in the heap: %d\n", fbcnt, fbcnt2);
    }
    if (verbose == 3)
        printblock(bp);

    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

/*
 * Extend heap with free blocks and return its block pointer
 */
static void *extend_heap(size_t words){
    dbg_printf("Extending the heap!\n");
    char *bp;
    size_t size;

    /*Allocate an even number of words to maintain alignments*/
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /*Intialize free block header/footer and the epilogue header*/
    PUT(HDRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp))));
    dbg_printf("the get_prev_alloc %d\n", GET_PREV_ALLOC(HDRP(bp)));
    PUT(FTRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp))));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /*The new epilogue block*/ 
#ifdef LIFO 
    int list_num = find_list(size);
    insert(list_num, bp);
#endif

    /*Coalasce if the previous block is free*/ 
    return coalesce(bp);
}

/*
 * Perform coalesce, there are four cases
 * 1: previous: allocated next: allocated
 * 2: previous: allocated next: free
 * 3: previous: free next: allocated
 * 4: previous: free next: free
 */
static void* coalesce(void *bp) {
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp)) >> 1;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        dbg_printf("coalasce case 2\n");
        char *oldnext_blkp = NEXT_BLKP(bp);

        delete(bp);
        delete(oldnext_blkp);

        size += GET_SIZE(HDRP(oldnext_blkp));
        PUT(HDRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp))));
        PUT(FTRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp))));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 
                    GET_ALLOC(HDRP(NEXT_BLKP(bp))) & 1));

        int list_num = find_list(size);
        insert(list_num, bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        dbg_printf("coalasce case 3\n");
        char *oldprev_blkp = PREV_BLKP(bp);
        
        delete(bp);
        delete(oldprev_blkp);

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0 | GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0 | GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        bp = PREV_BLKP(bp);
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 
                    GET_ALLOC(HDRP(NEXT_BLKP(bp))) & 1));
      
        int list_num = find_list(size);
        insert(list_num, bp);
    }

    else {                                     /* Case 4 */
        dbg_printf("coalasce case 4\n");
        char *oldprev_blkp = PREV_BLKP(bp);
        char *oldnext_blkp = NEXT_BLKP(bp);

        delete(bp);
        delete(oldprev_blkp);
        delete(oldnext_blkp);

        size += GET_SIZE(HDRP(oldprev_blkp)) + 
            GET_SIZE(FTRP(oldnext_blkp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0 | GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0 | GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        bp = PREV_BLKP(bp);
        PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 
                    GET_ALLOC(HDRP(NEXT_BLKP(bp))) & 1));

        int list_num = find_list(size);
        insert(list_num, bp);
    }
#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
        rover = bp;
#endif
    return bp;
} 

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - asize;
    char *old = bp;
    void *old_nextp = get_addr(NEXT_FBLKP(old));
    void *old_prevp = get_addr(PREV_FBLKP(old));

    if(remainder >= (2 * DSIZE)) {
        
        PUT(HDRP(bp), PACK(asize, (GET_PREV_ALLOC(HDRP(bp)) | 1)));
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(remainder, 2));
        PUT(FTRP(bp), PACK(remainder, 2)); 


        if(is_addr(old_prevp)) 
            put_addr(NEXT_FBLKP(old_prevp), old_nextp);
        else
            seg_listp[(long)old_prevp] = old_nextp;

        if(old_nextp != 0){
            if(is_addr(old_prevp))
                put_addr(PREV_FBLKP(old_nextp), old_prevp);
            else
                put_addr(PREV_FBLKP(old_nextp), (void *)-((long)(old_prevp)));
        }
        
        dbg_printf("remainder bigger than 2 DW, split!\n");
        int list_num = find_list(remainder);
        insert(list_num, bp);
    }
    else { /*The remainder is less than 2 double words, thus no split*/ 
        PUT(HDRP(bp), PACK(csize, (GET_PREV_ALLOC(HDRP(bp)) | 1)));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), (GET_ALLOC(HDRP(bp)) | 2)));

        dbg_printf("remainder less than 2 double words\n");
        if(is_addr(old_prevp)) 
            put_addr(NEXT_FBLKP(old_prevp), old_nextp);
        else
            seg_listp[(long)old_prevp] = old_nextp;

        if(old_nextp != 0){
            if(is_addr(old_prevp))
                put_addr(PREV_FBLKP(old_nextp), old_prevp);
            else
                put_addr(PREV_FBLKP(old_nextp), (void *)-((long)(old_prevp)));
        }
    }
}

/*
 * Insert a free block at the top of list: list_num
 */ 
static inline void insert(int list_num, void* bp) {
    char *old = seg_listp[list_num];

    if(old == 0) { /*The list: list_num has not been initialized*/ 
        seg_listp[list_num] = bp;
        put_addr(NEXT_FBLKP(bp), 0);
        put_addr(PREV_FBLKP(bp), (void*)(long)(-(list_num)));
    } 
    else {  
        seg_listp[list_num] = bp;
        put_addr(NEXT_FBLKP(bp), old);
        put_addr(PREV_FBLKP(old), bp);
        put_addr(PREV_FBLKP(bp), (void*)(long)(-(list_num)));
    }
}

/*
 * Delete a pointer from list
 */
static inline void delete(void* bp) {

    char *prevp = get_addr(PREV_FBLKP(bp));
    char *nextp = get_addr(NEXT_FBLKP(bp));

    if (is_addr(prevp)) {
        put_addr(NEXT_FBLKP(prevp), nextp);
        if(nextp != 0){
            put_addr(PREV_FBLKP(nextp), prevp);
        }
    } else {
        int list_num =(int)(long)(prevp);
        if(nextp != 0){
            put_addr(PREV_FBLKP(nextp), (void*)(-(long)list_num));
            seg_listp[list_num] = nextp;
        } else {
            seg_listp[list_num] = 0;
        }
    }
}

/*
 *find_fit - Find a fit for a block with asize
 */
static void *find_fit(size_t asize){
#ifdef NEXT_FIT 

#else 
    dbg_printf("finding_fit! \n");
    /* First fit search */
    void *bp;
    int list_num = find_list_fit(asize);

    if(list_num != -1){
        while(list_num < NUM_LIST){
            dbg_printf("the list number is %d\n", list_num);
            for (bp = seg_listp[list_num]; (bp != NULL) && ((get_addr(NEXT_FBLKP(bp)) != 0) 
                || ((int)(long)get_addr(PREV_FBLKP(bp)) == list_num));
                bp = get_addr(NEXT_FBLKP(bp))) {
                if (asize <= GET_SIZE(HDRP(bp))) {
                    return bp;
                }
            }
            list_num++;
        }
    }

    dbg_printf("found no fit!\n");
    return NULL; /* No fit */
#endif
}

/* 
 * Find fit list
 * Return -1 if no list is available, 
 * else return the list num, starts from 0
 * */ 
static int find_list_fit (size_t asize) {
   int cur_list = find_list(asize); 

    if (seg_listp[cur_list] != 0) {
        return cur_list;
    }
    else {
        for (int i = cur_list; i < (NUM_LIST-1); i++) {
            cur_list++;
            if (seg_listp[cur_list] != 0){
                return cur_list;
            }
        }
    }
    return -1;
} 

/*
 * Find the segregated list number according to size
 */
static int find_list(size_t asize){
    int num_blocks = asize / (DSIZE);
    int cur_list;

    if (num_blocks <= NUM_LINEAR) {
        cur_list = num_blocks-2;
    }
    else if (num_blocks <= NUM_INF) {
        int tmp = num_blocks;
        cur_list = NUM_LINEAR-1;
        while (!((tmp >= NUM_LINEAR) && (tmp <= (NUM_LINEAR<<1)))){
            cur_list++;
            tmp = tmp>>1;
        }
    }
    else {
        cur_list = NUM_LIST-1;
    }
    
    return cur_list;
}

/*
 * Print the block information
 */
static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize = 0, falloc = 0;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    if (halloc == 0){
        fsize = GET_SIZE(FTRP(bp));
        falloc = GET_ALLOC(FTRP(bp));  
    }

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    if (halloc == 0)
        printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
                (int)hsize, (halloc ? 'a' : 'f'), 
                (int)fsize, (falloc ? 'a' : 'f'));
    else
        printf("%p: header: [%d:%c]\n", bp,
                (int)hsize, (halloc ? 'a' : 'f'));
}

/*
 * The function checks the block correctness
 * 1: Check if the block is aligned to a double word
 * 2: If it is a free block, check if footer equeals header
 * 3: Check if the next block's header contatins the correct information
 */
static void checkblock(void *bp) 
{
    if (aligned(bp) == 0)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET_ALLOC(HDRP(bp)) == 0){
        if (GET(HDRP(bp)) != GET(FTRP(bp)))
            printf("Error: header does not match footer\n");
        if (GET_PREV_ALLOC(HDRP(NEXT_BLKP(bp))) != 0)
            printf("Error: header contain wrong previous block allocation information\n");
    }
    else {
        if (GET_PREV_ALLOC(HDRP(NEXT_BLKP(bp))) != 2)
            printf("Error: header contain wrong previous block allocation information\n");
    }

}

/*
 * Check the free list
 * Check if the free list pointer are correctly aligned and in the heap
 * Check if the list is continuous and has no loop
 * Check if all blocks in each list bucket fall within bucker range
 * Return the number of free blocks in this list if success
 * Return -1 if fail
 */
static int checkfreelist(void *flist, int verbose)
{
    int count = 0; /*count the number of free list*/ 
    signal(SIGALRM, fl_timeout);
    alarm(3);
    char *bp;
    int list = -1;
    if(flist != 0)
        list = (int)(long)get_addr(PREV_FBLKP(flist));
    for(bp = flist; bp!=0; bp = get_addr(NEXT_FBLKP(bp))){
        char *prevfb = get_addr(PREV_FBLKP(bp));
        char *nextfb = get_addr(NEXT_FBLKP(bp));

        if(find_list(GET_SIZE(HDRP(bp))) != list) {
            printf("Error: current size: %d should not be in list: %d\n", GET_SIZE(HDRP(bp)) , list);
        }
        
        if(is_addr(prevfb)){
            if (bp != get_addr(NEXT_FBLKP(prevfb)))
                printf("Error: The next block: %p of the previous block: %p \
                        doesn't match current block: %p\n", get_addr(NEXT_FBLKP(prevfb)),
                        prevfb, bp);

            if(!in_heap(prevfb)){
                printf("Error: previous block %p in the free list is not in heap\n", prevfb);
                return -1;
            }
            if(!aligned(prevfb))
                printf("Error: previous block %p in the free list is not aligned\n", prevfb);
        }

        if(nextfb != 0){
            if (bp != get_addr(PREV_FBLKP(nextfb)))
                printf("Error: The previous block: %p of the next block: %p \
                        doesn't match current block: %p\n", get_addr(PREV_FBLKP(nextfb)), 
                        nextfb, bp);

            if(!in_heap(nextfb)){
                printf("Error: next block %p in the free list is not in heap\n", nextfb);
                return -1;
            }
            if(!aligned(nextfb))
                printf("Error: next block %p in the free list is not aligned\n", nextfb);
        }

        if(verbose == 4){
            printf("current block : %p, previous block: %p, next block %p\n", bp, prevfb, nextfb);
        }
        count++;
    }
    return count;
}
