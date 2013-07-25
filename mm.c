/*
 * mm.c
 * 
 * Name: RedElephant Andrew Id: shiweid
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
/*#define DEBUG*/
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* Configuration macros*/ 
/*#define NEXT_FIT  [>policy<] */
#define LIFO

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
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */ 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp

/* Given free block ptr bp, compute address or address pointer of the
 * next and previous blocks */ 
#define NEXT_FBLKP(bp)  ((char*)(bp)) 
#define PREV_FBLKP(bp)  ((char*)(bp + WSIZE))

/* To store or get a double word size address in a wsize space*/ 
static inline void put_addr(void *bp, void *value) {
    if((size_t*)value != 0) /* Truncate the value into wsize(8 bytes)*/ 
        *(unsigned int*)bp = (unsigned int)(size_t)value;
    else
        *(unsigned int*)bp = 0;
}

static inline void *get_addr(void *bp) {
    if(*(unsigned int*)bp != 0)
        return (void *)(((unsigned long long)0x8<<32) | *(unsigned int*)bp);
    else
        return (void *)0;
}

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */ 
static char *fb_listp;  /* Pointer to the free block list for explicit list*/
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/*Function prototypes for internal help routines*/
static void *extend_heap(size_t words);
static void *coalesce(void* bp);
static void place(void* bp, size_t asize);
static void *find_fit(size_t asize);
static void printblock(void* bp);
static void checkblock(void* bp);
static int checkfreelist(void *flist, int verbose);

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
    
    if ((fb_listp = mem_sbrk(2*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    fb_listp = 0;

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);                     //line:vm:mm:endinit  

#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;

    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    dbg_printf("starting malloc\n");
    if (heap_listp == 0){
        mm_init();
    }

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                     
        asize = 2*DSIZE;                  
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

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
 * free
 */
void free (void *ptr) {
    dbg_printf("starting free %p\n", ptr);

    if(ptr == 0) 
        return;

    size_t size = GET_SIZE(HDRP(ptr));

    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    put_addr(PREV_FBLKP(ptr), 0);
    put_addr(NEXT_FBLKP(ptr), fb_listp);
    if(fb_listp != 0)
        put_addr(PREV_FBLKP(fb_listp), ptr);
    fb_listp = ptr;

    coalesce(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
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
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
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
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
    char *bp = heap_listp;

    if (verbose == 3)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose == 3) 
            printblock(bp);
        checkblock(bp);
    }

    checkfreelist(fb_listp, verbose);

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
    PUT(HDRP(bp), PACK(size, 0)); /*Free block header*/ 
    PUT(FTRP(bp), PACK(size, 0)); /*Free block Footer*/ 
#ifdef LIFO 
    /*Initialize the free block list*/ 
    if(fb_listp == 0) {
        put_addr(NEXT_FBLKP(bp), 0);
        put_addr(PREV_FBLKP(bp), 0);
        fb_listp = bp;
        dbg_printf("Initialized the free block list\n");
    }
    else {
    /*Modify the free block list*/ 
        char *old = fb_listp;
        fb_listp = bp;
        put_addr(PREV_FBLKP(fb_listp), 0);
        put_addr(NEXT_FBLKP(fb_listp), old);
        put_addr(PREV_FBLKP(old), fb_listp);
    }
#endif
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /*The new epilogue block*/ 

    /*Coalasce if the previous block is free*/ 
    return coalesce(bp);
}

static void* coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    char *old_nextp, *old_prevp;

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        dbg_printf("coalasce case 2\n");
        char *oldnext_blkp = NEXT_BLKP(bp);
        old_nextp = get_addr(NEXT_FBLKP(oldnext_blkp));
        old_prevp = get_addr(PREV_FBLKP(oldnext_blkp));

        size += GET_SIZE(HDRP(oldnext_blkp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        
        put_addr(NEXT_FBLKP(old_prevp), old_nextp);
        if(old_nextp != 0)
            put_addr(PREV_FBLKP(old_nextp), old_prevp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        dbg_printf("coalasce case 3\n");
        char *old_blkp = fb_listp;
        char *oldprev_blkp = PREV_BLKP(bp);
        old_nextp = get_addr(NEXT_FBLKP(oldprev_blkp));
        old_prevp = get_addr(PREV_FBLKP(oldprev_blkp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
      
        fb_listp = bp;

        put_addr(NEXT_FBLKP(old_prevp), old_nextp);
        if(old_nextp != 0)
            put_addr(PREV_FBLKP(old_nextp), old_prevp);

        put_addr(NEXT_FBLKP(fb_listp), get_addr(NEXT_FBLKP(old_blkp)));
        if(get_addr(NEXT_FBLKP(fb_listp)) != 0)
            put_addr(PREV_FBLKP(get_addr(NEXT_FBLKP(fb_listp))), fb_listp);
        put_addr(PREV_FBLKP(fb_listp), 0);

        
        /*[> The coalesced block are adjacent<] 
        if(get_addr(NEXT_FBLKP(fb_listp)) == fb_listp)
            put_addr(NEXT_FBLKP(fb_listp), old_nextp);
        put_addr(PREV_FBLKP(fb_listp), 0);*/
    }

    else {                                     /* Case 4 */
        dbg_printf("coalasce case 4\n");
        char *old_blkp = fb_listp;
        char *oldprev_blkp = PREV_BLKP(bp);
        char *oldnext_blkp = NEXT_BLKP(bp);

        size += GET_SIZE(HDRP(oldprev_blkp)) + 
            GET_SIZE(FTRP(oldnext_blkp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        fb_listp = bp;
        old_nextp = get_addr(NEXT_FBLKP(oldprev_blkp));
        old_prevp = get_addr(PREV_FBLKP(oldprev_blkp));
        put_addr(NEXT_FBLKP(old_prevp), old_nextp);
        if(old_nextp != 0)
            put_addr(PREV_FBLKP(old_nextp), old_prevp);

        put_addr(NEXT_FBLKP(fb_listp), get_addr(NEXT_FBLKP(old_blkp)));
        if(get_addr(NEXT_FBLKP(fb_listp)) != 0)
            put_addr(PREV_FBLKP(get_addr(NEXT_FBLKP(fb_listp))), fb_listp);
        put_addr(PREV_FBLKP(fb_listp), 0);
        
        /*if(get_addr(NEXT_FBLKP(fb_listp)) == fb_listp)
            put_addr(NEXT_FBLKP(fb_listp), old_nextp);
        put_addr(PREV_FBLKP(fb_listp), 0);*/
        
        old_nextp = get_addr(NEXT_FBLKP(oldnext_blkp));
        old_prevp = get_addr(PREV_FBLKP(oldnext_blkp));
        put_addr(NEXT_FBLKP(old_prevp), old_nextp);
        if(old_nextp != 0)
            put_addr(PREV_FBLKP(old_nextp), old_prevp);

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
    char *old = bp;
    void *old_nextp = get_addr(NEXT_FBLKP(old));
    void *old_prevp = get_addr(PREV_FBLKP(old));

    if((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);

        /*Initialize the new free block*/ 
        put_addr(NEXT_FBLKP(bp), old_nextp);
        put_addr(PREV_FBLKP(bp), old_prevp);

        if(old_prevp != 0) 
            put_addr(NEXT_FBLKP(old_prevp), bp);
        else /*The free block is at the beginning of free list*/ 
            fb_listp = bp;

        if(old_nextp != 0)
            put_addr(PREV_FBLKP(old_nextp), bp);

        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0)); 
    }
    else { /*The remainder is less than 2 double words, thus no split*/ 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));

        dbg_printf("remainder less than 2 double words\n");
        if(old_prevp != 0) 
            put_addr(NEXT_FBLKP(old_prevp), old_nextp);
        else /*The free block is at the beginning of free list*/ 
            fb_listp = old_nextp;
        dbg_printf("old_nextp: %p\n", old_nextp);
        dbg_printf("old_prevp: %p\n", old_prevp);
        if(old_nextp != 0)
            put_addr(PREV_FBLKP(old_nextp), old_prevp);
    }
}

/*
 *find_fit - Find a fit for a block with asize
 */
static void *find_fit(size_t asize){
#ifdef NEXT_FIT 
    /* Next fit search */
    char *oldrover = rover;

    /* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL;  /* no fit found */
#else 
    /* First fit search */
    void *bp;
/*may have problem */ 
    for (bp = fb_listp; (bp!=NULL) && ((get_addr(NEXT_FBLKP(bp)) != 0) 
    || (get_addr(PREV_FBLKP(bp)) == 0)); bp = get_addr(NEXT_FBLKP(bp))) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    }
    return NULL; /* No fit */
#endif
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
    (int)hsize, (halloc ? 'a' : 'f'), 
    (int)fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp) 
{
    if (aligned(bp) == 0)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

static int checkfreelist(void *flist, int verbose)
{
    signal(SIGALRM, fl_timeout);
    alarm(3);
    char *bp;
    for(bp = flist; bp!=0 && ((get_addr(NEXT_FBLKP(bp)) != 0) || (get_addr(PREV_FBLKP(bp)) == 0));
    bp = get_addr(NEXT_FBLKP(bp))){
        char *prevfb = get_addr(PREV_FBLKP(bp));
        char *nextfb = get_addr(NEXT_FBLKP(bp));

        if( prevfb != 0){
            if(!in_heap(prevfb)){
                printf("Error: previous block %p in the free list is not in heap\n", prevfb);
                return -1;
            }
            if(!aligned(prevfb))
                printf("Error: previous block %p in the free list is not aligned\n", prevfb);
        }

        if(nextfb != 0){
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
    }
    return 1;
}
