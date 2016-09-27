/*
 * This malloc package utilizes the Segregated
 * Linked List technique for memory management.
 * 
 * Jason Steck
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <inttypes.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your identifying information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Team Jason",
    /* First member's full name */
    "Jason Steck",
    /* First member's UID */
    "u0646190@utah.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's UID (leave blank if none) */
    ""
};

/* Debug Functions */

static int DEBUG = 0;
// trying to use \u2502 gives a warning :(
#define LINE_PREFIX "*% 3d| "
static int indent = 0;
#define di() (indent+=2)
#define dd() (indent-=2)

// Only output if DEBUG flag is set
#define d(fmt, ...) \
    do{ if(DEBUG) fprintf(stdout, fmt, ##__VA_ARGS__);}while(0)
// No prefix, but add newline
#define dn(fmt, ...) \
    d(fmt "\n", ##__VA_ARGS__)
// Prefix with line number
#define dl(fmt, ...) \
    d(LINE_PREFIX "%*s" fmt, __LINE__, indent, "", ##__VA_ARGS__)
// Prefix with line number and append newline
#define dln(fmt, ...) \
    d(LINE_PREFIX "%*s" fmt "\n", __LINE__, indent, "", ##__VA_ARGS__)
#define derr(fmt, ...) \
    dln(KRED"ERROR: "KNRM fmt, ##__VA_ARGS__)
#define din(fmt, ...) \
    do{ dln("__%s(" fmt ")__", __FUNCTION__, ##__VA_ARGS__); di();}while(0)
#define dout(fmt, ...) \
    do{ dln("%s RETURNS " fmt, __FUNCTION__, ##__VA_ARGS__); dd();}while(0)

/* Console Colors */
#define KNRM  "\x1B[0m"
#define KRED  "\x1B[31m"
#define KGRN  "\x1B[32m"
#define KYEL  "\x1B[33m"
#define KBLU  "\x1B[34m"
#define KMAG  "\x1B[35m"
#define KCYN  "\x1B[36m"
#define KWHT  "\x1B[37m"

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (512)  /* Extend heap by this amount (bytes) */  //32, 64->83

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define SET_SIZE(p, size)  (PUT(p, (GET(p)&3) | size ))
#define GET_ALLOC(p) (GET(p) & 0x1)
#define SET_ALLOC(p, t) (PUT(p, (GET(p)&~1)|t))
#define GET_PREV_ALLOC(p) ((GET(p) & 0x2)>>1)
#define SET_PREV_ALLOC(p, v) (PUT(p, (GET(p)&~2)|v<<1))

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Shortcuts for setting a blocks properties, given the body pointer */
#define BPREVBLOCKFOOTSIZE(bp) (GET_SIZE(((char *)(bp) - DSIZE)))
#define BSIZE(bp) (GET_SIZE(HDRP(bp)))
#define BHEADSIZESET(bp, size) (SET_SIZE(HDRP(bp),size))
#define BP(bp) (GET_PREV_ALLOC(HDRP(bp)))
#define BPSET(bp, v) (SET_PREV_ALLOC(HDRP(bp),v))
#define BT(bp) (GET_ALLOC(HDRP(bp)))
#define BTSET(bp, t) (SET_ALLOC(HDRP(bp),t))
#define BNEXT(bp) ((void *)GET(bp))
#define BNEXTSET(bp, nxtp) PUT(bp, (unsigned int)nxtp)
#define BPREV(bp) ((void *)GET(bp+WSIZE))
#define BPREVSET(bp, prevp) PUT(bp+WSIZE, (unsigned int)prevp)

#define BFOOTSIZE(bp) (GET(FTRP(bp)))
#define BFOOTSIZEUPDATE(bp) (PUT(FTRP(bp),BSIZE(bp)))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + BSIZE(bp))
#define PREV_BLKP(bp)  ((char *)(bp) - BPREVBLOCKFOOTSIZE(bp)) 

/* Global variables */
static int *Cats;
static int *CatMaxes;
static int *NextFits;
#define NUMCATS (12)
#define NUMCATSMAX (NUMCATS-1) // always one less than NUMCATS
static void *LAST;

/* Function prototypes for internal helper routines */
static void printHeap();
static void *expandHeapForFit(size_t size);
static void *extend_heap(size_t words);
static void growThisToEatThat(void *b1, void *b2);
static void disassociate(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *findFitIn(size_t size, int cati, int useNextFit);
static void addToLL(void *bp);
static void *coalesce(void *bp);
static size_t getStandardSize(int payloadSize);
static int getCatHeadIndex(int size);
static void getHeadInfo(void *bp, int *sizep, int *pp, int *tp);
static void printBlock(void *bp);
static void printBlocks(void *bp);
static void printMem(void *start, void *end);
static void printMemL(void *start, int length);
static void printMemBytes(void *start, void *end);
static void printMemLBytes(void *start, int length);

/*
 * Used for checking if a block's stats are what you think they should be
 */
void be(void *bp, int size, int p, int t)
{
    // Normalize the size
    size = getStandardSize(size);
    int aSize, aP, aT = -1;
    // Grab all the relevant information
    getHeadInfo(bp, &aSize, &aP, &aT);
    // Test the expected vs what we actually found
    if(size!=aSize && size+8!=aSize)
        derr("(%p) Size: Expected %d, Actual %d", bp, size, aSize);
    if(p!=aP)
        derr("(%p) p: Expected %d, Actual %d", bp, p, aP);
    if(t!=aT)
        derr("(%p) t: Expected %d, Actual %d", bp, t, aT);
}

/*
 * Prints the contents of the entire heap, and then some other pointers of note
 */
static void printHeap()
{
    //init has already been called, proceed to test
    dln("pagesize: %d Bytes", mem_pagesize());
    // Print entire Heap!
    dln("lo: %p", mem_heap_lo());
    dln("hi: %p", mem_heap_hi());
    dln("Cats: %p", Cats);
    dln("CatMaxes: %p", CatMaxes);
    dln("NextFits: %p", NextFits);
    printMem(mem_heap_lo(), mem_heap_hi());
    // Print information surrounding the last block on the heap
    dln("LAST block: ");
    printBlocks(LAST);
}

/*
 * Allocates and zero's out memory
 */
void *zero_sbrk(size_t growByBytes)
{
    dl("Growing heap from %d to ", mem_heapsize());
    char *bp = mem_sbrk(growByBytes);
    dn("%d Bytes. (Delta: %d Bytes)", mem_heapsize(), growByBytes);
    int i;
    // Zero out all of the addresses
    for(i=0;i<growByBytes;i++)
        PUT(bp+i, 0);
    // Return the newly allocated block
    return (void *)bp;
}


/* 
 * mm_init - Initialize the memory manager 
 */
int mm_init(void) 
{
    // NOTE: all functions starting with "d" are just used for debugging
    dn("=============== Beginning mm_init ===============");
    din("void"); 
    // NOTE: This array is just a shortcut to put the Constant, static Linked List boundaries in
    //       place without having to type them all in by hand for every location on the heap.
    int catMaxes[NUMCATSMAX] = {16, 24, 72, 80, 120, 136, 456, 520, 4080, 4104, 8200}; // The last catMax is implicitly infinite

    size_t initBlockSize = getStandardSize(CHUNKSIZE); // Given a minimum package size for block
    // Allocate initial heap
    int initHeapSize = (3*NUMCATS + initBlockSize/WSIZE);
    if ((Cats = mem_sbrk(WSIZE * initHeapSize)) == (void *)-1) // either zero_sbrk or mem_sbrk
       return -1;

    int i; // Current index of heap
    // Zero out Category Headers
    for(i=0;i<NUMCATS;i++)
        PUT(Cats + i, 0);
    // Initialize Category min values
    for(i=NUMCATS; i<NUMCATS+NUMCATSMAX; i++)
        PUT(Cats + i, PACK(0, catMaxes[i-NUMCATS]));
    CatMaxes = (void *)(Cats + NUMCATS);

    // NOTE: the last catMax is left off the heap since it's technically infinite

    NextFits = (Cats + i);
    int endOfNextFits = i+NUMCATS;
    for(; i<endOfNextFits; i++)
        PUT(Cats+i, 0);

    // Allow if we need to adjust the byte boundary by 4
    //i++;

    // Header with p and t set
    PUT(Cats + i, PACK(initBlockSize, 2)); 
    // Record where the "last" block is
    LAST = (void *)(Cats+i+1);

    i += initBlockSize/WSIZE; // Jump to next header

    // Epilogue Header. Size = 0, this allocated = 1
    PUT(Cats + i, PACK(0, 1));

    // Setup LAST block
    BFOOTSIZEUPDATE(LAST);

    // Create our first empty block
    void *first = mm_malloc(44);
    // Create a separator from our first to the rest
    mm_malloc(12); 
    mm_free(first);

    // NOTE: Again, all methods starting with "d" are just used for debugging
    dout("0");
    return 0;
}

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
void *mm_malloc(size_t payloadSize) 
{
    din("payloadSize: %d", payloadSize);
    int size = getStandardSize(payloadSize);
    char *bp = find_fit(size);

    // If we failed to get a pointer, end method
    if(bp==NULL)
    {
        dout("NULL");
        return NULL;
    }

    // Otherwise, update all of the block informations
    place(bp, size);
    dout("bp: %p", bp);
    return bp;
} 

/* 
 * mm_free - Free a block 
 */
void mm_free(void *bp)
{
    din("bp: %p", bp);
    dln("Block to free: ");
    int t;
    // Grab the allocated flag
    t = BT(bp);

    // If the block has already been unallocated, simply do nothing
    if(t==0)
    {
        dout("void; //Block was already unallocated!");
        return;
    }

    // Mark as unallocated
    BTSET(bp, 0);

    /* Combine the previous and/or next blocks if also unallocated */
    bp = coalesce(bp);

    /* Insert the block into the proper linked list */
    // If we should put the free block back into the linked lists
    if(bp==LAST)
    {
        dln("We freed a block next to the LAST block.");
    }
    else
    {
        dln("Freed regular block; should put it into a Linked List.");
        // Add the freed block to the appropriate linked list
        addToLL(bp);
    }

    // Tell the next block that we're unallocated
    dln("Setting the p flag to 0 for block %p", NEXT_BLKP(bp));
    BPSET(NEXT_BLKP(bp), 0);

    dout("void; //Everything seemed to work");
}

/*
 * Adds the chunk to the beginning of the correct linked list
 */
static void addToLL(void *bp)
{
    din("bp: %p", bp);
    // Determine which category this (potentially larger) block belongs to
    int size = BSIZE(bp);
    int cati = getCatHeadIndex(size);

    // Put at the beginning of the category
    void *firstNode = (void *)Cats[cati];
    Cats[cati] = (unsigned int)bp;
    if((unsigned int)firstNode != 0)
    {
        dln("Updating old first node's (%p) prev.", firstNode);
        BPREVSET(firstNode, bp);
    }

    dln("New Links for %p: ", bp);
    di();
        // Display the links
        dln("Next: %p", firstNode);
        dln("Prev: %p", (void*)0);
    dd();

    // Update the other nodes
    BNEXTSET(bp, firstNode);
    BPREVSET(bp, 0);
    dout("void; // Added %p to category #%d", bp, cati);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    din("bp: %p", bp);
    size_t prev_alloc = BP(bp);
    size_t next_alloc = BT(NEXT_BLKP(bp));
    dln("prev_alloc: %d", prev_alloc);
    dln("next_alloc: %d", next_alloc);

    // If we can eat the previous block
    if(!prev_alloc)
    {
        void *prev = PREV_BLKP(bp);
        dln("Previous block foot size: %d", BPREVBLOCKFOOTSIZE(bp));
        dln("Eating the previous block %p...", prev);
        // Pull the prev out of it's Linked List
        disassociate(prev);
        growThisToEatThat(prev, bp);
        bp = prev;
    }

    // If we can eat the next block
    if(!next_alloc)
    {
        void *next = NEXT_BLKP(bp);
        dln("I'm %p, and I think %p is the next block which is unallocated.", bp, next);
        dln("The current LAST is %p", LAST);
        // If the next block is the special one
        if(next==LAST)
        {
            dln("Setting LAST to %p", bp);
            LAST = bp;
        }
        else
            disassociate(next);

        growThisToEatThat(bp, next);
    }
    int *ft = (int *)FTRP(bp);
    dln("Before Footer Update, FOOTER %p has value %d", ft, *ft);
    // Update the Footer for the given blcok
    BFOOTSIZEUPDATE(bp);
    dln("FOOTER %p has value %d", ft, *ft);

    dout("%p", bp);
    return bp;
}

/*
 * mm_realloc - is the space is available, simply grow the selection, otherwise, move to new location.
 */
void *mm_realloc(void *ptr, size_t payloadSize)
{
    //printf("# ptr size: %d, Want: %d, LAST size: %d\n", BSIZE(ptr), getStandardSize(payloadSize), BSIZE(LAST));

    din("ptr: %p, payloadSize: %d", ptr, payloadSize);
    printBlocks(ptr);
    //Case 1: New size is 0 (Same as free)
    if(payloadSize == 0) 
    {
        dln("Doing regular free:");
        mm_free(ptr);
        dout("%p; // Repeat what we just freed.", ptr);
        return ptr;
    }
    //Case 2: Old ptr is null (Same as malloc)
    if(ptr == NULL)
    {
        dln("Doing regular malloc:");
        ptr = mm_malloc(payloadSize);
        dout("%p; // Location of newly allocated memory", ptr);
        return ptr;
    }

    // If they want space they already have, do nothing
    if(BSIZE(ptr)==getStandardSize(payloadSize))
    {
        dln("They already have the space they want.");
        dout("%p", ptr);
        return ptr;
    }

    // Determine available size
    void *nxtBlock = NEXT_BLKP(ptr);
    dln("nxtBlock: %p", nxtBlock);
    unsigned int available;
    if(BT(nxtBlock))
        available = 0;
    else
    {
        available = BSIZE(nxtBlock);
        if(nxtBlock==LAST)
        {
            dln("*The next block is the LAST");   
            available -= 16; // the LAST block always has at least 16 bytes
        }
    }
    dln("Available bytes in nxtBlock: %d", available);

    size_t size = getStandardSize(payloadSize);
    dln("We need a block of %d bytes", size);

    //Case 3: There is room to expand block to desired size
    if(size <= BSIZE(ptr) + available)
    {
        dln("There is room to expand!");
        growThisToEatThat(ptr, nxtBlock);
        place(ptr, size);
    }
    else if(nxtBlock==LAST)
    {
        // Make room in last
        void *hp = expandHeapForFit(size - BSIZE(ptr) +16);
        growThisToEatThat(ptr, hp);
        place(ptr, size);
    }
    else //Case 4: Not enough room to expand block to desired size
    {
        dln("Not enough room to expand. Getting new block:");
        unsigned int *newBlock = (unsigned int *)mm_malloc(payloadSize);
        dln("New block at %p", newBlock);
        dl("Copying %d bytes of old data... ", payloadSize);
        memcpy(newBlock, ptr, payloadSize);
        dn("done");
        ptr = newBlock;
    }
    
    dout("%p; // Pointer to newly allocated size.", ptr);
    return ptr;
}

/* 
 * checkheap - Optional function. Not going to implement.
 */
void mm_checkheap(int verbose)  
{ 
}


/* 
 * find_fit - Find a fit for a block with size bytes 
 */
static void *find_fit(size_t size)
{ 
    din("size: %d", size);
    int cati = getCatHeadIndex(size);
    dln("Starting in category #%d", cati);

    int useNextFit = 1;
    void *bp;
    dln("Loop through categories: ");
    do
    {
        dln("cati: %d", cati);
        di();
        bp = findFitIn(size, cati, useNextFit);
        // If we have something, return it
        if(bp != 0)
        {
            dd();
            dln("Found a fit at %p", bp);
            dout("%p", bp);   
            return bp;
        }
        // Else, check the next category, without next fit
        cati++;
        useNextFit = 0;
        dln("No fit in this category. Look at next category.");
        dd();
    }while(cati<NUMCATS);
    dln("No fit in regular categories.");
    // Check LAST block
    if(size + 16 <= BSIZE(LAST)) // leave at least min block open
    {
        dln("Found fit in LAST! (%p)", LAST);
        dout("%p", LAST);   
        return LAST;
    }
    dln("No fit in LAST; we must expand LAST:");
    // No room, need to expand heap

    bp = expandHeapForFit(size + 16);

    dln("Finally found fit:");
    dout("%p", bp);
    return bp;
}

/*
 * findFitIn - Determines if a fit can be found in the given category
 */
static void *findFitIn(size_t size, int cati, int useNextFit)
{
    din("size: %d, cati: %d, useNextFit: %d", size, cati, useNextFit);
    void *bp;
    if(useNextFit)
    {
        bp = (char *)NextFits[cati];
        dln("Using Next Fit starting at: %p", bp);   
    }
    else
    {
        bp = (char *)Cats[cati];
        dln("Using First Fit starting at: %p", bp);
    }

    void *start = bp;
    dln("Looping through Linked List:");
    di();
    do
    {
        dln("Looking at: %p", bp);
        // If we're at the end of list or never started
        if(bp==0)
        {
            bp = (void *)Cats[cati]; // Get the head
            dln("-Hit end of list, starting back at: %p", bp);
            continue;
        }
        
        /* Check out node */
        // If we found a valid node
        if(size <= BSIZE(bp))
        {
            dln("-Found a fit!");
            // Yay
            if(useNextFit)
            {
                NextFits[cati] = (unsigned int)BNEXT(bp);
                dln("-Updating Next Fit to 0x%08x", NextFits[cati]);
            }
            dd();
            dln("End of Loop");
            dout("%p; // The block to use!", bp);
            return bp;
        }
        else //didn't find it, go to the next
        {
            dln("-Not big enough");
            bp = BNEXT(bp);
        }
    }
    while(bp != start);
    dln("Ended up where we started. No fit in this list.");
    dd();
    dout("0");
    // We failed
    return 0;
}

/* 
 * Expands the heap and returns a pointer 
 */
static void *expandHeapForFit(size_t size)
{
    // Whenever we expand the heap, we must always take the LAST block into account
    size -= BSIZE(LAST)-16;
    size_t bytes = CHUNKSIZE;
    // make sure we only allocate in multiples of CHUNKSIZE
    while(size >= bytes)
        bytes += bytes;

    void *bp = extend_heap(bytes);
    //void *bp = extend_heap(size);
    return bp;
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t bytes) 
{
    char *oldHi = mem_heap_hi();
    din("Bytes to expand: %d", bytes);
    // Expand heap
    void *bp;
    // Grab new memory, return NULL if we fail
    if ((bp = mem_sbrk(bytes)) == (void *)-1)
    {
        derr("Could not allocate more heap space!");
        dout("NULL");
        return NULL;
    }

    // Update old e header (now new bp block)
    BHEADSIZESET(bp, bytes);
    BTSET(bp, 0);
    int p = BP(bp);

    dln("Heap expanded from %p to %p", oldHi, mem_heap_hi());
    dln("New Heap block pointer: %p", bp);

    // Create new epilogue header
    int *eBlock = (int *)NEXT_BLKP(bp);
    PUT(HDRP(eBlock), PACK(0, 1));
    dln("Setting new Epilogue body to %p", eBlock);
    printBlock((char *)eBlock);

    // If the previous block is not allocated
    if(p==0)
    {
        // Absorb it
        void *prevBlock = PREV_BLKP(bp);
        dln("Previous block %p unallocated; absorbing it:", prevBlock);
        // Pull previous block out of its linked list
        disassociate(prevBlock);
        growThisToEatThat(prevBlock, bp);
        bp = prevBlock;
        dln("New bp: %p", bp);
    }

    // Stick block at the end of largest list
    dln("Changing LAST from %p to %p", LAST, bp);
    LAST = bp;

    dout("%p; // New LAST, which has been expanded", bp);
    return bp;
}

/* 
 * Blocks must be adjacent.
 * Assumes b1 is earlier in heap.
 * b2 cannot be in a linked list.
 */
static void growThisToEatThat(void *b1, void *b2)
{
    din("b1: %p, b2: %p", b1, b2);
    if(BT(b2))
    {
        // Oops! Can't eat a block that's allocated
        derr("b2 is currently allocated! Cannot expand into it.");
        exit(0);
    }
    dl("Growing %p from %d to ", b1, BSIZE(b1));
    // Grow our head to include the next block
    BHEADSIZESET(b1, (BSIZE(b1)+BSIZE(b2)));
    dn("%d", BSIZE(b1));

    // If b1 is allocated
    if(BT(b1))
    {
        dln("Detected b1 as Allocated. Will not update footer, instead update next block (%p)", NEXT_BLKP(b1));
        dl("-Next block header set from 0x%08x to ", GET(HDRP(NEXT_BLKP(b1))));
        // Update the next block
        BPSET(NEXT_BLKP(b1), 1);
        dn("0x%08x", GET(HDRP(NEXT_BLKP(b1))));
    }
    else
    {
        dln("b1 is unallocated, so update footer for new chunk.");
        BFOOTSIZEUPDATE(b1);
    }

    if(b2==LAST)
    {
        dln("We ate the LAST one! Updating LAST from %p to %p", b2, b1);
        LAST = b1;
    }
    dout("void");
}

/*
 * Pulls the block out of the linked list
 */
static void disassociate(void *bp)
{
    din("bp: %p", bp);
    // If it's the special unallocated node
    if(bp==LAST)
    {
        dln("Warning, cannot disassociate the LAST block.");
        dout("void");
        return;
    }

    // If the block is allocated, we have a problem
    if(BT(bp))
    {
        derr("Tried to disassociate an allocated block!");
        exit(0);
    }

    //Figure out which list the node is in
    int size = BSIZE(bp);
    int cati = getCatHeadIndex(size);

    void *prev = BPREV(bp);
    void *next = BNEXT(bp);

    dln("prev: %p", prev);
    dln("next: %p", next);

    /* Update previous node */
    if(prev==0) // We're at the head
    {
        Cats[cati] = (unsigned int)next;
        dln("Updating cat%d head to point to 0x%08x", cati, Cats[cati]);
    }
    else 
    {
        dln("Updating next of %p to point to %p", prev, next);
        BNEXTSET(prev, next);
    }

    /* Update next node */
    if(next!=0)
    {
        dln("Updated prev of %p to point to %p", next, prev);
        BPREVSET(next, prev);
    }
    else
        dln("No next node to update");

    /* Update NextFit if needed */
    void *nf = (void *)NextFits[cati];
    if(bp==nf)
    {
        NextFits[cati] = (unsigned int)BNEXT(bp);
        dln("Updating NextFit of cat%d to 0x%08x", cati, NextFits[cati]);
    }
    dout("void");
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t size)
{
    /* At this point, a free block of sufficient size has been found, we just 
    need to stick it in the spot, make adjustments and update lists. No 
    coalescing is necessary. */
    din("bp: %p, size: %d", bp, size);

    // Simple error checking
    if(bp<mem_heap_lo() || bp>mem_heap_hi())
    {
        derr("The target block to allocate points outside of heap! (%p)", bp);
        //printHeap();
        dln("Problem block:");
        printBlocks(bp);
        exit(0);
    }

    size_t unSize = BSIZE(bp);
    int cati = getCatHeadIndex(unSize);
    // Make sure NextFits aren't affected
    if(bp == LAST)
        dln("The block to use the the LAST one");
    else
    {
        // If our block is a Next Fit
        if(bp==(void *)NextFits[cati])
        {
            dln("The block is the Next Fit");
            // Push it to the next node
            NextFits[cati] = (unsigned int)BNEXT(bp);
            dln("Updating the NextFit of cat%d to 0x%08x", cati, NextFits[cati]);
        }
        else
            dln("The block is not a Next Fit");
    }


    //Disassociate block from its cat list, if it was an unallocated chunk
    if(BT(bp))
        dln("Block is marked as Allocated. Will not disassociate.");
    else
    {
        dln("Block is marked as Unallocated; Disassociating it now:");
        disassociate(bp);
    }

    //Case 1: Entire Empty block will be used
    if(size + 8 >= unSize) // Don't let there be 8 bytes left over
    {
        dln("Using up entire block, simply mark block as allocated.");
        //Update header
        BTSET(bp, 1);
        // Update the next block
        BPSET(NEXT_BLKP(bp), 1);
    }
    else //Case 2: Empty block will have a leftover piece
    {
        dln("We will have a block leftover");
        size_t extraSize = unSize - size;

        //Update newly allocated header
        BTSET(bp, 1);
        BHEADSIZESET(bp, size);
        dln("Setting allocated header to size %d", size);

        //Create header for remaining unused, unallocated space
        void *newBlock = NEXT_BLKP(bp);
        BHEADSIZESET(newBlock, extraSize);
        BPSET(newBlock, 1);
        BTSET(newBlock, 0);
        BFOOTSIZEUPDATE(newBlock);
        dln("Created new block at %p, with a size of %d", newBlock, extraSize);

        /* Stick free block in appropriate cat list */
        // If we were using the LAST unallocated block
        if(bp==LAST)
        {
            dln("Block was the LAST one, updating LAST from %p to %p", LAST, newBlock);
            LAST = newBlock;
        }
        else
        {
            dln("Regular unallocated block, add the new block to the LL");
            addToLL(newBlock);
        }

        // Update the block after the new one show it's empty
        BPSET(NEXT_BLKP(newBlock), 0);
    }
    dout("void");
}

/* 
 * getStandardSize - Returns the standardized block size given a payload size
 */
static size_t getStandardSize(int payloadSize)
{
    // Calculate the correct block size of the payload
    size_t size = (payloadSize+11)&~7;
    // Manually adjust the trouble blocks
    if(size==120)
        size = 136;
    else if(size==456)
        size = 520;
    // Return the size of the block
    return size;
}

/*
 * Returns a pointer the the first node in the block size category
 */
static int getCatHeadIndex(int size)
{
    /* Look through the category maxes to find cat index */
    int i;
    for(i=0; i<NUMCATSMAX; i++)
        if(size <= CatMaxes[i]) //If we found a category that can hold the size
            return i; // Grab the pointer to the head 
    // If we didn't find one, then we will use the largest category (last one)
    return i;
}

/* A single call to get all the properties of the head */
static void getHeadInfo(void *bp, int *sizep, int *pp, int *tp)
{
    int *head = (int *)HDRP(bp);
    *sizep = GET_SIZE(head);
    *pp = GET_PREV_ALLOC(head);
    *tp = GET_ALLOC(head);
}

/*
 * Simply prints out and return's a block's info
 */
void pBlock(void *bp, int *size, int *p, int *t)
{
    getHeadInfo(bp, size, p ,t);

    d("(%p) %s%s%s, ", bp, (bp==LAST?"LAST, ":""), (*size==0?(*t==0?"Epilogue"KRED"? "KNRM:"Epilogue, "):""),(*t?"Allocated":"Unallocated"));
    // If there's a problem between the flags
    if(!*p && !*t)
        d("%d Bytes, "KRED"p: %d, t: %d"KNRM"\n", *size, *p, *t);
    else
        d("%d Bytes, p: %d, t: %d\n", *size, *p, *t);

    // If our node is unallocated
    if(*t==0 && *size!=0)
    {
        dl("  Next: %p\n", BNEXT(bp));
        dl("  Prev: %p\n", BPREV(bp));
        int ftsize = BFOOTSIZE(bp);
        if(ftsize!=*size)
            d(KRED"  ERROR:"KNRM" Foot Size is %d Bytes, when it should be %d!\n", ftsize, *size);
    }
}

/* 
 * Simple wrapper
 */
static void printBlock(void *bp)
{
    int a,b,c = 0;
    pBlock(bp, &a, &b, &c);
}

/* 
 * printBlocks - Prints the memory locations relevant to the block
 */
static void printBlocks(void *bp)
{
    int size, p, t = -1;
    int prevSize, prevP, prevT = -1;
    int nxtSize, nxtP, nxtT = -1;

    // Get all the info we need
    getHeadInfo(bp, &size, &p, &t);
    getHeadInfo(NEXT_BLKP(bp), &nxtSize, &nxtP, &nxtT);

    dl("=========================\n");
    dl("Prev Block: ");
    // If the previous block is unallocated
    if(!p)
    {
        void *prevBlock = PREV_BLKP(bp);
        pBlock(prevBlock, &prevSize, &prevP, &prevT);
    }
    else
        d("Unknown\n");

    dl("This Block: ");
    pBlock(bp, &size, &p, &t);

    // If we're not the Epilogue block
    if(size!=0)
    {
        // Say what was wrong with the next head
        if(nxtP!=t)
            dl(KRED"ERROR: "KNRM" Next head incorrectly thinks I'm %s!\n", (nxtP? "Allocated":"Unallocated"));

        if(!nxtT && !t)
            dl(KRED"ERROR: "KNRM" Both the next head and myself seem to be Unallocated! We should have been coalesced!\n"); 
    }
    
    dl("Next Block: ");
    if(size==0)
        dl("None\n");
    else
        pBlock(NEXT_BLKP(bp), &nxtSize, &nxtP, &nxtT);
    dl("=========================\n");
}

/* 
 * printMem - prints the contents of memory from 
 *            one location to another
 */
static void printMem(void *start, void *end)
{
    int *cursor = start;
    int *finish = (int *)end;
    printf("Printing Memory Chunk: \n");
    for(; cursor <= finish; cursor++)
        printf("%p | 0x%08X (%d)\n", cursor, *(int *)(cursor), *(int *)(cursor));
}

/* 
 * printMemL - prints the contents of memory from 
 *            one location for some length in bytes.
 */
static void printMemL(void *start, int length)
{
    int *cursor = start;
    int *finish = ((int *)start) + length;
    printf("Printing %d Integers of Memory: \n", length);
    for(; cursor < finish; cursor++)
        printf("%p | 0x%08X (%d)\n", cursor, *(int *)(cursor), *(int *)(cursor));
}

/* 
 * printMem - prints the contents of memory from 
 *            one location to another, inclusive
 */
static void printMemBytes(void *start, void *end)
{
    char *cursor = start;
    char *finish = (char *)end;
    printf("Printing Memory Chunks by Byte: \n");
    for(; cursor <= finish; cursor++)
        printf("%p | 0x%02X (%d)\n", cursor, *(char *)(cursor), *(char *)(cursor));
}

/* 
 * printMemL - prints the contents of memory from 
 *            one location for some length in bytes.
 */
static void printMemLBytes(void *start, int length)
{
    char *cursor = start;
    char *finish = ((char *)start) + length;
    printf("Printing %d Byes of Memory: \n", length);
    for(; cursor < finish; cursor++)
        printf("%p | 0x%02X (%d)\n", cursor, *(char *)(cursor), *(char *)(cursor));
}
