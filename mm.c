/*
ICS lab4 malloc
Author: wei luo@Fudan University
Date: 06/20/2011
*/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"


#define WSIZE 			4
#define DSIZE 			8
#define TSIZE			12
#define FSIZE			16
#define CHUNKSIZE	 	(1<<12)
#define OVERHEAD 		24
#define MAXNUM			(1<<30)

#define MAX(x, y) 		( (x) > (y) ? (x) : (y) )

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) 	((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) 				(*(size_t *)(p))
#define PUT(p, val) 		(*(size_t *)(p) = (val));

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) 		(GET(p) & ~0x7)
#define GET_ALLOC(p) 		(GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) 		((char *)(bp) - TSIZE - DSIZE)
#define FTRP(bp) 		((char *)(bp) + GET_SIZE(HDRP(bp)) - FSIZE - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)		((char *)(bp) + GET_SIZE(((char *)(bp) - TSIZE - DSIZE)))
#define PREV_BLKP(bp) 		((char *)(bp) - GET_SIZE(((char *)(bp) - FSIZE - DSIZE)))

/* Next and previous free block */
#define NEXT_FBLK(bp)		((char *)(bp) - WSIZE - DSIZE)
#define PREV_FBLK(bp)		((char *)(bp) - DSIZE - DSIZE)

/* Given block bp, compute where previous and next block with same size stores */
#define SAME_PREV(bp)		((char *)(bp) - DSIZE)
#define SAME_NEXT(bp)		((char *)(bp) - WSIZE)

/* Always points to the prologue block */
static char *heap_listp;


/* Start and end of free block list */
static size_t *startp;
static size_t *endp;


/* Static functions */
static int power_of_two(size_t size);
static int id(size_t size);
static void delete_node(void *bp);
static void *get_same(void *bp);
static void insert_node(void *bp);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static int mm_check(void);


/* Functions */
int mm_init(void);
void mm_free(void *);
void *mm_malloc(size_t size);
void *mm_realloc(void *bp, size_t size);




static int power_of_two(size_t size) {
	int result = 0;
	while (size >> 1) {
		size >>= 1;
		result ++;
	}
	return result;
}


static int id(size_t size) {
	if (size <= 4095)
		return power_of_two(size);
	else if (size <= 32767)
			return (11 + size / 4096);
		else if (size <= 524287)
				return (5 + power_of_two(size));
		else
			return 24;
}


static void delete_node(void *bp) {
	if (GET(SAME_PREV(bp))) {
		PUT(SAME_NEXT(GET(SAME_PREV(bp))), GET(SAME_NEXT(bp)));
		if (GET(SAME_NEXT(bp)))
			PUT(SAME_PREV(GET(SAME_NEXT(bp))), GET(SAME_PREV(bp)));
	}
	else {
		if(GET(SAME_NEXT(bp))) {
			PUT(NEXT_FBLK(GET(PREV_FBLK(bp))), GET(SAME_NEXT(bp)));
			PUT(PREV_FBLK(GET(SAME_NEXT(bp))), GET(PREV_FBLK(bp)));
			PUT(PREV_FBLK(GET(NEXT_FBLK(bp))), GET(SAME_NEXT(bp)));
			PUT(NEXT_FBLK(GET(SAME_NEXT(bp))), GET(NEXT_FBLK(bp)));
			PUT(SAME_PREV(GET(SAME_NEXT(bp))), 0);
		}
		else {
			PUT(NEXT_FBLK(GET(PREV_FBLK(bp))), GET(NEXT_FBLK(bp)));
			PUT(PREV_FBLK(GET(NEXT_FBLK(bp))), GET(PREV_FBLK(bp)));
		}
	}
}

static void *get_same(void *bp) {
	size_t size = GET_SIZE(HDRP(bp));
	size_t *q = startp + id(size);
	size_t *p;
	for (p = (size_t *)GET(NEXT_FBLK(q)); GET_SIZE(HDRP(p)) > OVERHEAD; p = (size_t *)GET(NEXT_FBLK(p))){
		if( GET_SIZE(HDRP(p)) == size) {
			PUT(SAME_NEXT(bp), GET(SAME_NEXT(p)));
			if(GET(SAME_NEXT(bp)))
				PUT(SAME_PREV(GET(SAME_NEXT(bp))), (size_t)bp);
			PUT(SAME_NEXT(p), (size_t)bp);
			PUT(SAME_PREV(bp), (size_t)p);
			return p;
		}
	}
	return NULL;
}

static void insert_node(void *bp) {
	if (get_same(bp) != NULL)
		return;
	size_t *p = startp + id(GET_SIZE(HDRP(bp)));
	PUT(NEXT_FBLK(bp), (size_t)GET(NEXT_FBLK(p)));
	PUT(PREV_FBLK(GET(NEXT_FBLK(p))), (size_t)bp);
	PUT(NEXT_FBLK(p), (size_t)bp);
	PUT(PREV_FBLK(bp), (size_t)p);
	PUT(SAME_NEXT(bp), 0);
	PUT(SAME_PREV(bp), 0);
}


static void *coalesce(void *bp) {
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {
		insert_node(bp);
		return bp;
	}

	else if (prev_alloc && !next_alloc) {
		delete_node(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		insert_node(bp);
		return (bp);
	}

	else if (!prev_alloc && next_alloc) {
		delete_node(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		insert_node(PREV_BLKP(bp));
		return (PREV_BLKP(bp));
	}

	else {
		delete_node(PREV_BLKP(bp));
		delete_node(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
			GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		insert_node(PREV_BLKP(bp));
		return (PREV_BLKP(bp));
	}
}


static void *extend_heap(size_t words) {

	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((int)(bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));			/* free block header */
	PUT(FTRP(bp), PACK(size, 0));			/* free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));	/* new epilogue header */

	return coalesce(bp);
}


int mm_init(void) {


	/* Preparation for segregated free list */
	if ((heap_listp = mem_sbrk(32 * WSIZE)) == NULL)
		return -1;
	PUT(heap_listp, PACK(OVERHEAD, 1));
	heap_listp += OVERHEAD;
	PUT(heap_listp - WSIZE, PACK(OVERHEAD, 1));
	PUT(heap_listp, PACK(26 * WSIZE, 1));
	startp = (size_t *)(heap_listp + WSIZE);
	int i;
	for (i = 0; i < 24; i ++) {
		PUT(startp, (size_t)(heap_listp - WSIZE));
		startp ++;
	}
	PUT(startp, PACK(26 * WSIZE, 1));
	startp = (size_t *)(heap_listp + TSIZE);


	/* create the initial empty heap */
	if ((heap_listp = mem_sbrk(OVERHEAD << 1)) == NULL)
		return -1;
	PUT(heap_listp, 0);
	PUT(heap_listp + WSIZE, PACK(OVERHEAD, 1));
	PUT(heap_listp + OVERHEAD, PACK(OVERHEAD, 1));
	PUT(heap_listp + OVERHEAD + WSIZE, PACK(0, 1));
	endp = (size_t *)(heap_listp + WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return -1;
	return 0;
}



void mm_free(void *bp) {
	size_t size = GET_SIZE(HDRP(bp));

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}



static void *find_fit(size_t asize) {

	size_t *bp;
	size_t *ap = startp + id(asize);
	size_t *cp;
	int min;
	while (ap <= endp) {
		/* best fit search */
		min = MAXNUM;
		for (bp = (size_t *)GET(NEXT_FBLK(ap)); GET_SIZE(HDRP(bp)) > OVERHEAD; bp = (size_t *)GET(NEXT_FBLK(bp))) {
			if ((asize <= GET_SIZE(HDRP(bp)))&&(GET_SIZE(HDRP(bp)) - asize < min)) {
				min = GET_SIZE(HDRP(bp)) - asize;
				cp = bp;
			}
		}
		if ( min != MAXNUM)
			return cp;
		ap ++;
	}
	return NULL;  /* no fit */
}


static void *place(void *bp, size_t asize) {

	size_t csize = GET_SIZE(HDRP(bp));

	if ((csize - asize) >= (DSIZE + OVERHEAD)) {

		/* Occupy the part on the back, aimed to reduce
		 * operations on pointers */
		delete_node(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		insert_node(bp);
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		return bp;
	}
	else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		delete_node(bp);
		return bp;
	}
}


void *mm_malloc(size_t size) {

	size_t asize;		/* adjusted block size */
	size_t extendsize; 	/* amount to extend heap if no fit */
	char *bp;

	if (size <= 0)
		return NULL;

	if (size <= DSIZE)
		asize = DSIZE + OVERHEAD;
	else
		asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL) {
		return place( bp, asize);
	}

	/* No fit found. Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	return place(bp, asize);
}





/*
 * mm_realloc - best one I can think of
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL)
    	return mm_malloc(size);
    else if (size == 0) {
    	mm_free(ptr);
    	return NULL;
    }
    else {

    	/* Adjusted size for new space */
    	size_t asize;
    	if (size <= DSIZE)
    		asize = DSIZE + OVERHEAD;
    	else
    		asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);

    	/* Remaining size */
    	size_t rsize = GET_SIZE(HDRP(ptr)) - asize;

    	if ((int)rsize >= OVERHEAD + DSIZE) {
    		PUT(FTRP(ptr), PACK(rsize, 1));
    		PUT(HDRP(ptr), PACK(asize, 1));
    		PUT(FTRP(ptr), PACK(asize, 1));
    		PUT(HDRP(NEXT_BLKP(ptr)), PACK(rsize, 1));
    		mm_free(NEXT_BLKP(ptr));
    		return (ptr);
    	}
    	else if ((int)rsize >= 0) return (ptr);
    	else {


				if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))){
					size_t tsize = GET_SIZE(HDRP(NEXT_BLKP(ptr))) + GET_SIZE(HDRP(ptr));
					if((int)(tsize - asize )>= OVERHEAD + DSIZE ) {

						delete_node(NEXT_BLKP(ptr));

						PUT(HDRP(ptr), PACK(asize, 1));
						PUT(FTRP(ptr), PACK(asize, 1));

						PUT(HDRP(NEXT_BLKP(ptr)), PACK(tsize - asize, 0));
						PUT(FTRP(NEXT_BLKP(ptr)), PACK(tsize - asize, 0));

						insert_node(NEXT_BLKP(ptr));

						return (ptr);
					}
					else if ((int)(tsize - asize) > 0){
						delete_node(NEXT_BLKP(ptr));

						PUT(HDRP(ptr), PACK(tsize, 1));
						PUT(FTRP(ptr), PACK(tsize, 1));
						return ptr;
					}
					else {
						void *new_ptr = mm_malloc(size);
						memcpy(new_ptr, ptr, GET_SIZE(HDRP(ptr)) - OVERHEAD);
						mm_free(ptr);
						return (new_ptr);
					}
				}
				else {
					void *new_ptr = mm_malloc(size);
					memcpy(new_ptr, ptr, GET_SIZE(HDRP(ptr)) - OVERHEAD);
					mm_free(ptr);
					return (new_ptr);
				}
    	}
    }

}



/*
 * mm_check - Does not currently check anything
 */
static int mm_check(void)
{
  return 1;
}







