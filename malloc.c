#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>

#define DMEM_DEBUG 0
#define USE_LIBC 0 // use libc
#define USE_QMEM 1 // use quantum mem
#define USE_UTAG 1 // use uint64 tag
#define USE_FBIN 1 // use fast bin

#if DMEM_DEBUG

#define TRACE(...) \
    ({ \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n"); \
    })

#define ASSERT(cond, ...) \
    ({ \
        if (!(cond)) { \
            TRACE(__VA_ARGS__); \
            abort(); \
        } \
    })

#define IF_DEBUG if (1)

#else

#define TRACE(...) (0)
#define ASSERT(cond, ...) (0)
#define IF_DEBUG if (0)

#endif

// slow tests: test 2 5 9 12

#define INLINE inline __attribute__((always_inline))

/***** common end *****/

/***** dmem start *****/

// dmem for dreadful memory

#define DMEM_MAX_ALIGN (2 * sizeof(size_t))
#define DMEM_AS_FREE(tag) ((free_block_t *)(tag))
#define DMEM_AS_TAG(fb) ((mem_tag_t *)(fb))
#define DMEM_PAGE_SIZE 4096
#define DMEM_MIN_SHRINK_SIZE ((size_t)-1) // don't shrink at all
    // (4 * DMEM_PAGE_SIZE - 2 * sizeof(mem_tag_t)) // min freed size at the end for a heap to shrink

#define DMEM_MIN_BLOCK_SIZE (sizeof(free_block_t) + sizeof(mem_tag_t))

#if USE_UTAG

typedef uint64_t mem_tag_t;

#define DMEM_TAG_SIZE(tag) (*(uint64_t *)(tag) & 0x3fffffffffffffffl)
#define DMEM_TAG_IS_FREE(tag) ((int)((*(uint64_t *)(tag) >> 62)))
#define DMEM_TAG_IS_QUANTUM(tag) (*(int64_t *)(tag) < 0)

#define DMEM_TAG(size, free, q) \
    ((uint64_t)(size) | ((uint64_t)(free) << 62) | ((uint64_t)(q) << 63))

typedef struct free_block_t_tag {
    mem_tag_t tag;
    struct free_block_t_tag *prev;
    struct free_block_t_tag *next;
} free_block_t;

#else

#define DMEM_MEM_TAG \
    size_t size: 62; \
    size_t free: 1; \
    size_t q: 1;

typedef struct {
    DMEM_MEM_TAG
} mem_tag_t;

#define DMEM_TAG_SIZE(tag) ((tag)->size)
#define DMEM_TAG_IS_FREE(tag) ((tag)->free)
#define DMEM_TAG_IS_QUANTUM(tag) ((tag)->q)

#define DMEM_TAG(size, free, q) ((mem_tag_t) { (size), (free), (q) })

typedef struct free_block_t_tag {
    DMEM_MEM_TAG
    struct free_block_t_tag *prev;
    struct free_block_t_tag *next;
} free_block_t;

#endif

// [ mem_tag ] [ mem_tag_t *prev ] [ mem_tag_t *next ]

#if USE_FBIN
#define DMEM_BIN_BASE 64
#define DMEM_BIN_COUNT 7 // must be an odd number
// bin 0: size <= BASE
// bin i: BASE * 2 ^ (i - 1) < size <= BASE * 2 ^ i
// bin 2: 256 < size <= 1024
// bin 3: 1024 < size <= 4096
// bin 4: size > 4096
#else
#define DMEM_BIN_BASE 0
#define DMEM_BIN_COUNT 1
#endif

typedef struct {
    free_block_t *head_bin[DMEM_BIN_COUNT];

    // free_block_t *head_free;
    size_t used;
    mem_tag_t init_tag; // init tag { 0, 0 }
} dmem_t;

INLINE size_t
dmem_bin_upper_bound(size_t bin)
{
    return DMEM_BIN_BASE << (2 * bin);
}

INLINE size_t
dmme_bin_find(size_t size)
{
#if USE_FBIN
    for (size_t i = 0; i < DMEM_BIN_COUNT; i++) {
        if (size <= dmem_bin_upper_bound(i)) return i;
    }

    return DMEM_BIN_COUNT - 1;
#else
    (void)size;
    return 0;
#endif
}

INLINE void *
dmem_break(dmem_t *dmem, ssize_t n)
{
    void *ret = (void *)(dmem + 1) + dmem->used;

    if (!n) {
        return ret;
    } else {
        if (sbrk(n) == (void *)-1) {
            return NULL; // out of mem
        }

        dmem->used += n;

        return ret; // return the previous end
    }
}

// initialize dmem in a mem trunk
INLINE void
dmem_init(dmem_t *dmem)
{
    // dmem->head_free = NULL;
    // dmem->used = 0;
    // dmem->init_tag = { 0, 0 };

    memset(dmem, 0, sizeof(*dmem));
}

// want to allocate n bytes
// align n to DMEM_MAX_ALIGN
INLINE size_t
dmem_align_size(size_t n)
{
    return (n + DMEM_MAX_ALIGN - 1) / DMEM_MAX_ALIGN * DMEM_MAX_ALIGN;
}

// get the tail tag using a head tag
INLINE mem_tag_t *
dmem_tag_head_to_tail(mem_tag_t *tag, size_t size)
{
    return (mem_tag_t *)(((void *)(tag + 1)) + size);
}

// get the head tag using the data
INLINE mem_tag_t *
dmem_tag_data_to_head(void *data)
{
    return (mem_tag_t *)data - 1;
}

// get the head tag using the data
INLINE mem_tag_t *
dmem_tag_head_to_data(mem_tag_t *head)
{
    return (mem_tag_t *)head + 1;
}

INLINE mem_tag_t *
dmem_tag_tail_to_head(mem_tag_t *tag, size_t size)
{
    return (mem_tag_t *)((void *)tag - size) - 1;
}

INLINE mem_tag_t *
dmem_tag_next(mem_tag_t *cur)
{
    return (void *)cur + DMEM_TAG_SIZE(cur) + 2 * sizeof(mem_tag_t);
}

INLINE mem_tag_t *
dmem_tag_prev(mem_tag_t *cur)
{
    mem_tag_t *prev_end = cur - 1;

    // init tag
    if (!DMEM_TAG_SIZE(prev_end)) return NULL;

    return dmem_tag_tail_to_head(prev_end, DMEM_TAG_SIZE(prev_end));
}

INLINE free_block_t *
dmem_tag_next_free(free_block_t *cur)
{
    // assuming cur is free
    ASSERT(DMEM_TAG_IS_FREE(cur), "getting free chain of non-free block");

    return cur->next;
}

INLINE void
dmem_dump(dmem_t *dmem)
{
    mem_tag_t *begin = (mem_tag_t *)(dmem + 1);
    mem_tag_t *end = dmem_break(dmem, 0), *tail;

    fprintf(stderr, "dmem: base: %p, header: %lu, used: %lu\n",
            dmem, sizeof(*dmem), dmem->used);

    for (size_t bin = 0; bin < DMEM_BIN_COUNT; bin++) {
        fprintf(stderr, "bin %lu %p\n", bin, dmem->head_bin[bin]);
    }

    for (; begin != end; begin = dmem_tag_next(begin)) {
        tail = dmem_tag_head_to_tail(begin, DMEM_TAG_SIZE(begin));
        fprintf(stderr, "%p [ %lu %d | %lu %d ]", begin,
                DMEM_TAG_SIZE(begin), DMEM_TAG_IS_FREE(begin),
                DMEM_TAG_SIZE(tail), DMEM_TAG_IS_FREE(tail));

        if (DMEM_TAG_IS_FREE(begin)) {
            fprintf(stderr, " prev: %p, next %p", DMEM_AS_FREE(begin)->prev, DMEM_AS_FREE(begin)->next);
        }

        fprintf(stderr, "\n");
    }
}

// remove the current node from the chain
// to delete the current node
INLINE void
dmem_remove_node(dmem_t *dmem, free_block_t *node, size_t bin)
{
    if (node->prev) {
        DMEM_AS_FREE(node->prev)->next = node->next;
    } else {
        // head node
        dmem->head_bin[bin] = node->next;
    }

    if (node->next) {
        DMEM_AS_FREE(node->next)->prev = node->prev;
    }
}

INLINE void
dmem_append_node(dmem_t *dmem, free_block_t *tag, size_t bin)
{
    free_block_t *node = DMEM_AS_FREE(tag);

    node->prev = NULL;
    node->next = dmem->head_bin[bin];

    if (dmem->head_bin[bin]) {
        DMEM_AS_FREE(dmem->head_bin[bin])->prev = tag;
    }

    dmem->head_bin[bin] = tag;
}

INLINE void
dmem_tag_reset(mem_tag_t *tag, size_t size, size_t free)
{
    mem_tag_t *conjugate = dmem_tag_head_to_tail(tag, size);
    *tag = *conjugate = DMEM_TAG(size, free, 0);
}

INLINE void *
dmem_alloc(dmem_t *dmem, size_t n)
{
    size_t aligned, original, rest, bin;
    mem_tag_t *nmem, *next, *prev_tail;
    free_block_t *node;

    ASSERT(n != 0, "allocating 0 byte");

    aligned = dmem_align_size(n);

    TRACE("### allocating a mem of size %lu, aligned to %lu", n, aligned);

    // search for first fit
    for (bin = dmme_bin_find(aligned);
         bin < DMEM_BIN_COUNT; bin++) {
        TRACE("searching bin %lu", bin);

        for (node = dmem->head_bin[bin]; node; node = dmem_tag_next_free(node)) {
            if (DMEM_TAG_SIZE(node) >= aligned) {
                TRACE("found first fit at %p", node);

                original = DMEM_TAG_SIZE(node);
                rest = original - aligned;
                
                if (rest >= DMEM_MIN_BLOCK_SIZE) {
                    // split it to smaller blocks

                    // reset the first half
                    dmem_tag_reset(DMEM_AS_TAG(node), aligned, 0);

                    // reset the second half as a free block
                    rest = rest - 2 * sizeof(mem_tag_t);
                    next = dmem_tag_next(DMEM_AS_TAG(node));

                    dmem_remove_node(dmem, node, bin);
                    dmem_append_node(dmem, DMEM_AS_FREE(next), dmme_bin_find(rest));

                    dmem_tag_reset(next, rest, 1);

                    TRACE("splitting to a %lu block and a %lu block", aligned, rest);
                } else {
                    // can't split

                    TRACE("no splitting possible, taking the whole block");

                    // remove the current node from the chain
                    dmem_remove_node(dmem, node, bin);

                    // use the original size
                    dmem_tag_reset(DMEM_AS_TAG(node), original, 0);
                }

                IF_DEBUG {
                    dmem_dump(dmem);
                }

                return dmem_tag_head_to_data((mem_tag_t *)node);
            }
        }
    }

    TRACE("serach done, none is found");

    // TRACE("a");
    prev_tail = (mem_tag_t *)dmem_break(dmem, 0) - 1;
    // TRACE("b %p %p", prev_tail, dmem);

    if (DMEM_TAG_IS_FREE(prev_tail)) {
        // last block is free, we allocate less mem
        TRACE("coalescing the last block, extending %lu", aligned - DMEM_TAG_SIZE(prev_tail));

        if (!dmem_break(dmem, aligned - DMEM_TAG_SIZE(prev_tail))) {
            TRACE("no mem left");
            return NULL;
        }

        nmem = dmem_tag_tail_to_head(prev_tail, DMEM_TAG_SIZE(prev_tail));

        dmem_remove_node(dmem, DMEM_AS_FREE(nmem), dmme_bin_find(DMEM_TAG_SIZE(prev_tail)));
    } else {
        TRACE("no free mem found, allocating new mem");
        nmem = dmem_break(dmem, 2 * sizeof(mem_tag_t) + aligned);
    }

    if (!nmem) {
        TRACE("no mem left");
        return NULL;
    }

    dmem_tag_reset(nmem, aligned, 0);

    IF_DEBUG {
        dmem_dump(dmem);
    }

    return dmem_tag_head_to_data(nmem);
}

// freeing the current tag
// probe around to reconstruct the free chain
INLINE void
dmem_coalesce(dmem_t *dmem, mem_tag_t *tag,
              mem_tag_t **begin, mem_tag_t **end)
{
    mem_tag_t *prev, *prev_tail, *next;
    mem_tag_t *cur_break;

    int prev_is_free, next_is_free;

    cur_break = dmem_break(dmem, 0);

    // check previous tag
    prev_tail = tag - 1;
    next = dmem_tag_next(tag);

    prev_is_free = DMEM_TAG_SIZE(prev_tail) /* not init tag */ && DMEM_TAG_IS_FREE(prev_tail);
    next_is_free = next != cur_break && DMEM_TAG_IS_FREE(next);

    prev = dmem_tag_tail_to_head(prev_tail, DMEM_TAG_SIZE(prev_tail));

    if (prev_is_free) {
        TRACE("coalescing previous block");
        *begin = prev;
        dmem_remove_node(dmem, DMEM_AS_FREE(prev), dmme_bin_find(DMEM_TAG_SIZE(prev)));
    } else {
        *begin = tag;
    }

    if (next_is_free) {
        TRACE("coalescing next block");
        *end = dmem_tag_head_to_tail(next, DMEM_TAG_SIZE(next));
        dmem_remove_node(dmem, DMEM_AS_FREE(next), dmme_bin_find(DMEM_TAG_SIZE(next)));
    } else {
        *end = dmem_tag_head_to_tail(tag, DMEM_TAG_SIZE(tag));
    }
}

INLINE int
dmem_is_last_block(dmem_t *dmem, mem_tag_t *tag)
{
    return dmem_tag_head_to_tail(tag, DMEM_TAG_SIZE(tag)) + 1 == dmem_break(dmem, 0);
}

INLINE void
dmem_free(dmem_t *dmem, void *data)
{
    mem_tag_t *tag;
    mem_tag_t *begin, *end;
    size_t final_size;

    ASSERT(data, "freeing NULL");

    tag = dmem_tag_data_to_head(data);

    TRACE("### freeing mem at %p", data);

    // begin is the head tag of the final block after coalescing
    // end is the tail tag of the final block after coalescing

    dmem_coalesce(dmem, tag, &begin, &end);

    final_size = (uintptr_t)end - (uintptr_t)begin - sizeof(mem_tag_t);

    // reset the whole coalesced block
    dmem_tag_reset(begin, final_size, 1);

    if (dmem_is_last_block(dmem, begin) && final_size >= DMEM_MIN_SHRINK_SIZE) {
        dmem_break(dmem, -(2 * sizeof(mem_tag_t) + final_size));
    } else {
        dmem_append_node(dmem, DMEM_AS_FREE(begin), dmme_bin_find(final_size));
    }

    TRACE("final block of size %lu", final_size);

    IF_DEBUG {
        dmem_dump(dmem);
    }
}

INLINE void *
dmem_realloc(dmem_t *dmem, void *data, size_t n)
{
    mem_tag_t *tag = dmem_tag_data_to_head(data), *next, *next_next, *new_next;
    mem_tag_t *cur_break;
    free_block_t *node;
    size_t total, aligned, rest, original;
    void *new_data;

    ASSERT(data, "reallocating NULL");

    aligned = dmem_align_size(n);
    cur_break = dmem_break(dmem, 0);

    TRACE("### resizing mem at %p to %lu", data, n);

    if (DMEM_TAG_SIZE(tag) >= aligned) {
        // shrink

        rest = DMEM_TAG_SIZE(tag) - aligned;

        if (rest >= DMEM_MIN_BLOCK_SIZE) {
            // shrink block

            next_next = dmem_tag_next(tag);

            // first half
            dmem_tag_reset(tag, aligned, 0);

            // second half
            next = dmem_tag_next(tag);
            rest = rest - 2 * sizeof(mem_tag_t);

            // coalesce with the next block
            if (next_next != cur_break && DMEM_TAG_IS_FREE(next_next)) {
                TRACE("coalesce after shrink");

                rest += DMEM_TAG_SIZE(next_next) + 2 * sizeof(mem_tag_t);

                dmem_remove_node(dmem, DMEM_AS_FREE(next_next), dmme_bin_find(DMEM_TAG_SIZE(next_next)));
            }

            dmem_tag_reset(next, rest, 1);
            dmem_append_node(dmem, DMEM_AS_FREE(next), dmme_bin_find(rest));

            TRACE("shrink block to %lu and %lu", aligned, rest);
        }

        IF_DEBUG {
            dmem_dump(dmem);
        }

        return data; // no need to change data
    } else {
        // grow

        next = dmem_tag_next(tag);
        node = DMEM_AS_FREE(next);

        if (next != cur_break && DMEM_TAG_IS_FREE(next)) {
            total = DMEM_TAG_SIZE(tag) + 2 * sizeof(mem_tag_t) + DMEM_TAG_SIZE(next);
            
            if (total >= aligned) {
                if (total - aligned >= DMEM_MIN_BLOCK_SIZE) {
                    // split the next block
                    rest = total - aligned - 2 * sizeof(mem_tag_t);
                    new_next = dmem_tag_head_to_tail(tag, aligned) + 1;
                    // find the next block manually

                    TRACE("splitting next block, remaining size %lu", rest);

                    // inherit prev and next pointers

                    dmem_remove_node(dmem, node, dmme_bin_find(DMEM_TAG_SIZE(node)));

                    dmem_tag_reset(new_next, rest, 1);
                    dmem_tag_reset(tag, aligned, 0);

                    dmem_append_node(dmem, DMEM_AS_FREE(new_next), dmme_bin_find(rest));
                } else {
                    TRACE("no splitting required");

                    dmem_remove_node(dmem, node, dmme_bin_find(DMEM_TAG_SIZE(node)));
                    dmem_tag_reset(tag, total, 0);
                }

                IF_DEBUG {
                    dmem_dump(dmem);
                }

                // data stays the same
                return data;
            } // no enough size
        }

        TRACE("failed to resize, using free and alloc");

        original = DMEM_TAG_SIZE(tag);

        new_data = dmem_alloc(dmem, n);

        if (new_data) {
            TRACE("memmove %lu %lu %lu\n", original, aligned, original > aligned ? aligned : original);
            memmove(new_data, data, original > aligned ? aligned : original);
        }

        dmem_free(dmem, data);

        return new_data;
    }
}

/***** dmem end *****/

/***** qmem start *****/

// qmem for quantum memory
// qmem holds mem chunks of size <= sizeof(uintptr_t) * 8

// (1 byte bitmap, 8 byte data) * DMEM_MAX_ALIGN

// 1, 2, 4, 8, 16

typedef uint32_t qmem_word_t;

// padd to s1 with a s0 prefix
#define QMEM_PAD_SIZE(s0, s1) ((s1) <= (s0) ? 0 : (s1) - (s0))
#define QMEM_PAD(s0, s1) \
    uint8_t _align[QMEM_PAD_SIZE((s0), (s1))];

typedef struct {
    uint8_t idx;
    uint8_t size: 7;
    uint8_t q: 1;
} qmem_tag_t;

#define QMEM_QSIZE 16
#define QMEM_MAP_SIZE 5 // hold maps of chunk size [ 2^0, 2^1, ... , 2^4 ]
#define QMEM_BLOCK_T_DEF(size) \
    typedef struct _qmem_block##size##_t_tag { \
        struct _qmem_block##size##_t_tag *prev; \
        struct _qmem_block##size##_t_tag *next; \
        qmem_word_t bitmap; /* 1 means free */ \
        QMEM_PAD(sizeof(qmem_word_t), (size)) \
        struct { \
            QMEM_PAD(sizeof(qmem_tag_t), (size)) \
            qmem_tag_t tag; \
            uint8_t mem[size]; \
        } data[sizeof(qmem_word_t) * 8]; \
    } _qmem_block##size##_t

#define QMEM_BLOCK_T(size) _qmem_block##size##_t

typedef struct qmem_block_t_tag {
    struct qmem_block_t_tag *prev;
    struct qmem_block_t_tag *next;
    qmem_word_t bitmap;
} qmem_block_t;

QMEM_BLOCK_T_DEF(1);
QMEM_BLOCK_T_DEF(2);
QMEM_BLOCK_T_DEF(4);
QMEM_BLOCK_T_DEF(8);
QMEM_BLOCK_T_DEF(16);

typedef struct {
    qmem_block_t *map[QMEM_MAP_SIZE]; // map[n] holds chunk of size 2^n
} qmem_t;

qmem_t *qmem_new()
{
    qmem_t *qmem = malloc(sizeof(*qmem));
    memset(qmem, 0, sizeof(*qmem));
    return qmem;
}

#define QMEM_BLOCK_NEW(s) \
    ({ \
        QMEM_BLOCK_T(s) *bin = malloc(sizeof(QMEM_BLOCK_T(s))); \
        bin->prev = NULL; \
        bin->next = NULL; \
        bin->bitmap = -1; \
        for (uint8_t i = 0; i < sizeof(qmem_word_t) * 8; i++) { \
            bin->data[i].tag.idx = i; \
            bin->data[i].tag.size = (s); \
            bin->data[i].tag.q = 1; \
        } \
        bin; \
    })

#define QMEM_CHECK_SET(mask, ishft, bshft) \
    if (!(bitmap & mask)) { \
        idx |= 1 << ishft; \
        bitmap = bitmap >> bshft; \
    }

INLINE qmem_tag_t *
qmem_ptr_to_tag(void *ptr)
{
    return (qmem_tag_t *)ptr - 1;
}

INLINE qmem_block_t *
qmem_ptr_to_block(void *ptr)
{
    qmem_tag_t *tag = qmem_ptr_to_tag(ptr);
    int pref = QMEM_PAD_SIZE(sizeof(qmem_tag_t), tag->size) + sizeof(qmem_tag_t);

    return ptr - pref - tag->idx * (pref + tag->size) -
           2 * sizeof(qmem_block_t *) -
           sizeof(qmem_word_t) - QMEM_PAD_SIZE(sizeof(qmem_word_t), tag->size);
}

INLINE int
qmem_size_to_bin(uint8_t size)
{
    switch (size) {
        case 1: return 0;
        case 2: return 1;
        case 4: return 2;
        case 8: return 3;
        case 16: return 4;
        default:
            ASSERT(0, "invalid size");
    }

    return -1;
}

#define QMEM_ALLOC(bin_idx, size) \
    ({ \
        QMEM_BLOCK_T(size) *bin; \
        qmem_word_t bitmap; \
        int idx; \
 \
        if (!qmem->map[bin_idx]) { \
            qmem->map[bin_idx] = (qmem_block_t *)QMEM_BLOCK_NEW(size); \
        } \
        bin = (QMEM_BLOCK_T(size) *)qmem->map[bin_idx]; \
 \
        while (1) { \
            bitmap = bin->bitmap; \
            idx = 0; \
 \
            if (bitmap) { \
                /* QMEM_CHECK_SET(0xffffffff, 5, 32); */ \
                QMEM_CHECK_SET(0xffff, 4, 16); \
                QMEM_CHECK_SET(0xff, 3, 8); \
                QMEM_CHECK_SET(0xf, 2, 4); \
                QMEM_CHECK_SET(0x3, 1, 2); \
                QMEM_CHECK_SET(0x1, 0, 1); \
 \
                bin->bitmap &= ~(1 << idx); \
 \
                /* remove the current block */ \
                if (!bin->bitmap) { \
                    if ((qmem_block_t *)bin == qmem->map[bin_idx]) { \
                        qmem->map[bin_idx] = (qmem_block_t *)bin->next; \
 \
                        if (bin->next) { \
                            bin->next->prev = bin->prev; \
                        } \
                    } else { \
                        if (bin->prev) { \
                            bin->prev->next = bin->next; \
                        } \
 \
                        if (bin->next) { \
                            bin->next->prev = bin->prev; \
                        } \
                    } \
 \
                    bin->next = bin->prev = NULL; \
                } \
 \
                return bin->data[idx].mem; \
            } \
 \
            if (!bin->next) { \
                bin->next = QMEM_BLOCK_NEW(size); \
            } \
            bin = bin->next; \
        } \
    })

INLINE void *
qmem_alloc(qmem_t *qmem, size_t size)
{
    switch (size) {
        case 1: QMEM_ALLOC(0, 1);

        case 2: QMEM_ALLOC(1, 2);

        case 3:
        case 4: QMEM_ALLOC(2, 4);

        case 5:
        case 6:
        case 7:
        case 8: QMEM_ALLOC(3, 8);

        case 9: case 10: case 11: case 12:
        case 13: case 14: case 15: case 16:
            QMEM_ALLOC(4, 16);

        default:
            ASSERT(0, "unsupported quantum size %lu", size);
    }

    return NULL;
}

INLINE void
qmem_free(qmem_t *qmem, void *ptr)
{
    qmem_block_t *block = qmem_ptr_to_block(ptr);
    qmem_tag_t *tag = qmem_ptr_to_tag(ptr);
    int bin_idx = qmem_size_to_bin(tag->size);

    if (!block->bitmap) {
        // append to the chain
        block->prev = NULL;
        block->next = qmem->map[bin_idx];

        if (qmem->map[bin_idx]) {
            qmem->map[bin_idx]->prev = block;
        }

        qmem->map[bin_idx] = block;
    }

    block->bitmap |= 1 << tag->idx;

    if (block->bitmap == (qmem_word_t)-1 &&
        (block->prev || block->next)) {
        // remove if all freed
        if (qmem->map[bin_idx] == block) {
            qmem->map[bin_idx] = block->next;
        }

        if (block->next) {
            block->next->prev = block->prev;
        }

        if (block->prev) {
            block->prev->next = block->next;
        }

        free(block);
    }
}

INLINE int
qmem_is_qmem(void *ptr)
{
    qmem_tag_t *tag = qmem_ptr_to_tag(ptr);
    return tag->q;
}

INLINE size_t
qmem_size(void *ptr)
{
    qmem_tag_t *tag = qmem_ptr_to_tag(ptr);
    return tag->size;
}

#if !USE_LIBC

static void *heap = NULL;
static size_t cur_size = 0;
static qmem_t *qmem = NULL;

INLINE void heap_init()
{
    if (!heap) {
        heap = sbrk(sizeof(dmem_t));
        cur_size = sizeof(dmem_t);

        if (USE_QMEM) {
            dmem_init(heap);
            qmem = qmem_new();
        }
    }
}

void *calloc(size_t num, size_t size) {
    void *ret = malloc(num * size);
    memset(ret, 0, num * size);
    return ret;
}

void *malloc(size_t size) {
    heap_init();

    if (!USE_QMEM || size > QMEM_QSIZE) {
        return dmem_alloc(heap, size);
    } else {
        return qmem_alloc(qmem, size);
    }
}

void free(void *ptr) {
    if (ptr) {
        if (!USE_QMEM || !qmem_is_qmem(ptr)) {
            dmem_free(heap, ptr);
        } else {
            qmem_free(qmem, ptr);
        }
    }
}

void *realloc(void *ptr, size_t size) {
    void *new;
    size_t orig;    

    if (!ptr) return malloc(size);

    heap_init();
    
    if (!USE_QMEM || !qmem_is_qmem(ptr)) {
        return dmem_realloc(heap, ptr, size);
    } else {
        new = malloc(size);
        orig = qmem_size(ptr);

        memcpy(new, ptr, orig > size ? size : orig);
        qmem_free(qmem, ptr);

        return new;
    }
}

#else

#endif

