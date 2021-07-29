/*
 * Copyright (C) 2021 Red Hat, Inc.
 *
 * This file is released under the GPL.
 */

#include <linux/device-mapper.h>
#include <linux/export.h>
#include <linux/hash.h>
#include <linux/mutex.h>
#include <linux/rbtree.h>
#include <linux/slab.h>

#include "dm.h"

#define DM_MSG_PREFIX "thinp2"

/*----------------------------------------------------------------*/

struct riw_lock {
	spinlock_t lock;
	bool intent;
	__s32 count;
	struct list_head waiters;
};

struct waiter {
	struct list_head list;
	struct task_struct *task;
	bool wants_upgrade;
	bool wants_write;
};

static void __wait(struct waiter *w)
{
	for (;;) {
		set_current_state(TASK_UNINTERRUPTIBLE);

		if (!w->task)
			break;

		schedule();
	}

	set_current_state(TASK_RUNNING);
}

static void __wake_waiter(struct waiter *w)
{
	struct task_struct *task;

	list_del(&w->list);
	task = w->task;
	smp_mb();
	w->task = NULL;
	wake_up_process(task);
}

/*
 * We either wake a few readers or a single writer.
 */
// FIXME: handle INTENT locks
static void __wake_many(struct riw_lock *lock)
{
	struct waiter *w, *tmp;

	BUG_ON(lock->count < 0);
	list_for_each_entry_safe(w, tmp, &lock->waiters, list) {
		if (w->wants_write) {
			if (w->wants_upgrade) {
				if (lock->count > 1)
					return; /* still read locked */
			} else if (lock->count > 0)
					return; /* still read locked */

			lock->count = -1;
			__wake_waiter(w);
			return;
		}

		if (w->wants_intent) {

		}

		lock->count++;
		__wake_waiter(w);
	}
}

static void riw_init(struct riw_lock *lock)
{
	spin_lock_init(&lock->lock);
	lock->count = 0;
	INIT_LIST_HEAD(&lock->waiters);
}

static int __available_for_read(struct riw_lock *lock)
{
	return lock->count >= 0 && list_empty(&lock->waiters);
}

static int riw_down_read(struct riw_lock *lock)
{
	struct waiter w;

	spin_lock(&lock->lock);
	if (__available_for_read(lock)) {
		lock->count++;
		spin_unlock(&lock->lock);
		return 0;
	}

	get_task_struct(current);

	w.task = current;
	w.wants_upgrade = false;
	w.wants_write = false;
	list_add_tail(&w.list, &lock->waiters);
	spin_unlock(&lock->lock);

	__wait(&w);
	put_task_struct(current);
	return 0;
}

#if 0
// FIXME: I don't think we need this.
static int riw_down_read_nonblock(struct riw_lock *lock)
{
	int r;

	spin_lock(&lock->lock);
	if (__available_for_read(lock)) {
		lock->count++;
		r = 0;
	} else
		r = -EWOULDBLOCK;

	spin_unlock(&lock->lock);
	return r;
}
#endif

static void riw_up_read(struct riw_lock *lock)
{
	spin_lock(&lock->lock);
	BUG_ON(lock->count <= 0);
	--lock->count;
	if (!list_empty(&lock->waiters))
		__wake_many(lock);
	spin_unlock(&lock->lock);
}

// FIXME: how do we prevent multiple INTENT locks being granted?
static int riw_down_intent(struct riw_lock *lock)
{
	struct waiter w;

	spin_lock(&lock->lock);
	if (__available_for_read(lock) && !lock->intent) {
		lock->intent = true;
		lock->count++;
		spin_unlock(&lock->lock);
		return 0;
	}

	get_task_struct(current);

	w.task = current;
	w.wants_upgrade = true;
	w.wants_write = false;
	list_add_tail(&w.list, &lock->waiters);
	spin_unlock(&lock->lock);

	__wait(&w);
	put_task_struct(current);
	return 0;
}

static int riw_up_intent(struct riw_lock *lock)
{
	spin_lock(&lock->lock);
	BUG_ON(lock->count <= 0);
	--lock->count;
	lock->intent = false;
	if (!list_empty(&lock->waiters))
		__wake_many(lock);
	spin_unlock(&lock->lock);
}

static int riw_upgrade(struct riw_lock *lock)
{
	struct waiter w;

	spin_lock(&lock->lock);

	BUG_ON(!lock->intent);
	lock->intent = false;

	if (lock->count == 1 && list_empty(&lock->waiters)) {
		lock->count = -1;
		spin_unlock(&lock->lock);
		return 0;
	}

	get_task_struct(current);
	w.task = current;
	w.wants_upgrade = false;
	w.wants_write = true;

	list_add(&w.list, &lock->waiters);
	spin_unlock(&lock->lock);

	__wait(&w);
	put_task_struct(current);

	return 0;
}

static int riw_down_write(struct riw_lock *lock)
{
	struct waiter w;

	spin_lock(&lock->lock);
	if (lock->count == 0 && list_empty(&lock->waiters)) {
		lock->count = -1;
		spin_unlock(&lock->lock);
		return 0;
	}

	get_task_struct(current);
	w.task = current;
	w.wants_upgrade = false;
	w.wants_write = true;

	/*
	 * Writers given priority. We know there's only one mutator in the
	 * system, so ignoring the ordering reversal.
	 */
	list_add(&w.list, &lock->waiters);
	spin_unlock(&lock->lock);

	__wait(&w);
	put_task_struct(current);

	return 0;
}

static void riw_up_write(struct riw_lock *lock)
{
	spin_lock(&lock->lock);
	BUG_ON(lock->count >= 0);
	lock->count = 0;
	if (!list_empty(&lock->waiters))
		__wake_many(lock);
	spin_unlock(&lock->lock);
}

/*----------------------------------------------------------------*/

/* metadata blocks are indexed by a 64 bit value */
typedef uint64_t mblock;

#define MD_BLOCK_SIZE 4096

enum io_dir {
	DIR_READ,
	DIR_WRITE,
};

// FIXME: I've forgotten what this is
enum io_flags {
	IOF_NULL,
};

// Lock types are not visible above the tm which exposes spine
// objects that enforce the rolling lock protocol.


// If the block is already shadowed, and it's not going to be changed.
// Then we can get away with an INTENT lock.

// If a parent is exclusive, then we may as well make the child exclusive.
// 
// If the child needs to be shadowed, then the parent will always
// need to be upgraded.

enum lock_type {
	LT_UNLOCKED = 0,
	LT_READ,
	LT_INTENT,
	LT_WRITE,
};

struct buffer {
	spinlock_t lock;

	// transaction manager
	bool dirty;
	struct list_head list;

	// client (eg, btree)
	mblock loc;
	void *data;

	// buffer pool
	struct rb_node node;

	// locks
	enum lock_type lt; 
	struct riw_lock riw;

	// io
	int err;
	bool pending;
	enum io_dir dir;
	enum io_flags flags;
};

// No locking, that's added by the transaction manager layer.
struct buffer_pool {
	unsigned nr_buffers;
	struct buffer *bufs;
	struct list_head free;
	struct rb_root allocated;
};

static int bp_init(struct buffer_pool *bp, unsigned nr_buffers)
{
	struct buffer *bufs;

	bp->nr_buffers = nr_buffers;
	INIT_LIST_HEAD(&bp->free);
	bp->allocated = RB_ROOT;

	// FIXME: use vmalloc?
	bp->bufs = kmalloc(nr_buffers * sizeof(buffer), GFP_KERNEL);
	if (!bp->bufs)
		return -ENOMEM;

	for (i = 0; i < nr_buffers; i++)
		list_add(&bp->bufs[i].list, &bp->free);

	return 0;
}

static void bp_exit(struct buffer_pool *bp)
{
	kfree(bp->bufs);
}

struct buffer *bp_find(struct buffer_pool *bp, mblock loc)
{
	return NULL;
}

struct buffer *bp_alloc(struct buffer_pool *bp, mblock loc)
{
	struct buffer *buf;
	struct rb_node **rbp, *parent;

	if (list_empty(&bp->free))
		return NULL;

	buf = list_first_entry(&bp->free, struct buffer, list);
	list_del(&buf->list);

	rbp = &bp->allocated;
	parent = NULL;
	while (*rbp) {
		parent = *rbp;
		pbuf = node_to_buf(parent);

		if (loc < pbuf->loc)
			rbp = &(*rbp)->rb_left;
		else
			rbp = &(*rbp)->rb_right;
	}

	rb_link_node(&buf->rb_node, parent, rbp);
	rb_insert_color(&buf->rb_node, &bp->allocated);

	return buf;
}

void bp_free(struct buffer_pool *bp, struct buffer *buf)
{
	rb_erase(&buf->node, &bp->allocated);
}

/*----------------------------------------------------------------*/

// FIXME: support plugging while we issue multiple buffers
struct io_engine {
	unsigned block_size;
	struct block_device *bdev;
};

static int io_init(struct io_engine *io,
                   struct block_device *bdev,
                   unsigned block_size)
{
	io->bdev = bdev;
	io->block_size = block_size;

	return 0;
}

static void io_exit(struct io_engine *engine)
{
}

static uint64_t io_nr_blocks(struct io_engine *engine)
{
	return 0;
}

static int io_issue(struct io_engine *io, enum io_dir d, struct buffer *b)
{
	return -EINVAL;
}

static int io_wait_buffer(struct io_engine *io, struct buffer *b)
{
	return -EINVAL;
}

static int io_wait(struct io_engine *io, unsigned count)
{
	return -EINVAL;
}

/*----------------------------------------------------------------*/

// FIXME: implemented in core only for now.

struct space_map {
	unsigned nr_blocks;

	// Selects which alloc_bits, or nr_free to use.
	unsigned index;

	unsigned alloc_begin;
	unsigned long *alloc_bits[2];
	unsigned nr_free[2];

	// 255 is the max ref count, blocks will need to be cloned beyond this.
	uint8_t *ref_counts;
};

#define BITS_PER_ULONG (8 * sizeof(unsigned long))

static int sm_init(struct space_map *sm, unsigned nr_blocks)
{

	size_t bitset_len = (nr_blocks + (BITS_PER_ULONG - 1)) / BITS_PER_ULONG;

	sm->nr_blocks = nr_blocks;
	sm->index = 0;
	sm->alloc_begin = 0;

	sm->alloc_bits[0] = kzalloc(bitset_len, GFP_KERNEL);
	if (!sm->alloc_bits[0])
		return 0;

	sm->alloc_bits[1] = kzalloc(bitset_len, GFP_KERNEL);
	if (!sm->alloc_bits[1])
		return 0;

	sm->nr_free[0] = nr_blocks;
	sm->nr_free[1] = nr_blocks;

	sm->ref_counts = kzalloc(nr_blocks, GFP_KERNEL);
	if (!sm->ref_counts)
		return -ENOMEM;

	return 0;
}

static void sm_exit(struct space_map *sm)
{
	kfree(sm->alloc_bits[0]);
	kfree(sm->alloc_bits[1]);
	kfree(sm->ref_counts);
}

static int sm_resize(struct space_map *sm, uint32_t nr_blocks)
{
	return -EINVAL;
}

static unsigned sm_nr_free(struct space_map *sm)
{
	return sm->nr_free[sm->index];
}

// FIXME: slow
static int find_free_block_(unsigned long *bits, mblock b, mblock e, mblock *loc)
{
	while (b < e) {
		if (!test_bit(b, bits)) {
			*loc = b;
			set_bit(b, bits);
			return 0;
		}
	}

	return -ENOMEM;
}

static int sm_new(struct space_map *sm, mblock *loc)
{
	int r;
	unsigned long *bits = sm->alloc_bits[sm->index];

	if (!sm->nr_free[sm->index])
		return -ENOMEM;

	r = find_free_block_(bits, sm->alloc_begin, sm->nr_blocks, loc);
	if (r == -ENOMEM)
		r = find_free_block_(bits, 0, sm->alloc_begin, loc);

	if (r == 0)
		sm->nr_free[sm->index]--;

	return r;
}

static void sm_check(struct space_map *sm, mblock loc)
{
	BUG_ON(loc >= sm->nr_blocks);
}

static uint8_t sm_get(struct space_map *sm, mblock loc)
{
	sm_check(sm, loc);
	return sm->ref_counts[loc];
}

// Returns -EBUSY if ref count is saturated
static int sm_inc(struct space_map *sm, mblock loc)
{
	sm_check(sm, loc);
	if (sm->ref_counts[loc] == 0xff)
		return -EBUSY;

	sm->ref_counts[loc]++;
	return 0;
}

static int sm_dec(struct space_map *sm, mblock loc)
{
	sm_check(sm, loc);

	if (sm->ref_counts[loc] == 0) 
		return -EINVAL;

	sm->ref_counts[loc]--;
	return 0;
}

static int sm_commit(struct space_map *sm)
{
	sm->index = !sm->index;
	return 0;
}

/*----------------------------------------------------------------*/

struct ro_spine;
struct shadow_spine;

struct transaction_manager {
	struct io_engine io;
	struct space_map sm;
	struct buffer_pool bp;

	struct list_head clean;
	struct list_head dirty;
	struct list_head pending;
};

int
tm_init(struct transaction_manager *tm,
        struct block_device *bdev, sector_t block_size,
        unsigned max_held_per_thread)
{
	int r;
	unsigned nr_buffers = max_held_per_thread * 1024 + 8192;

	r = io_init(&tm->io, bdev, block_size);
	if (r)
		return r;

	r = bp_init(&tm->bp, nr_buffers);
	if (r)
		return r;

	r = sm_init(&tm->sm, io_nr_blocks(&tm->io));
	if (r)
		return r;

	INIT_LIST_HEAD(&tm->clean);
	INIT_LIST_HEAD(&tm->dirty);
	INIT_LIST_HEAD(&tm->pending);
	return 0;
}

static void tm_destroy(struct transaction_manager *tm)
{
	bp_exit(&tm->bp);
	sm_exit(&tm->sm);
	io_exit(&tm->io);
}

static int tm_new(struct transaction_manager *tm, mblock *b)
{
	return sm_new(&tm->sm, b);
}

static int tm_get(struct transaction_manager *tm, mblock loc,
                   enum lock_type lt, struct buffer **buf)
{
	int r;
	unsigned long flags;
	struct buffer *b;

	// get_ ...
	b = bp_find(&tm->bp, loc);
	if (!b) {
		b = bp_alloc(&tm->bp, loc);
		if (!b)
			return -ENOMEM;

		spin_lock_irqsave(&b->lock, flags);
		r = io_issue(&tm->io, DIR_READ, b);
		if (r) {
			spin_unlock_irqrestore(&b->lock, flags);
			return r;
		}
		spin_unlock_irqrestore(&b->lock, flags);

		r = io_wait_buffer(&tm->io, b);
		if (r) {
			spin_unlock_irqrestore(&b->lock, flags);
			return r;
		}

		spin_lock_irqsave(&b->lock, flags);
	} 
	spin_unlock_irqrestore(&b->lock, flags);

	// lock_ ...
	switch (lt) {
	case LT_UNLOCKED:
		BUG();
		break;

	case LT_READ:
		riw_down_read(&lt->riw);
		break;

	case LT_INTENT:
		riw_down_intent(&lt->riw);
		break;

	case LT_WRITE:
		riw_down_write(&lt->riw);
		break;
	}

	*buf = b;
	return 0;
}

static void tm_put(struct transaction_manager *tm, struct buffer *buf)
{
	if (buf->dirty)
		list_add(&buf->list, &tm->dirty);
	else
		list_add(&buf->list, &tm->clean);
}

static int tm_ro_spine(struct transaction_manager *tm, struct ro_spine *result)
{
	return -EINVAL;
}

static int tm_shadow_spine(struct transaction_manager *tm,
                           struct shadow_spine *result)
{
	return -EINVAL;
}

static int tm_commit(struct transaction_manager *tm, void *sb_data)
{
	return -EINVAL;
}

/*----------------------------------------------------------------*/

struct ro_spine {

};

static void ro_exit(struct ro_spine *s)
{
}

// This has to lock the new block before unlocking the parent.
static int ro_next(struct ro_spine *s, mblock loc)
{
	return -EINVAL;
}

static struct buffer *ro_get(struct ro_spine *s)
{
	return NULL;
}

/*----------------------------------------------------------------*/

/*
 * If we shadow a node with ref count higher than one, then this is
 * a 'clone', and we need to callback to increment the values in
 * this node.
 */
typedef int (*clone_fn)(void *context, struct buffer *parent,
                        struct buffer *new_child);

struct shadow_spine {
	struct transaction_manager *tm;

	void *clone_context;
	clone_fn clone;

	bool upgraded;

	bool has_parent;
	struct buffer *parent;
	mblock root;

	struct list_head held;
};

static void s_exit(struct shadow_spine *s)
{
}

static int s_new(struct shadow_spine *s, struct buffer **buf)
{
	return -EINVAL;
}

// FIXME: if INTENT or WRITE is implied by the state of the spine, how
// do we READ lock? eg, to find a suitable node for rebalancing.
static int s_get(struct shadow_spine *s, mblock loc, struct buffer **buf)
{
	*buf = NULL;
	return -EINVAL;
}

static mblock s_current(struct shadow_spine *s)
{
	return 0;
}

/*
 * All held buffers, and future buffers will now
 * be WRITE locked rather than INTENT.
 */
static int s_upgrade(struct shadow_spine *s)
{
	return -EINVAL;
}

static void s_put(struct shadow_spine *s, struct buffer *buf)
{
}

// buf becomes the new parent, old parent is unlocked.  Checks no buffers currently
// held other than buf.
static int s_step(struct shadow_spine *s, struct buffer *buf)
{
	return -EINVAL;
}

// Panics if there's no root.
static mblock s_root(struct shadow_spine *s)
{
	return 0;
}

/*----------------------------------------------------------------*/

/*
 * Information about the values stored within the btree.
 */
struct value_type {
	/*
	 * The size in bytes of each value.
	 */
	uint32_t size;

	/*
	 * Any of these methods can be safely set to NULL if you do not
	 * need the corresponding feature.
	 */

	/*
	 * The btree is making a duplicate of the value, for instance
	 * because previously-shared btree nodes have now diverged.
         * This method is _not_ called for insertion of a new
	 * value: It is assumed the ref count is already 1.
	 */
	void (*inc)(void *context, const void *value, unsigned count);

	/*
	 * This value is being deleted.  The btree takes care of freeing
	 * the memory pointed to by @value.  Often the dec function just
	 * needs to decrement a reference count somewhere.
	 */
	void (*dec)(void *context, const void *value, unsigned count);

	/*
	 * A test for equality between two values.  When a value is
	 * overwritten with a new one, the old one has the dec method
	 * called _unless_ the new and old value are deemed equal.
	 */
	int (*equal)(void *context, const void *value1, const void *value2);
};

struct btree {
	struct value_type *vt;
	void *vt_context;

	struct transaction_manager *tm;
	mblock root;
};

enum node_flags {
	INTERNAL_NODE = 1,
	LEAF_NODE = 1 << 1,
};

struct node_header {
	__le32 csum;
	__le32 flags;
	__le64 blocknr;
	__le32 purpose;
	__le16 nr_entries;
	__le16 value_size;
} __attribute__((packed, aligned(8)));

#define INTERNAL_NR_ENTRIES ((MD_BLOCK_SIZE - sizeof(struct node_header)) / (sizeof(__le64) * 2))
#define BTREE_CSUM_XOR 0xca8b176b4c75f80b	

static uint16_t leaf_max_entries(uint16_t value_size)
{
	return (MD_BLOCK_SIZE - sizeof(struct node_header)) /
		(sizeof(__le64) + value_size);
}

struct internal_node {
	struct node_header header;
	__le64 keys[INTERNAL_NR_ENTRIES];
	__le64 values[INTERNAL_NR_ENTRIES];
} __attribute__((packed, aligned(8)));

struct leaf_node {
	struct node_header header;
} __attribute__((packed, aligned(8)));

static __le64 *key_ptr(struct leaf_node *n, unsigned index)
{
	return NULL;
}

static void *value_ptr(struct leaf_node *n, unsigned index)
{
	return NULL;
}

static uint64_t value64(struct leaf_node *n, unsigned index)
{
	__le64 *v_le = value_ptr(n, index);
	return le64_to_cpu(*v_le);
}

/*----------------------------------------------------------------*/

static int bsearch(__le64 *keys, unsigned count, uint64_t key, bool want_hi)
{
	int lo = -1, hi = count;

	while (hi - lo > 1) {
		int mid = lo + ((hi - lo) / 2);
		uint64_t mid_key = le64_to_cpu(keys[mid]);

		if (mid_key == key)
			return mid;

		if (mid_key < key)
			lo = mid;
		else
			hi = mid;
	}

	return want_hi ? hi : lo;
}

static inline int lower_bound(__le64 *keys, unsigned count, uint64_t key)
{
	return bsearch(keys, count, key, false);
}

/*----------------------------------------------------------------*/

static int btree_new(struct btree *bt, struct value_type *vt, void *vt_context,
                     struct transaction_manager *tm)
{
	return -EINVAL;
}

static void btree_init(struct btree *bt, struct value_type *vt, void *vt_context,
                      struct transaction_manager *tm, mblock root)
{
	bt->vt = vt;
	bt->vt_context = vt_context;
	bt->tm = tm;
	bt->root = root;
}

static int btree_del(struct btree *bt)
{
	return -EINVAL;
}

static int btree_clone(struct btree *new_bt, struct btree *old_bt)
{
	return -EINVAL;
}

static int lookup_(struct ro_spine *s, mblock block, uint64_t key,
		   uint64_t *rkey, void *v, size_t value_size)
{
	int i, r;
	uint32_t flags, nr_entries;
	struct node_header *hdr;

	for (;;) {
		r = ro_next(s, block);
		if (r < 0)
			return r;

		hdr = ro_get(s)->data;
		flags = le32_to_cpu(hdr->flags);
		nr_entries = le16_to_cpu(hdr->nr_entries);

		if (flags & INTERNAL_NODE) {
			struct internal_node *n = ro_get(s)->data;

			i = lower_bound(n->keys, nr_entries, key);
			if (i < 0 || i >= nr_entries)
				return -ENODATA;

			block = n->values[i];

		} else if (flags & LEAF_NODE) {
			struct leaf_node *n = ro_get(s)->data;

			i = lower_bound(key_ptr(n, 0), nr_entries, key);
			if (i < 0 || i >= nr_entries)
				return -ENODATA;

			*rkey = le64_to_cpu(*key_ptr(n, i));
			memcpy(v, value_ptr(n, i), value_size);
			return 0;
		}
	}
}

static int btree_lookup(struct btree *bt, uint64_t key, void *value_le)
{
	int r;
	uint64_t rkey;
	struct ro_spine spine;

	r = tm_ro_spine(bt->tm, &spine);
	if (r)
		return r;

	r = lookup_(&spine, bt->root, key, &rkey, value_le, bt->vt->size);
	if (!r && rkey != key)
		r = -ENODATA;

	ro_exit(&spine);
	return r;
}

/*----------------------------------------------------------------*/

static int btree_lookup_range(struct btree *bt, uint64_t key_b, uint64_t key_e,
                              uint64_t *result_key, void *value_le)
{
	return -EINVAL;
}

/*----------------------------------------------------------------*/

typedef void (*copy_entries_fn)(void *dest, unsigned dest_offset,
                                const void *src, unsigned src_offset,
                                unsigned count);
typedef void (*move_entries_fn)(void *dest, unsigned dest_offset,
                                const void *src, unsigned src_offset,
                                unsigned count);

struct node_ops {
	copy_entries_fn copy;
	move_entries_fn move;
};

static void copy_internal(void *dest_, unsigned dest_offset,
                       	  const void *src_, unsigned src_offset,
                       	  unsigned count)
{
	struct internal_node *dest = dest_;
	struct internal_node const *src = src_;
	memcpy(dest->keys + dest_offset, src->keys + src_offset, count * sizeof(dest->keys[0]));
	memcpy(dest->values + dest_offset, src->values + src_offset, count * sizeof(dest->values[0]));
}

static void move_internal(void *dest_, unsigned dest_offset,
                       	  const void *src_, unsigned src_offset,
                       	  unsigned count)
{
	struct internal_node *dest = dest_;
	struct internal_node const *src = src_;
	memmove(dest->keys + dest_offset, src->keys + src_offset, count * sizeof(dest->keys[0]));
	memmove(dest->values + dest_offset, src->values + src_offset, count * dest->values[0]);
}

static struct node_ops internal_ops = {
	.copy = copy_internal,
	.move = move_internal,
};

static void copy_leaf(void *dest_, unsigned dest_offset,
               	      const void *src_, unsigned src_offset,
                      unsigned count)
{
	struct leaf_node *dest = dest_, *src = (struct leaf_node *) src_;
	unsigned size = le32_to_cpu(dest->header.value_size);

	memcpy(key_ptr(dest, dest_offset), key_ptr(src, src_offset), count * sizeof(__le64));
	memcpy(value_ptr(dest, dest_offset), value_ptr(src, src_offset), count * size);
}

static void move_leaf(void *dest_, unsigned dest_offset,
                      const void *src_, unsigned src_offset,
                      unsigned count)
{
	struct leaf_node *dest = dest_, *src = (struct leaf_node *) src_;
	unsigned size = le32_to_cpu(dest->header.value_size);

	memmove(key_ptr(dest, dest_offset), key_ptr(src, src_offset), count * sizeof(__le64));
	memmove(value_ptr(dest, dest_offset), value_ptr(src, src_offset), count * size);
}

static struct node_ops leaf_ops = {
	.copy = copy_leaf,
	.move = move_leaf,
};

struct node_ops *get_ops(struct node_header *hdr)
{
	if (le32_to_cpu(hdr->flags) & INTERNAL_NODE)
		return &internal_ops;
	else
		return &leaf_ops;
}

static void array_insert(void *base, size_t elt_size, unsigned nr_elts,
			 unsigned index, void *elt)
{
	if (index < nr_elts)
		memmove(base + (elt_size * (index + 1)),
			base + (elt_size * index),
			(nr_elts - index) * elt_size);

	memcpy(base + (elt_size * index), elt, elt_size);
}

static void copy_entries(struct node_header *dest, unsigned dest_offset,
                         struct node_header *src, unsigned src_offset,
                         unsigned count)
{
	struct node_ops *ops = get_ops(dest);
	BUG_ON(get_ops(src) != ops);
	ops->copy(dest, dest_offset, src, src_offset, count);
}

static void move_entries(struct node_header *dest, unsigned dest_offset,
                         struct node_header *src, unsigned src_offset,
                         unsigned count)
{
	struct node_ops *ops = get_ops(dest);
	BUG_ON(get_ops(src) != ops);
	ops->move(dest, dest_offset, src, src_offset, count);
}

static void shift_down(struct node_header *n, unsigned count)
{
	struct node_ops *ops = get_ops(n);
	ops->move(n, 0, n, count, le16_to_cpu(n->nr_entries) - count);
}

static void shift_up(struct node_header *n, unsigned count)
{
	struct node_ops *ops = get_ops(n);
	ops->move(n, count, n, 0, le16_to_cpu(n->nr_entries));
}

static int insert_at(struct leaf_node *n, unsigned index,
		     uint64_t key, void *value)
{
	unsigned nr_entries = le16_to_cpu(n->header.nr_entries);
	unsigned value_size = le16_to_cpu(n->header.value_size);

	__le64 key_le = cpu_to_le64(key);

	if (index > nr_entries || index >= leaf_max_entries(value_size)) {
		DMERR("too many entries in btree node for insert");
		return -ENOMEM;
	}

	array_insert(key_ptr(n, 0), sizeof(__le64), nr_entries, index, &key_le);
	array_insert(value_ptr(n, 0), value_size, nr_entries, index, value);
	n->header.nr_entries = cpu_to_le16(nr_entries + 1);

	return 0;
}

/*
 * Redistributes entries between two btree nodes to make them
 * have similar numbers of entries.
 */
static void redistribute2(struct node_header *left, struct node_header *right)
{
	unsigned nr_left = le16_to_cpu(left->nr_entries);
	unsigned nr_right = le16_to_cpu(right->nr_entries);
	unsigned total = nr_left + nr_right;
	unsigned target_left = total / 2;
	unsigned target_right = total - target_left;

	if (nr_left < target_left) {
		unsigned delta = target_left - nr_left;
		copy_entries(left, nr_left, right, 0, delta);
		shift_down(right, delta);
	} else if (nr_left > target_left) {
		unsigned delta = nr_left - target_left;
		if (nr_right)
			shift_up(right, delta);
		copy_entries(right, 0, left, target_left, delta);
	}

	left->nr_entries = cpu_to_le16(target_left);
	right->nr_entries = cpu_to_le16(target_right);
}

static void redistribute3(struct node_header *left, struct node_header *center, struct node_header *right)
{
	unsigned nr_left = le16_to_cpu(left->nr_entries);
	unsigned nr_center = le16_to_cpu(center->nr_entries);
	unsigned nr_right = le16_to_cpu(right->nr_entries);
	unsigned total, target_left, target_center, target_right;

	BUG_ON(nr_center);

	total = nr_left + nr_right;
	target_left = total / 3;
	target_center = (total - target_left) / 2;
	target_right = (total - target_left - target_center);

	if (nr_left < target_left) {
		unsigned left_short = target_left - nr_left;
		copy_entries(left, nr_left, right, 0, left_short);
		copy_entries(center, 0, right, left_short, target_center);
		shift_down(right, nr_right - target_right);

	} else if (nr_left < (target_left + target_center)) {
		unsigned left_to_center = nr_left - target_left;
		copy_entries(center, 0, left, target_left, left_to_center);
		copy_entries(center, left_to_center, right, 0, target_center - left_to_center);
		shift_down(right, nr_right - target_right);

	} else {
		unsigned right_short = target_right - nr_right;
		shift_up(right, right_short);
		copy_entries(right, 0, left, nr_left - right_short, right_short);
		copy_entries(center, 0, left, target_left, nr_left - target_left);
	}

	left->nr_entries = cpu_to_le16(target_left);
	center->nr_entries = cpu_to_le16(target_center);
	right->nr_entries = cpu_to_le16(target_right);
}

static int split_one_into_two(struct shadow_spine *s, struct buffer *child, unsigned parent_index,
                              uint64_t key, struct buffer **new_child)
{
	return -EINVAL;
#if 0
	int r;
	struct dm_block *left, *right, *parent;
	struct btree_node *ln, *rn, *pn;
	__le64 location;

	left = shadow_current(s);

	r = new_block(s->info, &right);
	if (r < 0)
		return r;

	ln = dm_block_data(left);
	rn = dm_block_data(right);

	rn->header.flags = ln->header.flags;
	rn->header.nr_entries = cpu_to_le16(0);
	rn->header.value_size = ln->header.value_size;
	redistribute2(ln, rn);

	/* patch up the parent */
	parent = shadow_parent(s);
	pn = dm_block_data(parent);

	location = cpu_to_le64(dm_block_location(right));
	__dm_bless_for_disk(&location);
	r = insert_at(sizeof(__le64), pn, parent_index + 1,
		      le64_to_cpu(rn->keys[0]), &location);
	if (r) {
		unlock_block(s->info, right);
		return r;
	}

	/* patch up the spine */
	if (key < le64_to_cpu(rn->keys[0])) {
		unlock_block(s->info, right);
		s->nodes[1] = left;
	} else {
		unlock_block(s->info, left);
		s->nodes[1] = right;
	}

	return 0;
#endif
}

/*
 * We often need to modify a sibling node.  This function shadows a particular
 * child of the given parent node.  Making sure to update the parent to point
 * to the new shadow.
 */
static int shadow_child(struct shadow_spine *s,
	                struct internal_node *parent,
	                unsigned index, struct buffer **result)
{
	mblock loc = le64_to_cpu(parent->values[index]);
	int r = s_get(s, loc, result);
	if (r)
		return r;

	parent->values[index] = cpu_to_le64((*result)->loc);
	return 0;
}

/*
 * Splits two nodes into three.  This is more work, but results in fuller
 * nodes, so saves metadata space.
 */
static int split_two_into_three(struct shadow_spine *s, struct buffer *child, unsigned parent_index,
                                uint64_t key, struct buffer **new_child)
{
	return -EINVAL;

#if 0
	int r;
	unsigned middle_index;
	struct buffer *parent_buf;


	r = s_wlock(s, s_current(s), &parent_buf);





	struct dm_block *left, *middle, *right, *parent;
	struct btree_node *ln, *rn, *mn, *pn;
	__le64 location;

	parent = shadow_parent(s);
	pn = dm_block_data(parent);

	if (parent_index == 0) {
		middle_index = 1;
		left = shadow_current(s);
		r = shadow_child(s->info, vt, pn, parent_index + 1, &right);
		if (r)
			return r;
	} else {
		middle_index = parent_index;
		r = shadow_child(s->info, vt, pn, parent_index - 1, &left);
		right = shadow_current(s);
	}

	r = new_block(s->info, &middle);
	if (r < 0)
		return r;

	ln = dm_block_data(left);
	mn = dm_block_data(middle);
	rn = dm_block_data(right);

	mn->header.nr_entries = cpu_to_le16(0);
	mn->header.flags = ln->header.flags;
	mn->header.max_entries = ln->header.max_entries;
	mn->header.value_size = ln->header.value_size;

	redistribute3(ln, mn, rn);

	/* patch up the parent */
	pn->keys[middle_index] = rn->keys[0];
	location = cpu_to_le64(dm_block_location(middle));
	__dm_bless_for_disk(&location);
	r = insert_at(sizeof(__le64), pn, middle_index,
		      le64_to_cpu(mn->keys[0]), &location);
	if (r) {
	        if (shadow_current(s) != left)
		        unlock_block(s->info, left);

	        unlock_block(s->info, middle);

	        if (shadow_current(s) != right)
		        unlock_block(s->info, right);

	        return r;
	}


	/* patch up the spine */
	if (key < le64_to_cpu(mn->keys[0])) {
		unlock_block(s->info, middle);
		unlock_block(s->info, right);
		s->nodes[1] = left;
	} else if (key < le64_to_cpu(rn->keys[0])) {
		unlock_block(s->info, left);
		unlock_block(s->info, right);
		s->nodes[1] = middle;
	} else {
		unlock_block(s->info, left);
		unlock_block(s->info, middle);
		s->nodes[1] = right;
	}

	return 0;
#endif
}

// Only called on the root of the btree.  Spine should be empty.
// After call the new parent will have been pushed to the spine, and
// the child containing the key will be in new_block.
static int split_beneath(struct shadow_spine *s,
                         struct buffer *buf, uint64_t key,
                         struct buffer **new_child)
{
	return -EINVAL;

#if 0
	int r;
	struct buffer *parent_buf, *left_buf, *right_buf;

	r = s_wlock(s, s_current(s), &parent_buf);
	if (r)
		return r;

	r = s_new(s, &left_buf);
	if (r)
		return r;

	r = s_new(s, &right_buf);
	if (r)
		return r;

	struct node_header *hdr = parent_buf->data;
	if (le32_to_cpu(hdr->flags) & INTERNAL_NODE) {
		struct internal_node *left = left_buf->data;
		struct internal_node *right = right_buf->data;

		uint32_t nr_parent = le16_to_cpu(parent->header.nr_entries);
		uint32_t nr_left = nr_parent / 2;
		uint32_t nr_right = nr_parent - nr_left;

		left->header.flags = INTERNAL_NODE;
		left->header.nr_entries = cpu_to_le16(nr_left);
		left->header.value_size = sizeof(__le64);
		memcpy(left->keys, parent->keys, nr_left * sizeof(left->keys[0]));
		memcpy(left->values, parent->values, nr_left * sizeof(left->values[0]));

		right->header.flags = parent->header.flags;
		right->header.nr_entries = cpu_to_le16(nr_right);
		right->header.value_size = sizeof(__le64);
		memcpy(right->keys, parent->keys + nr_left, nr_right * sizeof(left->keys[0]));
		memcpy(right->values, parent->values + nr_left, nr_right * sizeof(left->values[0]));

	} else {
		struct leaf_node *left = left_buf->data;
		struct leaf_node *right = right_buf->data;

		uint32_t nr_parent = le16_to_cpu(parent->header.nr_entries);
		uint32_t nr_left = nr_parent / 2;
		uint32_t nr_right = nr_parent - nr_left;

		left->header.flags = LEAF_NODE;
		left->header.nr_entries = cpu_to_le16(nr_left);
		left->header.value_size = parent->header.value_size;
		memcpy(key_ptr(left, 0), key_ptr(parent, 0), nr_left * sizeof(__le64));
		memcpy(value_ptr(ln, 0), value_ptr(pn, 0), nr_left * bt->vt->size);

		right->header.flags = parent->header.flags;
		right->header.nr_entries = cpu_to_le16(nr_right);
		right->header.value_size = parent->header.value_size;
		memcpy(key_ptr(right, 0), key_ptr(parent, nr_left), nr_right * sizeof(__le64));
		memcpy(value_ptr(right, 0), value_ptr(parent, nr_left), nr_right * bt->vt->size);
	}

	/* new_parent should just point to l and r now */
	struct internal_node *parent = parent_buf->data;
	parent->header.flags = cpu_to_le32(INTERNAL_NODE);
	parent->header.nr_entries = cpu_to_le16(2);
	parent->header.value_size = cpu_to_le32(sizeof(__le64));

	parent->keys[0] = ln->keys[0];
	val = cpu_to_le64(left_buf->loc);
	parent->values[0] = cpu_to_le64(left_buf->loc);

	parent->keys[1] = rn->keys[0];
	parent->values[1] = cpu_to_le64(right_buf->loc);

	return 0;
#endif
}

/*
 * Redistributes a nodes entries with its right sibling.  Returns the node
 * containing the desired key.
 */
static struct buffer *rebalance2_(struct internal_node *parent, unsigned parent_index,
	                          struct buffer *left_child, struct buffer *right_child,
	                          uint64_t key)
{
	struct node_header *hdr = left_child->data;

	redistribute2(left_child->data, right_child->data);
	if (le32_to_cpu(hdr->flags) & INTERNAL_NODE) {
		struct internal_node *right = right_child->data;
		parent->keys[parent_index + 1] = right->keys[0];

		if (key < le64_to_cpu(right->keys[0]))
			return left_child;
		else
			return right_child;
	} else {
		struct leaf_node *right = right_child->data;
		parent->keys[parent_index + 1] = *key_ptr(right, 0);

		if (key < le64_to_cpu(*key_ptr(right, 0)))
			return left_child;
		else
			return right_child;
	}
}

static int rebalance_left(struct shadow_spine *s, struct buffer *child,
                          unsigned parent_index, uint64_t key, struct buffer **new_child)
{
	struct buffer *parent_buf, *sib;
	struct internal_node *parent;

	int r = s_get(s, s_current(s), &parent_buf);
	if (r)
		return r;

	parent = parent_buf->data;
	r = shadow_child(s, parent, parent_index - 1, &sib);
	if (r)
		return r;

	*new_child = rebalance2_(parent, parent_index, sib, child, key);
	return 0;
}

static int rebalance_right(struct shadow_spine *s, struct buffer *child,
                           unsigned parent_index, uint64_t key, struct buffer **new_child)
{
	struct buffer *parent_buf, *sib;
	struct internal_node *parent;

	int r = s_get(s, s_current(s), &parent_buf);
	if (r)
		return r;

	parent = parent_buf->data;
	r = shadow_child(s, parent, parent_index + 1, &sib);
	if (r)
		return r;

	*new_child = rebalance2_(parent, parent_index, child, sib, key);
	return 0;
}

/*
 * Returns the number of spare entries in a node.
 */
static int get_node_free_space(struct shadow_spine *s, mblock loc, unsigned *space)
{
	int r;
	unsigned nr_entries;

	struct buffer *buf;
	struct node_header *hdr;

	r = s_get(s, loc, &buf);
	if (r)
		return r;

	hdr = buf->data;
	nr_entries = le16_to_cpu(hdr->nr_entries);
	if (le32_to_cpu(hdr->flags) & INTERNAL_NODE)
		*space = INTERNAL_NR_ENTRIES - nr_entries;
	else
		*space = leaf_max_entries(le16_to_cpu(hdr->value_size)) - nr_entries;

	return 0;
}

#define SPACE_THRESHOLD 8
static int rebalance_or_split(struct shadow_spine *s,
                              struct buffer *buf, // FIXME: rename to child
                              unsigned parent_index, uint64_t key,
                              struct buffer **new_child)
{
	int r;
	struct buffer *parent_buf;
	struct internal_node *parent;
	unsigned nr_parent;
	unsigned free_space;
	bool left_shared = false, right_shared = false;
	struct node_header *hdr;

	r = s_get(s, s_current(s), &parent_buf);
	if (r)
		return r;

	parent = parent_buf->data;
	nr_parent = le16_to_cpu(parent->header.nr_entries);

	hdr = buf->data;

	/* Should we move entries to the left sibling? */
	if (parent_index > 0) {
		mblock left_b = parent->values[parent_index - 1];

		left_shared = sm_get(&s->tm->sm, left_b) > 1;
		if (!left_shared) {
			// left isn't shared
			r = get_node_free_space(s, left_b, &free_space);
			if (r)
				return r;

			if (free_space >= SPACE_THRESHOLD)
				return rebalance_left(s, buf, parent_index, key, new_child);
		}
	}

	/* Should we move entries to the right sibling? */
	if (parent_index < (nr_parent - 1)) {
		mblock right_b = parent->values[parent_index + 1];

		right_shared = sm_get(&s->tm->sm, right_b) > 1;
		if (!right_shared) {
			r = get_node_free_space(s, right_b, &free_space);
			if (r)
				return r;

			if (free_space >= SPACE_THRESHOLD)
				return rebalance_right(s, buf, parent_index, key, new_child);
		}
	}

        /*
         * We need to split the node, normally we split two nodes
         * into three.  But when inserting a sequence that is either
         * monotonically increasing or decreasing it's better to split
         * a single node into two.
         */
	if (left_shared || right_shared || (nr_parent <= 2) ||
            (parent_index == 0) || (parent_index + 1 == nr_parent))
		return split_one_into_two(s, buf, parent_index, key, new_child);
	else
		return split_two_into_three(s, buf, parent_index, key, new_child);
}

/*
 * Does the node contain a particular key?
 */
// FIXME: duplicate bsearch
static bool contains_key(struct leaf_node *n, uint64_t key)
{
	unsigned count = le16_to_cpu(n->header.nr_entries);
	int i = lower_bound(key_ptr(n, 0), count, key);
	return (i >= 0) &&
	       (i < count) && 
	       (le64_to_cpu(*key_ptr(n, i)) == key);
}

/*
 * In general we preemptively make sure there's a free entry in every
 * node on the spine when doing an insert.  But we can avoid that with
 * leaf nodes if we know it's an overwrite.
 */
static bool has_space_for_insert(struct node_header *hdr, uint64_t key)
{
	if (le16_to_cpu(hdr->nr_entries) < leaf_max_entries(le16_to_cpu(hdr->value_size)))
		return true;

	if (le32_to_cpu(hdr->flags) & LEAF_NODE) {
		/* we don't need space if it's an overwrite */
		struct leaf_node *n = (struct leaf_node *) hdr;
		return contains_key(n, key);
	}

	return false;
}

static int insert_raw(struct shadow_spine *s,
                      mblock block,
		      uint64_t key, unsigned *index)
{
	bool top = true;
	int i = *index;

	for (;;) {
		unsigned nr_entries;
		struct buffer *buf;
		int r = s_get(s, block, &buf);

		struct node_header *hdr = buf->data;
		if (!has_space_for_insert(hdr, key)) {
			if (top)
				r = split_beneath(s, buf, key, &buf);
			else
				r = rebalance_or_split(s, buf, i, key, &buf);

			if (r < 0)
				return r;

			/* making space can cause the current node to change */
			hdr = buf->data;
		}

		nr_entries = le16_to_cpu(hdr->nr_entries);
		if (le32_to_cpu(hdr->flags) & INTERNAL_NODE) {
			struct internal_node *n = (struct internal_node *) hdr;
			i = lower_bound(n->keys, nr_entries, key);

			if (i < 0) {
				/* adjust the lower key */
				r = s_upgrade(s);
				if (r)
					return r;
				n = buf->data;

				/* change the bounds on the lowest key */
				n->keys[0] = cpu_to_le64(key);
				i = 0;
			}

			block = le64_to_cpu(n->values[i]);
		} else {
			struct leaf_node *n = (struct leaf_node *) hdr;

			i = lower_bound(key_ptr(n, 0), nr_entries, key);
			if (i < 0 || le64_to_cpu(*key_ptr(n, i)) != key)
				i++;

			*index = i;
			break;
		}

		r = s_step(s, buf);
		if (r)
			return r;

		top = false;
	}

	return 0;
}

static bool need_insert(struct leaf_node *n, uint64_t key, unsigned index)
{
        return ((index >= le16_to_cpu(n->header.nr_entries)) ||
		(le64_to_cpu(*key_ptr(n, index)) != key));
}

static int insert_(struct btree *bt, struct shadow_spine *s, uint64_t key, void *value_le)
{
	int r, index;
	struct buffer *buf;
	struct leaf_node *n;
	struct value_type *vt = bt->vt;

	r = insert_raw(s, bt->root, key, &index);
	if (r < 0)
		return r;

	r = s_upgrade(s);
	if (r)
		return r;

	r = s_get(s, s_current(s), &buf);
	if (r)
		return r;

	n = buf->data;
	if (need_insert(n, key, index))
		r = insert_at(n, index, key, value_le);
	else {
		if (vt->dec && (!vt->equal ||
		                !vt->equal(bt->vt_context, value_ptr(n, index), value_le)))
			vt->dec(bt->vt_context, value_ptr(n, index), 1);

		memcpy(value_ptr(n, index), value_le, vt->size);
	}

	return r;
}

static int btree_insert(struct btree *bt, uint64_t key, void *value_le)
{
	int r;
	struct shadow_spine spine;

	tm_shadow_spine(bt->tm, &spine);
	r = insert_(bt, &spine, key, value_le);
	if (!r)
		bt->root = s_root(&spine);
	s_exit(&spine);
	return 0;
}

/*----------------------------------------------------------------*/

static int btree_remove(struct btree *bt, uint64_t key)
{
	return -EINVAL;
}

static int btree_highest_key(struct btree *bt, uint64_t *key)
{
	return -EINVAL;
}

/*----------------------------------------------------------------*/

/*
 * The allocation groups are at fixed positions, every 2^16 sectors (32M).
 */
#define AG_SIZE 0x10000


// allocation groups
// FIXME: do we need a generation nr?  Might be helpful to stop data leaks
// when doing a thin_repair.
struct alloc_group {
	spinlock_t lock;

	uint64_t index;
	uint32_t alloc_cursor;
	uint32_t nr_allocated;
};

/*
 * Returns -ENOSPC if full.
 * FIXME: page align if possible.
 */
static int ag_alloc(struct alloc_group *ag, sector_t len, sector_t *result, uint16_t *result_len)
{
	int r = 0;
	unsigned long flags;
	spin_lock_irqsave(&ag->lock, flags);

	if (ag->alloc_cursor >= AG_SIZE)
		r = -ENOSPC;
	else {
		len = min((uint32_t) len, AG_SIZE - ag->alloc_cursor);
		*result_len = len;
		*result = ag->alloc_cursor;
		ag->alloc_cursor += len;
		ag->nr_allocated += len;
	}

	spin_unlock_irqrestore(&ag->lock, flags);
	return r;
}

static int ag_free(struct alloc_group *ag, sector_t len)
{
	int r = 0;
	unsigned long flags;
	spin_lock_irqsave(&ag->lock, flags);

	if (ag->nr_allocated < len)
		r = -EINVAL;
	else
		ag->nr_allocated -= len;

	spin_unlock_irqrestore(&ag->lock, flags);
	return r;
}

struct alloc_group_disk {
	__le16 alloc_cursor;
	__le16 nr_allocated;
}; // FIXME: packed + aligned

static struct value_type alloc_group_vt_ = {
	.size = sizeof(struct alloc_group_disk),
	.inc = NULL,
	.dec = NULL,
	.equal = NULL,
};

struct ag_tree {
	struct btree tree;
};

static int agt_new(struct ag_tree *agt, struct transaction_manager *tm)
{
	return -EINVAL;
}

static int agt_open(struct ag_tree *agt, struct transaction_manager *tm, mblock root)
{
	return -EINVAL;
}

static int agt_resize(struct ag_tree *ag, sector_t data_size)
{
	return -EINVAL;
}

/*
 * A long term borrow of an allocation group.  Typically used by a single _active_ thin
 * device.  No choice is given about which ag to borrow, one with free space will be
 * automatically chosen.
 */
static int agt_borrow(struct ag_tree *agt, struct alloc_group *result)
{
	return -EINVAL;
}

/*
 * Update the tree with changes to the borrowed allocation group.  The ag remains borrowed.
 */
static int agt_update(struct ag_tree *agt, struct alloc_group *ag)
{
	return -EINVAL;
}

/*
 * Update and return the borrowed ag.
 */
static int agt_release(struct ag_tree *agt, struct alloc_group *result)
{
	return -EINVAL;
}
 
/*----------------------------------------------------------------*/

/*
 * The extent tree holds all extents in the pool.  Avoiding contention
 * on update is important.
 */
struct extent {
	uint32_t alloc_group;
	uint16_t offset;


	// Allocation groups are no bigger than 32m, so 16bits is enough.
	uint16_t len;

	// FIXME: what happens if the ref_count saturates?
	uint16_t ref_count;
};

struct extent_disk {
	__le32 alloc_group;
	__le16 offset;
	__le16 len;
	__le16 ref_count;
} __attribute__((packed, aligned(4)));

static struct value_type extent_vt_ = {
	.size = sizeof(struct extent_disk),
	.inc = NULL,
	.dec = NULL,
	.equal = NULL,
};

struct extent_tree {
	uint64_t next_key;
	struct btree tree;
};

/*
 * Extents are identified by an opaque 64 bit value.
 */
typedef uint64_t extent_key;

static int et_new(struct extent_tree *et, struct transaction_manager *tm)
{
	et->next_key = 0;
	return btree_new(&et->tree, &extent_vt_, NULL, tm);
}

static int et_open(struct extent_tree *et, struct transaction_manager *tm, mblock root)
{
	btree_init(&et->tree, &extent_vt_, NULL, tm, root);
	return btree_highest_key(&et->tree, &et->next_key);
}

static int et_lookup(struct extent_tree *et, extent_key e, struct extent *result)
{
	struct extent_disk disk;
	int r = btree_lookup(&et->tree, e, &disk);
	if (r)
		return r;

	result->alloc_group = le32_to_cpu(disk.alloc_group);
	result->offset = le16_to_cpu(disk.offset);
	result->len = le16_to_cpu(disk.offset);
	result->ref_count = le16_to_cpu(disk.ref_count);

	return 0;
}

static int et_insert(struct extent_tree *et, struct extent *e, extent_key *key_result)
{
	struct extent_disk disk;
	disk.alloc_group = cpu_to_le32(e->alloc_group);
	disk.offset = cpu_to_le16(e->offset);
	disk.len = cpu_to_le16(e->len);
	disk.ref_count = cpu_to_le16(e->ref_count);

	*key_result = et->next_key;
	return btree_insert(&et->tree, et->next_key++, &disk);
}

static int et_remove(struct extent_tree *et, extent_key e)
{
	return btree_remove(&et->tree, e);
}

/*----------------------------------------------------------------*/

/*
 * Device identifier
 */
typedef uint64_t thin_id;

static struct value_type dev_vt_ = {
	.size = sizeof(__le64),
	.inc = NULL,
	.dec = NULL,
	.equal = NULL,
};

struct dev_tree {
	struct btree tree;
};

static int dt_new(struct dev_tree *dt, struct transaction_manager *tm)
{
	return btree_new(&dt->tree, &dev_vt_, NULL, tm);
}

static int dt_open(struct dev_tree *dt, struct transaction_manager *tm, mblock root)
{
	btree_init(&dt->tree, &dev_vt_, NULL, tm, root);
	return 0;
}

static int dt_lookup(struct dev_tree *dt, thin_id dev, mblock *root)
{
	__le64 value_le;
	int r = btree_lookup(&dt->tree, dev, &value_le);
	if (r)
		return r;

	*root = __le64_to_cpu(value_le);
	return 0;
}

static int dt_insert(struct dev_tree *dt, thin_id dev, mblock root)
{
	__le64 value_le = cpu_to_le64(root);
	return btree_insert(&dt->tree, dev, &value_le);
}

static int dt_remove(struct dev_tree *dt, thin_id dev, mblock *root)
{
	__le64 value_le;
	int r = btree_lookup(&dt->tree, dev, &value_le);
	if (r)
		return r;

	*root = __le64_to_cpu(value_le);
	return btree_remove(&dt->tree, dev);
}

/*----------------------------------------------------------------*/

struct mapping {
	sector_t thin_b;
	extent_key extent;
	uint16_t offset;
	uint16_t len;
};

struct mapping_disk {
	__le64 extent;
	__le16 offset;
	__le16 len;
};

static struct value_type mapping_vt_ = {
	.size = 8,
	.inc = NULL,
	.dec = NULL,
	.equal = NULL,
};

struct mapping_tree {
	struct btree tree;
};

static int mt_new(struct mapping_tree *mt, struct transaction_manager *tm,
                  struct extent_tree *et)
{
	return btree_new(&mt->tree, &mapping_vt_, et, tm);
}

static int mt_open(struct mapping_tree *mt, struct transaction_manager *tm,
                   struct extent_tree *et, mblock root)
{
	btree_init(&mt->tree, &mapping_vt_, et, tm, root);
	return 0;
}

static int mt_del(struct mapping_tree *mt)
{
	return -EINVAL;
}

static int mt_close(struct mapping_tree *mt)
{
	return -EINVAL;
}

/*
 * Find the first mapping in the range thin_b..thin_e
 */
static int mt_lookup(struct mapping_tree *mt, sector_t thin_b, sector_t thin_e,
                     struct mapping *result)
{
	struct mapping_disk disk;
	uint64_t key;

	int r = btree_lookup_range(&mt->tree, thin_b, thin_e, &key, &disk);
	if (r)
		return r;

	result->thin_b = key;
	result->extent = le64_to_cpu(disk.extent);
	result->offset = le16_to_cpu(disk.offset);
	result->len = le16_to_cpu(disk.len);

	return 0;
}

static int mt_insert(struct mapping_tree *mt, struct mapping *m)
{
	return -EINVAL;
}

/*
 * Removes or truncates any mappings in the range thin_b..thin_e
 */
static int mt_remove(struct mapping_tree *mt, sector_t thin_b, sector_t thin_e)
{
	return -EINVAL;
}

/*----------------------------------------------------------------*/

struct pool_metadata {
	struct transaction_manager tm;
	struct ag_tree agt;
	struct extent_tree et;
	struct dev_tree dt;
};

/*
 * Reopens or creates a new, empty metadata volume.
 */
struct metadata *metadata_open(struct block_device *bdev,
			       sector_t data_block_size,
			       bool format_device)
{
	return NULL;
}

int pool_commit(struct pool_metadata *pmd)
{
	return tm_commit(&pmd->tm, NULL);
}

int pool_metadata_close(struct pool_metadata *pmd)
{
	return pool_commit(pmd);
}

int pool_grow_data_dev(struct pool_metadata *pmd, sector_t new_size)
{
	return agt_resize(&pmd->agt, new_size);
}

int pool_grow_metadata_dev(struct pool_metadata *pmd, mblock new_size)
{
	return sm_resize(&pmd->tm.sm, new_size);
}

int pool_get_free_data(struct pool_metadata *pmd, sector_t *result)
{
	return -EINVAL;
}

int pool_get_free_metadata(struct pool_metadata *pmd, mblock *result)
{
	return -EINVAL;
}

int pool_create_thin(struct pool_metadata *pmd, thin_id dev)
{
	int r;
	struct btree tree;

	r = btree_new(&tree, &mapping_vt_, &pmd->tm, &pmd->tm);
	if (r)
		return r;

	return dt_insert(&pmd->dt, dev, tree.root);
}

int pool_create_snap(struct pool_metadata *pmd, thin_id dev, thin_id origin)
{
	int r;
	struct btree old_bt, new_bt;
	mblock mapping_root;

	r = dt_lookup(&pmd->dt, origin, &mapping_root);
	if (r)
		return r;

	btree_init(&new_bt, &mapping_vt_, &pmd->tm, &pmd->tm, mapping_root);
	r = btree_clone(&new_bt, &old_bt);
	if (r)
		return r;

	return dt_insert(&pmd->dt, dev, new_bt.root);
}

/*
 * Fails if device is active.  FIXME: no it doesn't.
 */
int pool_del_thin(struct pool_metadata *pmd, thin_id dev)
{
	int r;
	mblock mapping_root;
	struct mapping_tree mt;

	r = dt_remove(&pmd->dt, dev, &mapping_root);
	if (r)
		return r;

	r = mt_open(&mt, &pmd->tm, &pmd->et, mapping_root);
	if (r)
		return r;

	return mt_del(&mt);
}

struct thin {
	struct pool_metadata *pmd;
	struct mapping_tree mappings;
	struct alloc_group ag;
};

/*
 * Opening the same device more than once will fail with -EBUSY.
 */
int thin_open(struct pool_metadata *pmd, thin_id dev, struct thin *td)
{
	int r;
	mblock mapping_root;

	td->pmd = pmd;

	r = dt_lookup(&pmd->dt, dev, &mapping_root);
	if (r)
		return r;

	r = mt_open(&td->mappings, &pmd->tm, &pmd->et, mapping_root);
	if (r)
		return r;

	return 0;
}

int thin_close(struct thin *td)
{
	return mt_close(&td->mappings);
}

enum thin_op {
	T_READ,
	T_WRITE,
	T_ZERO,  // Use for requesting removal of mappings
};

struct map_op {
	enum thin_op op;
	sector_t b;
	sector_t e;
};

static void _remap_zeroes(struct map_op *data_op, sector_t len)
{
	data_op->op = T_ZERO;
	data_op->b = 0;
	data_op->e = len;
}

static int _provision(struct thin *td,
                      sector_t thin_b, sector_t thin_e,
                      struct map_op *data_op)
{
	int r;
	extent_key e_key;
	struct extent e;
	struct mapping m;
	sector_t new_block;
	uint16_t len;

	/* allocate new block */
	for (;;) {
		int r = ag_alloc(&td->ag, thin_e - thin_b, &new_block, &len);
		if (!r)
			break;

		if (r == -ENOSPC) {
			r = agt_release(&td->pmd->agt, &td->ag);
			if (r)
				return r;

			r = agt_borrow(&td->pmd->agt, &td->ag);
			if (r)
				return r;
		}  else
			return r;
	}

	// FIXME: amortise this, by only updating on commit
	r = agt_update(&td->pmd->agt, &td->ag);
	if (r)
		return r;

	/* insert new extent */
	e.alloc_group = td->ag.index;
	e.len = thin_e - thin_b;
	e.ref_count = 1;
	r = et_insert(&td->pmd->et, &e, &e_key);
	if (r)
		return r;

	/* insert new mapping */
	m.thin_b = thin_b;
	m.extent = e_key;
	m.offset = 0;
	m.len = thin_e - thin_b;
	r = mt_insert(&td->mappings, &m);
	if (r)
		return r;

	/* remap */
	data_op->op = T_WRITE;
	data_op->b = (e.alloc_group * AG_SIZE) + e.offset;
	data_op->e = data_op->b + e.len;

	return 0;
}

static int _read(struct thin *td,
                 struct map_op *thin_op,
                 struct map_op *data_op)
{
	struct mapping m;
	struct extent e;

	/* find a mapping */
	int r = mt_lookup(&td->mappings, thin_op->b, thin_op->e, &m);
	if (r == -ENODATA) {
		_remap_zeroes(data_op, thin_op->e - thin_op->b);
		return 0;
	}

	if (r)
		return r;

	if (m.thin_b > thin_op->b) {
		_remap_zeroes(data_op, m.thin_b - thin_op->b);
		return 0;
	}

        /* find the extent */
        r = et_lookup(&td->pmd->et, m.extent, &e);
        if (r)
	        return r;

        /* remap */
        data_op->op = T_READ;
        data_op->b = (e.alloc_group * AG_SIZE) + e.offset + m.offset;
        data_op->e = data_op->b + min((uint64_t) (e.len - m.offset),
                                      (uint64_t) (thin_op->e - thin_op->b));
        return 0;
}

static int _write(struct thin *td,
                  struct map_op *thin_op,
                  struct map_op *data_op)
{
	struct mapping m;
	struct extent e;
	uint16_t len;

	/* find a mapping */
	int r = mt_lookup(&td->mappings, thin_op->b, thin_op->e, &m);
	if (r == -ENODATA)
		return _provision(td, thin_op->b, thin_op->e, data_op);

	if (r)
		return r;

	if (m.thin_b > thin_op->b)
		return _provision(td, thin_op->b, m.thin_b, data_op);

        /* find the extent */
        r = et_lookup(&td->pmd->et, m.extent, &e);
        if (r)
	        return r;

	len = min((uint64_t) (e.len - m.offset), (uint64_t) m.len);
	len = min((uint64_t) len, (uint64_t) (thin_op->e - thin_op->b));

	/* break sharing? */
        if (e.ref_count > 1)
	        return _provision(td, thin_op->b, thin_op->b + len, data_op);

        /* remap */
        data_op->op = T_WRITE;
        data_op->b = (e.alloc_group * AG_SIZE) + e.offset + m.offset;
        data_op->e = data_op->b + min((uint64_t) (e.len - m.offset),
                                      (uint64_t) (thin_op->e - thin_op->b));
        return 0;
}

static int _zero(struct thin *td,
                 struct map_op *thin_op,
                 struct map_op *data_op)
{
	// FIXME: implement
	return 0;
}

/*
 * Only part of the thin range may be mapped, so this needs
 * to be called in a loop.
 */
int thin_map(struct thin *td, struct map_op *thin_op, struct map_op *data_op)
{
	switch (thin_op->op) {
	case T_READ:
		return _read(td, thin_op, data_op);
	case T_WRITE:
		return _write(td, thin_op, data_op);
	case T_ZERO:
		return _zero(td, thin_op, data_op);
	}

	return -EINVAL;
}

MODULE_DESCRIPTION(DM_NAME " thin provisioning target");
MODULE_AUTHOR("Joe Thornber <dm-devel@redhat.com>");
MODULE_LICENSE("GPL");

/*----------------------------------------------------------------*/
