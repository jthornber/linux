/*
 * Copyright (C) 2021 Red Hat, Inc.
 *
 * This file is released under the GPL.
 */

#include <linux/export.h>
#include <linux/mutex.h>
#include <linux/hash.h>
#include <linux/slab.h>
#include <linux/device-mapper.h>

#define DM_MSG_PREFIX "thinp2"

/*----------------------------------------------------------------*/

/* metadata blocks are indexed by a 64 bit value */
typedef uint64_t mblock;

enum io_dir {
	DIR_READ,
	DIR_WRITE,
};

enum io_flags {
	IOF_NULL,

};

struct buffer {
	// client (eg, btree)
	mblock loc;
	void *data;

	// buffer pool
	// struct rbtree_node node;

	// io
	int err;
	bool pending;
	enum io_dir dir;
	enum io_flags flags;

	// transaction manager
	struct list_head list;
};

// No locking, that's added by the transaction manager layer.
struct buffer_pool {
	unsigned nr_buffers;
	struct list_head free;
	// struct rbtree_root allocated;
};

static int bp_init(struct buffer_pool *bp, unsigned nr_buffers)
{
	return -EINVAL;
}

static void bp_exit(struct buffer_pool *bp)
{
}

struct buffer *bp_find(struct buffer_pool *bp, mblock loc)
{
	return NULL;
}

struct buffer *bp_alloc(struct buffer_pool *bp, mblock loc)
{
	return NULL;
}

void bp_free(struct buffer_pool *bp, mblock loc)
{
}

/*----------------------------------------------------------------*/

// FIXME: support plugging while we issue multiple buffers
struct io_engine {

};

static int io_init(struct block_device *bdev)
{
	return -EINVAL;
}

static void io_exit(struct io_engine *engine)
{
}

static int io_issue(struct io_engine *engine, enum io_dir d, enum io_flags f, struct buffer *b)
{
	return -EINVAL;
}

static int io_wait_buffer(struct io_engine *engine, struct buffer *b)
{
	return -EINVAL;
}

static int io_wait(struct io_engine *engine, unsigned count)
{
	return -EINVAL;
}

/*----------------------------------------------------------------*/

// FIXME: implemented in core only for now.
struct space_map {
	unsigned nr_blocks;

	// This reflects the last committed transaction.
	unsigned alloc_current;
	unsigned alloc_begin;

	// FIXME: we should have two of these bitsets; one for the committed transaction
	// and another for the currently open transaction.  This will make commit faster, since
	// we swap and memcpy the bitset, rather than running through all the ref counts.
	unsigned long *allocated_bits;

	// 255 is the max ref count, blocks will need to be cloned beyond this.
	uint8_t *ref_counts;
};

static int sm_init(struct space_map *sm)
{
	return -EINVAL;
}

static int sm_exit(struct space_map *sm)
{
	return -EINVAL;
}

static int sm_resize(struct space_map *sm, uint32_t nr_blocks)
{
	return -EINVAL;
}

static unsigned sm_nr_free(struct space_map *sm)
{
	return -EINVAL;
}

static int sm_new(struct space_map *sm, mblock *loc)
{
	return -EINVAL;
}

// Returns -EBUSY if ref count is saturated
static int sm_inc(struct space_map *sm, mblock loc)
{
	return -EINVAL;
}

static int sm_dec(struct space_map *sm, mblock loc)
{
	return -EINVAL;
}

static int sm_commit(struct space_map *sm)
{
	return -EINVAL;
}

/*----------------------------------------------------------------*/

struct transaction_manager {
	struct space_map sm;
	struct buffer_pool bp;

	struct list_head clean;
	struct list_head dirty;
	struct list_head pending;
};

static struct transaction_manager *
tm_create(struct block_device *bdev, sector_t block_size,
          unsigned max_held_per_thread)
{
	return NULL;
}

static void tm_destroy(struct transaction_manager *tm)
{
}

/*
 * Any changes to the metadata must be bracketed by these begin/end calls.
 * This ensures the changes appear as one atomic unit (eg, a btree update).
 */
static void tm_begin_atomic(struct transaction_manager *tm)
{
}

static void tm_end_atomic(struct transaction_manager *tm)
{
}

enum TM_LOCK_TYPE {
	LT_SHARED,
	LT_INTENTIONAL,
	LT_EXCLUSIVE,
};

static int tm_new(struct transaction_manager *tm, mblock *b)
{
	return -EINVAL;
}

static int tm_shadow(struct transaction_manager *tm, mblock loc,
                     mblock *result, bool *inc_children)
{
	return -EINVAL;
}

static int tm_lock(struct transaction_manager *tm, mblock loc,
            	   enum TM_LOCK_TYPE type, uint32_t metadata_type,
            	   struct buffer **result)
{
	return -EINVAL;
}

static int tm_unlock(struct buffer *b)
{
	return -EINVAL;
}

int tm_commit(struct transaction_manager *tm, void *sb_data)
{
	return -EINVAL;
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

struct node_header {
	__le32 csum;
	__le32 flags;
	__le64 blocknr;
	__le32 purpose;
	__le16 nr_entries;
	__le16 value_size;
} __attribute__((packed, aligned(8)));

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

static int btree_lookup(struct btree *bt, uint64_t key, void *value_le)
{
	return -EINVAL;
}

static int btree_lookup_range(struct btree *bt, uint64_t key_b, uint64_t key_e,
                              uint64_t *result_key, void *value_le)
{
	return -EINVAL;
}

static int btree_insert(struct btree *bt, uint64_t key, void *value_le)
{
	return -EINVAL;
}

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

/*----------------------------------------------------------------*/
