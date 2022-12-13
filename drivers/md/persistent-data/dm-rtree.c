/*
 * Copyright (C) 2021 Red Hat, Inc.
 *
 * This file is released under the GPL.
 */

#include "dm-rtree.h"
#include "dm-space-map.h"

#include <linux/device-mapper.h>

#define DM_MSG_PREFIX "btree"

/*----------------------------------------------------------------*/

enum node_flags {
	INTERNAL_NODE = 1,
	LEAF_NODE = 1 << 1
};

// FIXME: add timestamp
struct node_header {
	__le32 csum;
	__le32 flags;
	__le64 blocknr;


	// FIXME: do we need this?
	/* this is the end value for the highest range in this subtree */
	__le64 node_end;

	__le32 nr_entries;
	__le32 padding;

	// FIXME: add data_base
} __attribute__((packed, aligned(8)));

// FIXME: if we shrink data_begin to 32bits, then we'll have to aligned(4)
struct disk_mapping {
	__le64 data_begin;
	__le32 len;
	__le32 time;
} __attribute__((packed, aligned(8)));

/*
 * We hold an extra key in these nodes so we know the end value for the highest
 * entry in the children.
 */

#define MD_BLOCK_SIZE 4096
#define INTERNAL_NR_ENTRIES ((MD_BLOCK_SIZE - sizeof(struct node_header)) / (sizeof(__le64) * 2))
#define LEAF_NR_ENTRIES ((MD_BLOCK_SIZE - sizeof(struct node_header))  / (sizeof(__le64) + sizeof(struct disk_mapping)))

// FIXME: make 32bit variants for small keys, and small data_blocks
struct internal_node {
	struct node_header header;
	__le64 keys[INTERNAL_NR_ENTRIES];
	__le64 values[INTERNAL_NR_ENTRIES];
} __attribute__((packed, aligned(8)));

struct leaf_node {
	struct node_header header;
	__le64 keys[LEAF_NR_ENTRIES];
	struct disk_mapping values[LEAF_NR_ENTRIES];
} __attribute__((packed, aligned(8)));

struct del_args {
	struct dm_transaction_manager *tm;
	struct dm_space_map *data_sm;
};

struct insert_args {
	struct dm_transaction_manager *tm;
	struct dm_space_map *data_sm;
	struct dm_mapping *v;
};

struct node_info {
	dm_block_t loc;
	dm_block_t lowest_key;
	unsigned nr_entries;
};

struct insert_result {
	unsigned nr_nodes;
	struct node_info nodes[2];
};

struct remove_args {
	struct dm_transaction_manager *tm;
	struct dm_space_map *data_sm;
	dm_block_t thin_b;
	dm_block_t thin_e;
};

struct node_ops {
	/*
         * Shifting may cause entries to be merged, so don't assume you know
         * the nr_entries after a shift.
         */
        // FIXME: I'm not sure shift needs to be an op
	void (*shift)(struct dm_block *left, struct dm_block *right, int count);

	void (*rebalance2)(struct dm_transaction_manager *tm,
                           struct dm_block *left, struct dm_block *right,
                           struct insert_result *res);
	int (*del)(struct del_args *args, struct dm_block *b);
	int (*insert)(struct insert_args *args, struct dm_block *b, struct insert_result *res);
	int (*remove)(struct remove_args *args, struct dm_block *b);
};

static int get_ops(struct node_header *h, struct node_ops **ops);

/*----------------------------------------------------------------*/

// FIXME: generate own random number
#define RTREE_CSUM_XOR 0x8f279d9c

static void node_prep(struct dm_block_validator *v,
		      struct dm_block *b,
		      size_t block_size)
{
	struct node_header *h = dm_block_data(b);

	h->blocknr = cpu_to_le64(dm_block_location(b));
	h->csum = cpu_to_le32(dm_bm_checksum(&h->flags,
					     block_size - sizeof(__le32),
					     RTREE_CSUM_XOR));
}

static int node_check(struct dm_block_validator *v,
		      struct dm_block *b,
		      size_t block_size)
{
	struct node_header *h = dm_block_data(b);
	uint32_t csum;

	if (dm_block_location(b) != le64_to_cpu(h->blocknr)) {
		DMERR_LIMIT("node_check failed: blocknr %llu != wanted %llu",
			    le64_to_cpu(h->blocknr), dm_block_location(b));
		return -ENOTBLK;
	}

	csum = dm_bm_checksum(&h->flags, block_size - sizeof(__le32), RTREE_CSUM_XOR);
	if (csum != le32_to_cpu(h->csum)) {
		DMERR_LIMIT("node_check failed: csum %u != wanted %u", csum, le32_to_cpu(h->csum));
		return -EILSEQ;
	}

	return 0;
}

struct dm_block_validator validator = {
	.name = "rtree_node",
	.prepare_for_write = node_prep,
	.check = node_check
};

/*----------------------------------------------------------------*/

static void init_node_info(struct node_info *info, dm_block_t loc, dm_block_t lowest_key, unsigned nr_entries)
{
	info->loc = loc;
	info->lowest_key = lowest_key;
	info->nr_entries = nr_entries;
}

static int bsearch(uint64_t *keys, unsigned count, uint64_t key, bool want_hi)
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

static inline int lower_bound(uint64_t *keys, unsigned count, uint64_t key)
{
	return bsearch(keys, count, key, false);
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

static void array_erase(void *base, size_t elt_size, unsigned nr_elts,
                        unsigned index)
{
	memmove(base + (elt_size * index),
                base + (elt_size * (index + 1)),
                (nr_elts - index - 1) * elt_size);
}

/*----------------------------------------------------------------*/

static int del_(struct del_args *args, dm_block_t loc)
{
	int r;
	struct node_ops *ops;
	struct dm_block *b;

	r = dm_tm_read_lock(args->tm, loc, &validator, &b);
	if (r)
		return r;

	r = get_ops(dm_block_data(b), &ops);
	if (r) {
		dm_tm_unlock(args->tm, b);
		return r;
	}

	r = ops->del(args, b);
	dm_tm_unlock(args->tm, b);
	return r;
}

/*----------------------------------------------------------------*/

static void internal_erase(struct internal_node *n, unsigned index)
{
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);
	array_erase(n->keys, sizeof(n->keys[0]), nr_entries, index);
	array_erase(n->values, sizeof(n->values[0]), nr_entries, index);
	n->header.nr_entries = cpu_to_le32(nr_entries - 1);
}

static void internal_move(struct internal_node *n, int shift)
{
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);

	if (shift < 0) {
		shift = -shift;
		BUG_ON(shift > nr_entries);
		memmove(n->keys, n->keys + shift, (nr_entries - shift) * sizeof(n->keys[0]));
		memmove(n->values, n->values + shift, (nr_entries - shift) * sizeof(n->values[0]));
	} else {
		BUG_ON(nr_entries + shift > INTERNAL_NR_ENTRIES);
		memmove(n->keys + shift, n->keys, nr_entries * sizeof(n->keys[0]));
		memmove(n->values + shift, n->values, nr_entries * sizeof(n->values[0]));
	}
}

static void internal_copy(struct internal_node *left, struct internal_node *right, int shift)
{
	uint32_t nr_left = le32_to_cpu(left->header.nr_entries);

	if (shift < 0) {
		shift = -shift;
		BUG_ON(nr_left + shift > INTERNAL_NR_ENTRIES);
		memcpy(left->keys + nr_left, right->keys, shift * sizeof(left->keys[0]));
		memcpy(left->values + nr_left, right->values, shift * sizeof(left->values[0]));
	} else {
		BUG_ON(shift > INTERNAL_NR_ENTRIES);
		memcpy(right->keys, left->keys + (nr_left - shift), shift * sizeof(left->keys[0]));
		memcpy(right->values, left->values + (nr_left - shift), shift * sizeof(left->values[0]));
	}
}

static void internal_shift(struct dm_block *left, struct dm_block *right, int count)
{
	struct internal_node *l = dm_block_data(left);
	struct internal_node *r = dm_block_data(right);

	uint32_t nr_left = le32_to_cpu(l->header.nr_entries);
	uint32_t nr_right = le32_to_cpu(r->header.nr_entries);

	BUG_ON(nr_left - count > INTERNAL_NR_ENTRIES);
	BUG_ON(nr_right + count > INTERNAL_NR_ENTRIES);

	if (count > 0) {
		internal_move(r, count);
		internal_copy(l, r, count);
	} else {
		internal_copy(l, r, count);
		internal_move(r, count);
	}

	l->header.nr_entries = cpu_to_le32(nr_left - count);
	r->header.nr_entries = cpu_to_le32(nr_right + count);
}

static void redist2_internal(struct dm_block *left_, struct dm_block *right_);
static void internal_rebalance2(struct dm_transaction_manager *tm, struct dm_block *left, struct dm_block *right, struct insert_result *res)
{
	struct internal_node *l = dm_block_data(left);
	struct internal_node *r = dm_block_data(right);

	uint32_t nr_left = le32_to_cpu(l->header.nr_entries);
	uint32_t nr_right = le32_to_cpu(r->header.nr_entries);

	if (nr_left + nr_right <= INTERNAL_NR_ENTRIES) {
		/* merge the two nodes */
		internal_shift(left, right, -le32_to_cpu(r->header.nr_entries));
		dm_tm_dec(tm, dm_block_location(right));
		res->nr_nodes = 1;
		init_node_info(&res->nodes[0], dm_block_location(left),
                               le64_to_cpu(l->keys[0]), le32_to_cpu(l->header.nr_entries));

	} else {
		redist2_internal(left, right);
		res->nr_nodes = 2;
		init_node_info(&res->nodes[0], dm_block_location(left),
                               le64_to_cpu(l->keys[0]), le32_to_cpu(l->header.nr_entries));
		init_node_info(&res->nodes[1], dm_block_location(right),
                               le64_to_cpu(r->keys[0]), le32_to_cpu(r->header.nr_entries));
	}
}

static int internal_del(struct del_args *args, struct dm_block *b)
{
	int r;
	struct internal_node *n = dm_block_data(b);
	struct dm_block_manager *bm = dm_tm_get_bm(args->tm);
	uint32_t i, nr_entries = le32_to_cpu(n->header.nr_entries);

	/* prefetch children */
	for (i = 0; i < nr_entries; i++)
		dm_bm_prefetch(bm, le64_to_cpu(n->values[i]));

	/* recurse into children */
	for (i = 0; i < nr_entries; i++) {
		int shared;
		dm_block_t child_b = le64_to_cpu(n->values[i]);

		r = dm_tm_block_is_shared(args->tm, child_b, &shared);
		if (r)
			return r;

		if (shared) {
			/* just decrement the ref count for this child */
			dm_tm_dec(args->tm, child_b);
		} else {
			r = del_(args, child_b);
			if (r)
				return r;
		}
	}

	dm_tm_dec(args->tm, dm_block_location(b));
	return 0;
}

static void insert_into_internal(struct internal_node *node, unsigned index,
		      	        uint64_t key, dm_block_t value)
{
	uint32_t nr_entries = le32_to_cpu(node->header.nr_entries);
	__le64 key_le = cpu_to_le64(key);
	__le64 value_le = cpu_to_le64(value);

	array_insert(node->keys, sizeof(node->keys[0]), nr_entries, index, &key_le);
	array_insert(node->values, sizeof(node->values[0]), nr_entries, index, &value_le);
	node->header.nr_entries = cpu_to_le32(nr_entries + 1);
}

static void redist2_internal(struct dm_block *left_, struct dm_block *right_)
{
	struct internal_node *left = dm_block_data(left_);
	struct internal_node *right = dm_block_data(right_);
	unsigned nr_left = le32_to_cpu(left->header.nr_entries);
	unsigned nr_right = le32_to_cpu(right->header.nr_entries);
	unsigned total = nr_left + nr_right;
	unsigned target_left = total / 2;

	// FIXME: these are the same
	if (nr_left < target_left) {
		int delta = (int) nr_left - (int) target_left;
		internal_shift(left_, right_, delta);

	} else if (nr_left > target_left) {
		int delta = nr_left - target_left;
		internal_shift(left_, right_, delta);
	}
}

static int shadow_node(struct dm_transaction_manager *tm, struct dm_space_map *data_sm,
                       dm_block_t loc, struct dm_block **result)
{
	int inc, r;

	r = dm_tm_shadow_block(tm, loc, &validator, result, &inc);
	if (r)
		return r;

	if (inc) {
		// FIXME: finish
	}

	return 0;
}

// FIXME: rename
static int insert_aux(struct insert_args *args, dm_block_t loc, struct insert_result *res)
{
	int r;
	struct dm_block *b;
	struct node_ops *ops;

	r = shadow_node(args->tm, args->data_sm, loc, &b);
	if (r)
		return r;

	r = get_ops(dm_block_data(b), &ops);
	if (r) {
		dm_tm_unlock(args->tm, b);
		return r;
	}

	r = ops->insert(args, b, res);
	dm_tm_unlock(args->tm, b);
	return r;
}

#if 0
static void rebalance3(struct insert_args *args, struct internal_node *n, unsigned index)
{
}
#endif

static int rebalance2(struct insert_args *args, struct internal_node *n, unsigned index)
{
	int r;
	struct insert_result res;
	struct dm_block *left, *right;
	struct node_ops *ops;

	r = shadow_node(args->tm, args->data_sm, n->values[index], &left);
	if (r)
		return r;

	r = shadow_node(args->tm, args->data_sm, n->values[index + 1], &right);
	if (r) {
		dm_tm_unlock(args->tm, left);
		return r;
	}

	r = get_ops(dm_block_data(left), &ops);
	if (r)
		goto out;

	ops->rebalance2(args->tm, left, right, &res);

	if (res.nr_nodes == 1) {
		if (le32_to_cpu(n->header.nr_entries == 2)) {
			// FIXME: avoid this copy
			memcpy(n, dm_block_data(left), 4096);
			dm_tm_dec(args->tm, dm_block_location(left));
		} else {
			n->keys[index] = res.nodes[0].lowest_key;
			n->values[index] = res.nodes[0].loc;
			internal_erase(n, index + 1);
		}
	} else {
		n->keys[index] = res.nodes[0].lowest_key;
		n->values[index] = res.nodes[0].loc;
		n->keys[index + 1] = res.nodes[1].lowest_key;
		n->values[index + 1] = res.nodes[1].loc;
	}

out:
	dm_tm_unlock(args->tm, left);
	dm_tm_unlock(args->tm, right);
	return r;
}

static void rebalance(struct insert_args *args, struct internal_node *n, unsigned index)
{
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);

	BUG_ON(nr_entries < 2);

#if 0
	if (index == 0)
		rebalance2(args, n, 0);

	else if (index == nr_entries - 1)
		rebalance2(args, n, nr_entries - 2);

	else
		rebalance3(args, n, index - 1);
#else
	// FIXME: add rebalance 3
	if (index == nr_entries - 1)
		rebalance2(args, n, nr_entries - 2);
	else
		rebalance2(args, n, index);

#endif
}

static int internal_insert(struct insert_args *args, struct dm_block *b, struct insert_result *res)
{
	int r, i;
	dm_block_t child_b;
	struct internal_node *n = dm_block_data(b);
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);
	
	i = lower_bound(n->keys, nr_entries, args->v->thin_begin);
	if (i < 0)
		i = 0;

	child_b = le64_to_cpu(n->values[i]);
	r = insert_aux(args, child_b, res);

	if (res->nr_nodes == 1) {
		n->keys[i] = cpu_to_le64(res->nodes[0].lowest_key);
		n->values[i] = cpu_to_le64(res->nodes[0].loc);

		// FIXME: this should depend on whether it's a leaf or internal
		if (res->nodes[0].nr_entries < ((INTERNAL_NR_ENTRIES * 2) / 3))
			rebalance(args, n, i);

		res->nr_nodes = 1;
		init_node_info(&res->nodes[0], dm_block_location(b),
                               le64_to_cpu(n->keys[0]), le32_to_cpu(n->header.nr_entries));
	} else {
		n->keys[i] = cpu_to_le64(res->nodes[0].lowest_key);
		n->values[i] = cpu_to_le64(res->nodes[0].loc);

		if (nr_entries < INTERNAL_NR_ENTRIES) {
			insert_into_internal(n, i + 1, res->nodes[1].lowest_key, res->nodes[1].loc);
			res->nr_nodes = 1;
			init_node_info(&res->nodes[0], dm_block_location(b),
	                               le64_to_cpu(n->keys[0]), le32_to_cpu(n->header.nr_entries));

		} else {
			/* split the node */
			struct dm_block *sib;
			struct internal_node *sib_n, *n2;

			r = dm_tm_new_block(args->tm, &validator, &sib);
			if (r < 0)
				return r;

			sib_n = dm_block_data(sib);

			sib_n->header.flags = n->header.flags;
			sib_n->header.nr_entries = cpu_to_le32(0);

			redist2_internal(b, sib);

			if (args->v->thin_begin < le64_to_cpu(sib_n->keys[0]))
				n2 = n;
			else {
				n2 = sib_n;
				i -= le32_to_cpu(n->header.nr_entries);
			}
			insert_into_internal(n2, i + 1, res->nodes[1].lowest_key, res->nodes[1].loc);

			res->nr_nodes = 2;
			init_node_info(&res->nodes[0], dm_block_location(b),
	                               le64_to_cpu(n->keys[0]), le32_to_cpu(n->header.nr_entries));
			init_node_info(&res->nodes[1], dm_block_location(sib),
	                               le64_to_cpu(sib_n->keys[0]), le32_to_cpu(sib_n->header.nr_entries));

			dm_tm_unlock(args->tm, sib);
		}
	}

	return 0;
}

static int internal_remove(struct remove_args *args, struct dm_block *b)
{
	return -EINVAL;
}

static struct node_ops internal_ops = {
	.shift = internal_shift,
	.rebalance2 = internal_rebalance2,
	.del = internal_del,
	.insert = internal_insert,
	.remove = internal_remove
};

/*----------------------------------------------------------------*/

static bool adjacent_mapping(struct dm_mapping *left, struct dm_mapping *right)
{
	uint64_t thin_delta = right->thin_begin - left->thin_begin;

	return (thin_delta == left->len) &&
               (left->data_begin + (uint64_t) left->len == right->data_begin) &&
               (left->time == right->time);
}

static void leaf_move(struct leaf_node *n, int shift)
{
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);

	if (shift == 0) {

	} else if (shift < 0) {
		shift = -shift;
		BUG_ON(shift > nr_entries);
		memmove(n->keys, n->keys + shift, (nr_entries - shift) * sizeof(n->keys[0]));
		memmove(n->values, n->values + shift, (nr_entries - shift) * sizeof(n->values[0]));
	} else {
		BUG_ON(nr_entries + shift > LEAF_NR_ENTRIES);
		memmove(n->keys + shift, n->keys, nr_entries * sizeof(n->keys[0]));
		memmove(n->values + shift, n->values, nr_entries * sizeof(n->values[0]));
	}
}

static void leaf_copy(struct leaf_node *left, struct leaf_node *right, int shift)
{
	uint32_t nr_left = le32_to_cpu(left->header.nr_entries);

	if (shift < 0) {
		shift = -shift;
		BUG_ON(nr_left + shift > LEAF_NR_ENTRIES);
		memcpy(left->keys + nr_left, right->keys, shift * sizeof(left->keys[0]));
		memcpy(left->values + nr_left, right->values, shift * sizeof(left->values[0]));
	} else {
		BUG_ON(shift > LEAF_NR_ENTRIES);
		memcpy(right->keys, left->keys + (nr_left - shift), shift * sizeof(left->keys[0]));
		memcpy(right->values, left->values + (nr_left - shift), shift * sizeof(left->values[0]));
	}
}

static void leaf_shift_(struct leaf_node *l, struct leaf_node *r, int count)
{
	uint32_t nr_left = le32_to_cpu(l->header.nr_entries);
	uint32_t nr_right = le32_to_cpu(r->header.nr_entries);

	BUG_ON(nr_left - count > LEAF_NR_ENTRIES);
	BUG_ON(nr_right + count > LEAF_NR_ENTRIES);

	if (count > 0) {
		leaf_move(r, count);
		leaf_copy(l, r, count);
	} else {
		leaf_copy(l, r, count);
		leaf_move(r, count);
	}

	l->header.nr_entries = cpu_to_le32(nr_left - count);
	r->header.nr_entries = cpu_to_le32(nr_right + count);
}

static void leaf_shift(struct dm_block *left, struct dm_block *right, int count)
{
	struct leaf_node *l = dm_block_data(left);
	struct leaf_node *r = dm_block_data(right);

	uint32_t nr_left = le32_to_cpu(l->header.nr_entries);
	uint32_t nr_right = le32_to_cpu(r->header.nr_entries);
	
	if (!count)
		return;

	if (nr_left && nr_right) {
		/*
                 * Check to see if we can merge the last entry from the left
                 * node with the first entry from the right node.
                 */
		struct disk_mapping *last_left = l->values + nr_left - 1;
		struct dm_mapping ll = {
			.thin_begin = l->keys[nr_left - 1],
			.data_begin = le64_to_cpu(last_left->data_begin),
			.len = le32_to_cpu(last_left->len),
			.time = le32_to_cpu(last_left->time)
		};
                                        
		struct disk_mapping *first_right = r->values;
		struct dm_mapping fr = {
			.thin_begin = r->keys[0],
			.data_begin = le64_to_cpu(first_right->data_begin),
			.len = le32_to_cpu(first_right->len),
			.time = le32_to_cpu(first_right->time)
		};

		if (adjacent_mapping(&ll, &fr)) {
			l->header.nr_entries = cpu_to_le32(nr_left - 1);
			r->keys[0] = l->keys[nr_left - 1];
			r->values[0].data_begin = l->values[nr_left - 1].data_begin;
			r->values[0].len = cpu_to_le32(ll.len + fr.len);

			// Adjust the count, since there's one fewer entries in left now
			if (count > 0)
				count -= 1;
		}
	}

	leaf_shift_(l, r, count);
}

static void redist2_leaf(struct dm_block *left_, struct dm_block *right_);
static void leaf_rebalance2(struct dm_transaction_manager *tm,
                            struct dm_block *left, struct dm_block *right,
                            struct insert_result *res)
{
	struct leaf_node *l = dm_block_data(left);
	struct leaf_node *r = dm_block_data(right);

	uint32_t nr_left = le32_to_cpu(l->header.nr_entries);
	uint32_t nr_right = le32_to_cpu(r->header.nr_entries);

	if (nr_left + nr_right <= LEAF_NR_ENTRIES) {
		/* merge the two nodes */
		leaf_shift(left, right, -nr_right);
		dm_tm_dec(tm, dm_block_location(right));
		res->nr_nodes = 1;
		init_node_info(&res->nodes[0], dm_block_location(left),
                               le64_to_cpu(l->keys[0]), le32_to_cpu(l->header.nr_entries));

	} else {
		redist2_leaf(left, right);
		res->nr_nodes = 2;
		init_node_info(&res->nodes[0], dm_block_location(left),
                               le64_to_cpu(l->keys[0]), le32_to_cpu(l->header.nr_entries));
		init_node_info(&res->nodes[1], dm_block_location(right),
                               le64_to_cpu(r->keys[0]), le32_to_cpu(r->header.nr_entries));
	}
}

static int leaf_del(struct del_args *args, struct dm_block *b)
{
	struct leaf_node *n = dm_block_data(b);
	uint32_t i, nr_entries = le32_to_cpu(n->header.nr_entries);

	/* release the data blocks */
	for (i = 0; i < nr_entries; i++) {
		struct disk_mapping *m = n->values + i;
		dm_block_t data_begin = le64_to_cpu(m->data_begin);
		dm_block_t data_end = data_begin + le32_to_cpu(m->len);
		dm_sm_dec_blocks(args->data_sm, data_begin, data_end);
	}

	dm_tm_dec(args->tm, dm_block_location(b));
	return 0;
}


// FIXME: make copy/move_entries generic, then we need only one redist2
// fn.
static void redist2_leaf(struct dm_block *left_, struct dm_block *right_)
{
	struct leaf_node *left = dm_block_data(left_);
	struct leaf_node *right = dm_block_data(right_);
	unsigned nr_left = le32_to_cpu(left->header.nr_entries);
	unsigned nr_right = le32_to_cpu(right->header.nr_entries);
	unsigned total = nr_left + nr_right;
	unsigned target_left = total / 2;

	// FIXME: these are the same
	if (nr_left < target_left) {
		int delta = (int) nr_left - (int) target_left;
		leaf_shift(left_, right_, delta);

	} else if (nr_left > target_left) {
		int delta = nr_left - target_left;
		leaf_shift(left_, right_, delta);
	}
}

static void leaf_insert_(struct leaf_node *n, struct dm_mapping *v, unsigned index)
{
	struct disk_mapping value_le;
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);
	__le64 key_le = cpu_to_le64(v->thin_begin);

	value_le.data_begin = cpu_to_le64(v->data_begin);
	value_le.len = cpu_to_le32(v->len);
	value_le.time = cpu_to_le32(v->time);

	array_insert(n->keys, sizeof(n->keys[0]), nr_entries, index, &key_le);
	array_insert(n->values, sizeof(n->values[0]), nr_entries, index, &value_le);
	n->header.nr_entries = cpu_to_le32(nr_entries + 1);
}

static int insert_into_leaf(struct insert_args *args, struct dm_block *b, unsigned index,
		      	    struct insert_result *res)
{
	int r;
	struct leaf_node *n = dm_block_data(b);
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);

	if (nr_entries == LEAF_NR_ENTRIES) {
		/* split the node */
		struct dm_block *sib;
		struct leaf_node *sib_n, *n2;

		r = dm_tm_new_block(args->tm, &validator, &sib);
		if (r < 0)
			return r;

		sib_n = dm_block_data(sib);

		sib_n->header.flags = n->header.flags;
		sib_n->header.nr_entries = cpu_to_le32(0);

		redist2_leaf(b, sib);

		/* choose which sibling to insert into */
		if (args->v->thin_begin < le64_to_cpu(sib_n->keys[0]))
			n2 = n;

		else {
			n2 = sib_n;
			index -= le32_to_cpu(n->header.nr_entries);
		}
		nr_entries = le32_to_cpu(n2->header.nr_entries);

		leaf_insert_(n2, args->v, index);

		res->nr_nodes = 2;
		init_node_info(&res->nodes[0], dm_block_location(b),
                               le64_to_cpu(n->keys[0]), le32_to_cpu(n->header.nr_entries));
		init_node_info(&res->nodes[1], dm_block_location(sib),
                               le64_to_cpu(sib_n->keys[0]), le32_to_cpu(sib_n->header.nr_entries));

		dm_tm_unlock(args->tm, sib);
	} else {
		leaf_insert_(n, args->v, index);
		res->nr_nodes = 1;
		init_node_info(&res->nodes[0], dm_block_location(b),
                               le64_to_cpu(n->keys[0]), le32_to_cpu(n->header.nr_entries));
	}
	return 0;
}

static void erase_from_leaf(struct leaf_node *node, unsigned index)
{
	uint32_t nr_entries = le32_to_cpu(node->header.nr_entries);
	array_erase(node->keys, sizeof(node->keys[0]), nr_entries, index);
	array_erase(node->values, sizeof(node->values[0]), nr_entries, index);
	node->header.nr_entries = cpu_to_le32(nr_entries - 1);
}

static int leaf_insert(struct insert_args *args, struct dm_block *b, struct insert_result *res)
{
	int i;
	struct leaf_node *n = dm_block_data(b);
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);
	struct dm_mapping *value = args->v;

	// FIXME: would this be better named 'index'
	i = lower_bound(n->keys, nr_entries, args->v->thin_begin);

	if (nr_entries == 0) {
		return insert_into_leaf(args, b, 0, res);

	} else if (i < 0) {
		struct disk_mapping *m = n->values + 0;
		struct dm_mapping right;

		right.thin_begin = le64_to_cpu(n->keys[0]);
		right.data_begin = le64_to_cpu(m->data_begin);
		right.len = le32_to_cpu(m->len);
		right.time = le32_to_cpu(m->time);
		
		if (adjacent_mapping(args->v, &right)) {
			n->keys[0] = cpu_to_le64(value->thin_begin);
			m->data_begin = cpu_to_le64(value->data_begin);
			m->len = cpu_to_le32(value->len + right.len);
		} else {
			/* new entry goes at start */
			return insert_into_leaf(args, b, 0, res);
		}

	} else if (i == nr_entries - 1) {
		/* check for adjacency on left */
		struct disk_mapping *m = n->values + i;
		struct dm_mapping left;

		left.thin_begin = le64_to_cpu(n->keys[i]);
		left.data_begin = le64_to_cpu(m->data_begin);
		left.len = le32_to_cpu(m->len);
		left.time = le32_to_cpu(m->time);

		if (adjacent_mapping(&left, value)) {
			m->len = cpu_to_le32(left.len + args->v->len);
		} else {
			return insert_into_leaf(args, b, i + 1, res);
		}

	} else {
		struct dm_mapping left;
		struct dm_mapping right;
		struct disk_mapping *lm = n->values + i;
		struct disk_mapping *rm = n->values + i + 1;

		left.thin_begin = le64_to_cpu(n->keys[i]);
		left.data_begin = le64_to_cpu(lm->data_begin);
		left.len = le32_to_cpu(lm->len);
		left.time = le32_to_cpu(lm->time);

		right.thin_begin = le64_to_cpu(n->keys[i + 1]);
		right.data_begin = le64_to_cpu(rm->data_begin);
		right.len = le32_to_cpu(rm->len);
		right.time = le32_to_cpu(rm->time);

		if (adjacent_mapping(&left, value)) {
			if (adjacent_mapping(value, &right)) {
				/* adjacent to both left and right */
				lm->len = cpu_to_le32(left.len + args->v->len + right.len);
				erase_from_leaf(n, i + 1);
			} else {
				/* adjacent to left only */
				lm->len = cpu_to_le32(left.len + args->v->len);
			}
		} else if (adjacent_mapping(value, &right)) {
			/* adjacent to right only */
			n->keys[i + 1] = cpu_to_le64(args->v->thin_begin);
			rm->data_begin = cpu_to_le64(args->v->data_begin);
			rm->len = cpu_to_le32(value->len + right.len);
		} else {
			/* not adjacent */
			return insert_into_leaf(args, b, i + 1, res);
		}
	}

	res->nr_nodes = 1;
	res->nodes[0].loc = dm_block_location(b);
	res->nodes[0].lowest_key = le64_to_cpu(n->keys[0]);
	res->nodes[0].nr_entries = le32_to_cpu(n->header.nr_entries);

	return 0;
}

static struct node_ops leaf_ops = {
	.shift = leaf_shift,
	.rebalance2 = leaf_rebalance2,
	.del = leaf_del,
	.insert = leaf_insert,
	.remove = NULL
};

static int get_ops(struct node_header *h, struct node_ops **ops)
{
	uint32_t flags = le32_to_cpu(h->flags);
	if (flags == LEAF_NODE)
		*ops = &leaf_ops;
	else if (flags == INTERNAL_NODE)
		*ops = &internal_ops;
	else
		return -EINVAL;
	return 0;
}

/*----------------------------------------------------------------*/

int dm_rtree_empty(struct dm_transaction_manager *tm, dm_block_t *root)
{
	int r;
	struct dm_block *b;
	struct node_header *h;

	r = dm_tm_new_block(tm, &validator, &b);
	if (r < 0)
		return r;

	h = dm_block_data(b);
	h->flags = cpu_to_le32(LEAF_NODE);
	h->blocknr = cpu_to_le64(dm_block_location(b));
	h->nr_entries = cpu_to_le32(0);

	*root = dm_block_location(b);
	dm_tm_unlock(tm, b);

	return 0;
}
EXPORT_SYMBOL_GPL(dm_rtree_empty);

/*----------------------------------------------------------------*/

int dm_rtree_del(struct dm_transaction_manager *tm, struct dm_space_map *data_sm, dm_block_t root)
{
	struct del_args args = {.tm = tm, .data_sm = data_sm};
	return del_(&args, root);

}
EXPORT_SYMBOL_GPL(dm_rtree_del);

/*----------------------------------------------------------------*/

int dm_rtree_lookup(struct dm_transaction_manager *tm, dm_block_t root,
                    dm_block_t key,
                    struct dm_mapping *result)
{
	int i, r;
	bool found = false;
	struct dm_block *b;
	uint32_t flags, nr_entries;
	struct node_header *h;
	struct internal_node *n;

	while (!found) {
		r = dm_tm_read_lock(tm, root, &validator, &b);
		if (r < 0)
			return r;

		h = dm_block_data(b);
		flags = le32_to_cpu(h->flags);
		nr_entries = le32_to_cpu(h->nr_entries);

		n = (struct internal_node *) h;
		i = lower_bound(n->keys, nr_entries, key);
		if (i < 0 || i >= nr_entries) {
			dm_tm_unlock(tm, b);
			return -ENODATA;
		}

		if (flags & INTERNAL_NODE)
			root = le64_to_cpu(n->values[i]);

		else {
			struct disk_mapping *v;
			dm_block_t thin_begin, thin_end, data_begin, data_end;
			uint32_t len, time;
			
			struct leaf_node *n = (struct leaf_node *) h;

			v = n->values + i;
			thin_begin = le64_to_cpu(n->keys[i]);
			data_begin = le64_to_cpu(v->data_begin);
			len = le32_to_cpu(v->len);
			time = le32_to_cpu(v->time);
			thin_end = thin_begin + len;
			data_end = data_begin + len;

			if (key > thin_end) {
				dm_tm_unlock(tm, b);
				return -ENODATA;
			}

			result->thin_begin = thin_begin;
			result->data_begin = data_begin;
			result->len = len;
			result->time = time;
			found = true;
		}

		dm_tm_unlock(tm, b);
	}

	return r;
}
EXPORT_SYMBOL_GPL(dm_rtree_lookup);

/*----------------------------------------------------------------*/

#if 0
/*
 * Copies entries from one region of a btree to another.  The regions
 * must not overlap.
 */
static void copy_entries(struct node_header *dest_h, unsigned dest_offset,
                         struct node_header *src_h, unsigned src_offset,
                         unsigned count)
{
	uint32_t flags = le32_to_cpu(dest_h->flags);

	if (flags & INTERNAL_NODE) {
		struct internal_node *dest = (struct internal_node *) dest_h;
		struct internal_node *src = (struct internal_node *) src_h;
		memcpy(dest->keys + dest_offset, src->keys + src_offset, count * sizeof(dest->keys[0]));
		memcpy(dest->values + dest_offset, src->values + src_offset, count * sizeof(dest->values[0]));
	} else {
		struct leaf_node *dest = (struct leaf_node *) dest_h;
		struct leaf_node *src = (struct leaf_node *) src_h;
		memcpy(dest->keys + dest_offset, src->keys + src_offset, count * sizeof(dest->keys[0]));
		memcpy(dest->values + dest_offset, src->values + src_offset, count * sizeof(dest->values[0]));
	}
}

/*
 * Moves entries from one region node to another.  The regions
 * may overlap.
 */
static void move_entries(struct node_header *dest_h, unsigned dest_offset,
                         struct node_header *src_h, unsigned src_offset,
                         unsigned count)
{
	uint32_t flags = le32_to_cpu(dest_h->flags);

	if (flags & INTERNAL_NODE) {
		struct internal_node *dest = (struct internal_node *) dest_h;
		struct internal_node *src = (struct internal_node *) src_h;
		memmove(dest->keys + dest_offset, src->keys + src_offset, count * sizeof(dest->keys[0]));
		memmove(dest->values + dest_offset, src->values + src_offset, count * sizeof(dest->values[0]));
	} else {
		struct leaf_node *dest = (struct leaf_node *) dest_h;
		struct leaf_node *src = (struct leaf_node *) src_h;
		memmove(dest->keys + dest_offset, src->keys + src_offset, count * sizeof(dest->keys[0]));
		memmove(dest->values + dest_offset, src->values + src_offset, count * sizeof(dest->values[0]));
	}
}

/*
 * Erases the first 'count' entries of a node, shifting following
 * entries down into their place.
 */
static void shift_down(struct node_header *h, unsigned count)
{
	move_entries(h, 0, h, count, le32_to_cpu(h->nr_entries) - count);
}

/*
 * Moves entries in a node up 'count' places, making space for
 * new entries at the start of the node.
 */
static void shift_up(struct node_header *h, unsigned count)
{
	move_entries(h, count, h, 0, le32_to_cpu(h->nr_entries));
}

/*
 * Redistributes entries between two btree nodes to make them
 * have similar numbers of entries.
 */
static void redistribute2(struct node_header *left, struct node_header *right)
{
	unsigned nr_left = le32_to_cpu(left->nr_entries);
	unsigned nr_right = le32_to_cpu(right->nr_entries);
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

	left->nr_entries = cpu_to_le32(target_left);
	right->nr_entries = cpu_to_le32(target_right);
}

/*
 * Redistribute entries between three nodes.  Assumes the central
 * node is empty.
 */
static void redistribute3(struct node_header *left, struct node_header *center, struct node_header *right)
{
	unsigned nr_left = le32_to_cpu(left->nr_entries);
	unsigned nr_center = le32_to_cpu(center->nr_entries);
	unsigned nr_right = le32_to_cpu(right->nr_entries);
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

	left->nr_entries = cpu_to_le32(target_left);
	center->nr_entries = cpu_to_le32(target_center);
	right->nr_entries = cpu_to_le32(target_right);
}


/*
 * Splits a node by creating a sibling node and shifting half the nodes
 * contents across.  Assumes there is a parent node, and it has room for
 * another child.
 */
static int split_one_into_two(struct shadow_spine *s, unsigned parent_index, dm_block_t key)
{
	int r;
	struct dm_block *left, *right, *parent;
	struct node_header *lh, *rh;
	struct internal_node *pn, *rn;
	__le64 location;

	left = shadow_current(s);

	r = dm_tm_new_block(s->tm, &validator, &right);
	if (r < 0)
		return r;

	lh = dm_block_data(left);
	rh = dm_block_data(right);

	rh->flags = lh->flags;
	rh->nr_entries = cpu_to_le32(0);
	redistribute2(lh, rh);

	/* patch up the parent */
	parent = shadow_parent(s);
	pn = dm_block_data(parent);

	location = cpu_to_le64(dm_block_location(right));
	rn = (struct internal_node *) rh;
	insert_into_internal(pn, parent_index + 1, le64_to_cpu(rn->keys[0]),
                             dm_block_location(right));

	/* patch up the spine */
	if (key < le64_to_cpu(rn->keys[0])) {
		dm_tm_unlock(s->tm, right);
		s->nodes[1] = left;
	} else {
		dm_tm_unlock(s->tm, left);
		s->nodes[1] = right;
	}

	return 0;
}

/*
 * We often need to modify a sibling node.  This function shadows a particular
 * child of the given parent node.  Making sure to update the parent to point
 * to the new shadow.
 */
static int shadow_child(struct dm_transaction_manager *tm,
                        struct dm_space_map *data_sm,
		        struct internal_node *pn,
		        unsigned index, struct dm_block **result)
{
	int r, inc;
	dm_block_t block = le64_to_cpu(pn->values[index]);
	r = dm_tm_shadow_block(tm, block, &validator, result, &inc);
	if (r)
		return r;

	if (inc)
		inc_children(tm, data_sm, *result);

	pn->values[index] = cpu_to_le64(dm_block_location(*result));
	return 0;
}

/*
 * Splits two nodes into three.  This is more work, but results in fuller
 * nodes, so saves metadata space.
 */
static int split_two_into_three(struct shadow_spine *s, unsigned parent_index, dm_block_t key)
{
	int r;
	unsigned middle_index;
	struct dm_block *left, *middle, *right, *parent;
	struct node_header *lh, *rh, *mh;
	struct internal_node *pn, *mn, *rn;

	parent = shadow_parent(s);
	pn = dm_block_data(parent);

	if (parent_index == 0) {
		middle_index = 1;
		left = shadow_current(s);
		r = shadow_child(s->tm, s->data_sm, pn, parent_index + 1, &right);
		if (r)
			return r;
	} else {
		middle_index = parent_index;
		r = shadow_child(s->tm, s->data_sm, pn, parent_index - 1, &left);
		right = shadow_current(s);
	}

	r = dm_tm_new_block(s->tm, &validator, &middle);
	if (r < 0)
		return r;

	lh = dm_block_data(left);
	mh = dm_block_data(middle);
	rh = dm_block_data(right);

	mh->nr_entries = cpu_to_le32(0);
	mh->flags = lh->flags;

	redistribute3(lh, mh, rh);

	/* patch up the parent */
	rn = (struct internal_node *) rh;
	mn = (struct internal_node *) mh;
	pn->keys[middle_index] = rn->keys[0];
	insert_into_internal(pn, middle_index,
                             le64_to_cpu(mn->keys[0]), dm_block_location(middle));

	/* patch up the spine */
	mn = (struct internal_node *) mh;
	if (key < le64_to_cpu(mn->keys[0])) {
		dm_tm_unlock(s->tm, middle);
		dm_tm_unlock(s->tm, right);
		s->nodes[1] = left;
	} else if (key < le64_to_cpu(rn->keys[0])) {
		dm_tm_unlock(s->tm, left);
		dm_tm_unlock(s->tm, right);
		s->nodes[1] = middle;
	} else {
		dm_tm_unlock(s->tm, left);
		dm_tm_unlock(s->tm, middle);
		s->nodes[1] = right;
	}

	return 0;
}

/*
 * Splits a node by creating two new children beneath the given node.
 */
static int split_beneath_leaf(struct shadow_spine *s, uint64_t key)
{
	int r;
	unsigned nr_left, nr_right;
	struct dm_block *left, *right, *new_parent;
	struct leaf_node *pn, *ln, *rn;
	struct internal_node *pn_i;

	BUG_ON(s->count != 1);
	new_parent = shadow_current(s);

	pn = dm_block_data(new_parent);

	/* create & init the left block */
	r = dm_tm_new_block(s->tm, &validator, &left);
	if (r < 0)
		return r;

	ln = dm_block_data(left);
	nr_left = le32_to_cpu(pn->header.nr_entries) / 2;

	ln->header.flags = pn->header.flags;
	ln->header.nr_entries = cpu_to_le32(nr_left);
	memcpy(ln->keys, pn->keys, nr_left * sizeof(pn->keys[0]));
	memcpy(ln->values, pn->values, nr_left * sizeof(pn->values[0]));

	/* create & init the right block */
	r = dm_tm_new_block(s->tm, &validator, &right);
	if (r < 0) {
		dm_tm_unlock(s->tm, left);
		return r;
	}

	rn = dm_block_data(right);
	nr_right = le32_to_cpu(pn->header.nr_entries) - nr_left;

	rn->header.flags = pn->header.flags;
	rn->header.nr_entries = cpu_to_le32(nr_right);
	memcpy(rn->keys, pn->keys + nr_left, nr_right * sizeof(pn->keys[0]));
	memcpy(rn->values, pn->values + nr_left, nr_right * sizeof(pn->values[0]));

	/* new_parent should just point to l and r now */
	pn_i = (struct internal_node *) pn;
	pn_i->header.flags = cpu_to_le32(INTERNAL_NODE);
	pn_i->header.nr_entries = cpu_to_le32(2);

	pn_i->keys[0] = ln->keys[0];
	pn_i->values[0] = cpu_to_le64(dm_block_location(left));
	
	pn_i->keys[1] = rn->keys[0];
	pn_i->values[1] = cpu_to_le64(dm_block_location(right));
	
	dm_tm_unlock(s->tm, left);
	dm_tm_unlock(s->tm, right);
	return 0;
}

static int split_beneath_internal(struct shadow_spine *s, uint64_t key)
{
	int r;
	unsigned nr_left, nr_right;
	struct dm_block *left, *right, *new_parent;
	struct internal_node *pn, *ln, *rn;
	struct internal_node *pn_i;

	BUG_ON(s->count != 1);
	new_parent = shadow_current(s);

	pn = dm_block_data(new_parent);

	/* create & init the left block */
	r = dm_tm_new_block(s->tm, &validator, &left);
	if (r < 0)
		return r;

	ln = dm_block_data(left);
	nr_left = le32_to_cpu(pn->header.nr_entries) / 2;

	ln->header.flags = pn->header.flags;
	ln->header.nr_entries = cpu_to_le32(nr_left);
	memcpy(ln->keys, pn->keys, nr_left * sizeof(pn->keys[0]));
	memcpy(ln->values, pn->values, nr_left * sizeof(pn->values[0]));

	/* create & init the right block */
	r = dm_tm_new_block(s->tm, &validator, &right);
	if (r < 0) {
		dm_tm_unlock(s->tm, left);
		return r;
	}

	rn = dm_block_data(right);
	nr_right = le32_to_cpu(pn->header.nr_entries) - nr_left;

	rn->header.flags = pn->header.flags;
	rn->header.nr_entries = cpu_to_le32(nr_right);
	memcpy(rn->keys, pn->keys + nr_left, nr_right * sizeof(pn->keys[0]));
	memcpy(rn->values, pn->values + nr_left, nr_right * sizeof(pn->values[0]));

	/* new_parent should just point to l and r now */
	pn_i = (struct internal_node *) pn;
	pn_i->header.flags = cpu_to_le32(INTERNAL_NODE);
	pn_i->header.nr_entries = cpu_to_le32(2);

	pn_i->keys[0] = ln->keys[0];
	pn_i->values[0] = cpu_to_le64(dm_block_location(left));
	
	pn_i->keys[1] = rn->keys[0];
	pn_i->values[1] = cpu_to_le64(dm_block_location(right));
	
	dm_tm_unlock(s->tm, left);
	dm_tm_unlock(s->tm, right);
	return 0;
}

static int split_beneath(struct shadow_spine *s, uint64_t key)
{
	struct node_header *h = dm_block_data(shadow_current(s));
	uint32_t flags = le32_to_cpu(h->flags);
	if (flags == LEAF_NODE) {
		return split_beneath_leaf(s, key);
	} else {
		return split_beneath_internal(s, key);
	}
}

/*
 * Redistributes a node's entries with its left sibling.
 */
static int rebalance_left(struct shadow_spine *s,
                          unsigned parent_index, uint64_t key)
{
	int r;
	struct dm_block *sib;
	struct node_header *lh, *rh;
	struct internal_node *rn, *pn = dm_block_data(shadow_parent(s));

	r = shadow_child(s->tm, s->data_sm, pn, parent_index - 1, &sib);
	if (r)
		return r;

	lh = dm_block_data(sib);
	rh = dm_block_data(shadow_current(s));
	redistribute2(lh, rh);

	rn = (struct internal_node *) rh;
	pn->keys[parent_index] = rn->keys[0];

	if (key < le64_to_cpu(rn->keys[0])) {
	        dm_tm_unlock(s->tm, s->nodes[1]);
	        s->nodes[1] = sib;
	} else {
	        dm_tm_unlock(s->tm, sib);
	}

	return 0;
}

/*
 * Redistributes a nodes entries with its right sibling.
 */
static int rebalance_right(struct shadow_spine *s,
                           unsigned parent_index, uint64_t key)
{
	int r;
	struct dm_block *sib;
	struct node_header *lh, *rh;
	struct internal_node *rn, *pn = dm_block_data(shadow_parent(s));

	r = shadow_child(s->tm, s->data_sm, pn, parent_index + 1, &sib);
	if (r)
		return r;

	lh = dm_block_data(shadow_current(s));
	rh = dm_block_data(sib);
	redistribute2(lh, rh);

	rn = (struct internal_node *) rh;
	pn->keys[parent_index + 1] = rn->keys[0];

	if (key < le64_to_cpu(rn->keys[0])) {
	        dm_tm_unlock(s->tm, sib);
	} else {
	        dm_tm_unlock(s->tm, s->nodes[1]);
	        s->nodes[1] = sib;
	}

	return 0;
}

/*
 * Returns the number of spare entries in a node.
 */
static int get_node_free_space(struct dm_transaction_manager *tm, dm_block_t b, unsigned *space)
{
	int r;
	unsigned nr_entries;
	struct dm_block *block;
	struct node_header *h;

	r = dm_tm_read_lock(tm, b, &validator, &block);
	if (r)
		return r;

	h = dm_block_data(block);
	nr_entries = le32_to_cpu(h->nr_entries);
	if (le32_to_cpu(h->flags) & INTERNAL_NODE)
		*space = INTERNAL_NR_ENTRIES - nr_entries;
	else
		*space = LEAF_NR_ENTRIES - nr_entries;

	dm_tm_unlock(tm, block);
	return 0;
}

/*
 * Make space in a node, either by moving some entries to a sibling,
 * or creating a new sibling node.  SPACE_THRESHOLD defines the minimum
 * number of free entries that must be in the sibling to make the move
 * worth while.  If the siblings are shared (eg, part of a snapshot),
 * then they are not touched, since this break sharing and so consume
 * more space than we save.
 */
#define SPACE_THRESHOLD 8
static int rebalance_or_split(struct shadow_spine *s, unsigned parent_index, uint64_t key)
{
	int r;
	struct internal_node *pn = dm_block_data(shadow_parent(s));
	unsigned nr_parent = le32_to_cpu(pn->header.nr_entries);
	unsigned free_space;
	int left_shared = 0, right_shared = 0;

	/* Should we move entries to the left sibling? */
	if (parent_index > 0) {
		dm_block_t left_b = le64_to_cpu(pn->values[parent_index - 1]);
		r = dm_tm_block_is_shared(s->tm, left_b, &left_shared);
		if (r)
			return r;

		if (!left_shared) {
			r = get_node_free_space(s->tm, left_b, &free_space);
			if (r)
				return r;

			if (free_space >= SPACE_THRESHOLD)
				return rebalance_left(s, parent_index, key);
		}
	}

	/* Should we move entries to the right sibling? */
	if (parent_index < (nr_parent - 1)) {
		dm_block_t right_b = le64_to_cpu(pn->values[parent_index + 1]);
		r = dm_tm_block_is_shared(s->tm, right_b, &right_shared);
		if (r)
			return r;

		if (!right_shared) {
			r = get_node_free_space(s->tm, right_b, &free_space);
			if (r)
				return r;

			if (free_space >= SPACE_THRESHOLD)
				return rebalance_right(s, parent_index, key);
		}
	}

        /*
         * We need to split the node.  Normally we split two nodes
         * into three, but when inserting a sequence that is either
         * monotonically increasing or decreasing it's better to split
         * a single node into two.
         */
	if (left_shared || right_shared || (nr_parent <= 2) ||
            (parent_index == 0) || (parent_index + 1 == nr_parent)) {
		return split_one_into_two(s, parent_index, key);
	} else {
		return split_two_into_three(s, parent_index, key);
	}
}

static bool has_space_for_insert(struct node_header *h, uint64_t key)
{
	if (le32_to_cpu(h->flags) & INTERNAL_NODE)
		return le32_to_cpu(h->nr_entries) < INTERNAL_NR_ENTRIES;
	else
		return le32_to_cpu(h->nr_entries) < LEAF_NR_ENTRIES;
}

/* index may be -1 if all the keys in the leaf are above the search key */
static int find_leaf_(struct shadow_spine *s, dm_block_t root, dm_block_t key, int *index)
{
	bool top = true;
	int r, i = *index;
	struct node_header *h;
	struct internal_node *n;
	uint32_t nr_entries;

	for (;;) {
		// FIXME: if we return a bool to indicate whether a copy was made,
		// then we could avoid patching the parent below.
		r = shadow_step(s, root);
		if (r < 0)
			return r;

		h = dm_block_data(shadow_current(s));

		/* patch up parent */
		if (shadow_has_parent(s)) {
			struct internal_node *pn = dm_block_data(shadow_parent(s));
			__le64 location = cpu_to_le64(dm_block_location(shadow_current(s)));
			pn->values[i] = location;
		}

		h = dm_block_data(shadow_current(s));

		if (!has_space_for_insert(h, key)) {
			if (top) {
				r = split_beneath(s, key);
			} else {
				r = rebalance_or_split(s, i, key);
			}

			if (r < 0)
				return r;

			/* making space can cause the current node to change */
			h = dm_block_data(shadow_current(s));
		}

		n = (struct internal_node *) h;
		nr_entries = le32_to_cpu(n->header.nr_entries);
		i = lower_bound(n->keys, nr_entries, key);

		if (le32_to_cpu(n->header.flags) & LEAF_NODE)
			break;

		if (i < 0) {
			/* change the bounds on the lowest key */
			n->keys[0] = cpu_to_le64(key);
			i = 0;
		}

		root = le64_to_cpu(n->values[i]);
		top = false;
	}

	*index = i;
	return 0;
}
#endif

int dm_rtree_insert(struct dm_transaction_manager *tm,
                    struct dm_space_map *data_sm,
                    dm_block_t root,
                    struct dm_mapping *value, dm_block_t *new_root, unsigned *nr_inserts)
{
	int r;
	struct insert_args args = {.tm = tm, .data_sm = data_sm, .v = value};
	struct insert_result res;
	r = insert_aux(&args, root, &res);
	if (r)
		return r;

	if (res.nr_nodes == 1) {
		*new_root = res.nodes[0].loc;

	} else {
		/* we need to create a new layer */
		struct dm_block *b;
		struct internal_node *n;

		r = dm_tm_new_block(tm, &validator, &b);
		if (r)
			return r;

		n = dm_block_data(b);
		n->header.flags = cpu_to_le32(INTERNAL_NODE);
		n->header.nr_entries = 2;
		n->keys[0] = cpu_to_le64(res.nodes[0].lowest_key);
		n->values[0] = cpu_to_le64(res.nodes[0].loc);
		n->keys[1] = cpu_to_le64(res.nodes[1].lowest_key);
		n->values[1] = cpu_to_le64(res.nodes[1].loc);

		*new_root = dm_block_location(b);
		dm_tm_unlock(tm, b);
	}

	return 0;
}
EXPORT_SYMBOL_GPL(dm_rtree_insert);

/*----------------------------------------------------------------*/

#if 0
static int remove_(struct dm_transaction_manager *tm,
                   struct dm_space_map *data_sm,
                   dm_block_t b, struct dm_block *parent, unsigned parent_index,
                   dm_block_t thin_begin, dm_block_t thin_end,
                   dm_block_t *new_root);

static void erase_internal_entry(struct internal_node *n, unsigned index)
{
	n->header.nr_entries = cpu_to_le32(le32_to_cpu(n->header.nr_entries) - 1);
	memmove(n->keys + index, n->keys + index + 1, sizeof(n->keys[0]));
	memmove(n->values + index, n->values + index + 1, sizeof(n->values[0]));
}

static void erase_leaf_entries(struct leaf_node *n, unsigned index_b, unsigned index_e)
{
	n->header.nr_entries = cpu_to_le32(le32_to_cpu(n->header.nr_entries) - (index_e - index_b));
	memmove(n->keys + index_b, n->keys + index_e, sizeof(n->keys[0]));
	memmove(n->values + index_b, n->values + index_e, sizeof(n->values[0]));
}

/*
 * We make no attempt to rebalance the nodes after the remove.  Now that
 * we're removing ranges it just gets too complicated.  Instead we'll track
 * the average residency (nr_entries, nr_internal, nr_leaf) and rebuild the
 * tree if it gets too bad.
 * 
 * If parent is 0, then there is no parent and block is the root of the tree.
 */
// FIXME: we don't need the new_root param
static int remove_internal_(struct dm_transaction_manager *tm,
                            struct dm_space_map *data_sm,
                            struct dm_block *block,
                            dm_block_t thin_begin, dm_block_t thin_end,
                            dm_block_t *new_root)
{
	struct internal_node *n = dm_block_data(block);
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);
	int r, i = lower_bound(n->keys, nr_entries, thin_begin);
	if (i < 0)
		i = 0;

	for (; i < nr_entries; i++) {
		dm_block_t key = le64_to_cpu(n->keys[i]);
		dm_block_t next_key;
		dm_block_t child;

		if (i == (nr_entries - 1)) {
			// FIXME: node_end is error prone, so I'm going to just recurse for now.
			remove_(tm, data_sm, le64_to_cpu(n->values[i]),
                                block, i, thin_begin, thin_end, new_root);

		} else {
			next_key = le64_to_cpu(n->keys[i + 1]);

			if (key >= thin_end)
				break;

			if (next_key <= thin_begin)
				continue;

			if (key >= thin_begin && next_key <= thin_end) {
				/* the whole entry is within the removal range, so we hand over to 
	                         * rtree_del.  FIXME: this mean _del can't call kmalloc, rewrite using
	                         * stack/recursion.
	                         */
	                        // FIXME: repeated moves
	  			child = le64_to_cpu(n->values[i]); 
	                        erase_internal_entry(n, i);
	                        {
		                        dm_tm_unlock(tm, block);
		                        r = dm_rtree_del(tm, data_sm, child); 
		                        if (r)
			                        return r;
	                        }
			} else {
				/* There's an overlap, recurse into the child */
				remove_(tm, data_sm, le64_to_cpu(n->values[i]),
	                                block, i,
	                                thin_begin, thin_end, new_root);
			}
		}
	}

	/* adjust the node_end */
	{
		dm_block_t node_end = le64_to_cpu(n->header.node_end);
		if ((thin_begin < node_end) && (thin_end >= node_end))
			n->header.node_end = cpu_to_le64(thin_begin);
	}

	return 0;
}

/*
 * Lot's of cases here.  An entry can be classified in relation to
 * thin_begin and thin_end:
 * 
 *   a) entirely below (many)
 *   b) overlap begin (single)
 *   c) entirely within (many)
 *   d) overlap end (single)
 *   e) overlap begin and end (single)
 *   f) entirely above (many)
 * 
 * Moving keys and values around is expensive, so we'd like to remove
 * (c) cases all in one operation.
 * 
 * (e) will cause an entry to be split into two smaller entries.  So removing
 * a range can increase the number of entries in the leaf, so we have to ensure
 * there's space before calling this.
 */
 
static int remove_leaf_(struct dm_transaction_manager *tm,
                        struct dm_space_map *data_sm,
                        struct dm_block *block,
                        dm_block_t thin_begin, dm_block_t thin_end)
{
	int i, r;
	unsigned within_start, within_end;
	dm_block_t key;
	struct disk_mapping *m;
	uint32_t len;
	struct leaf_node *n = dm_block_data(block);
	uint32_t nr_entries = le32_to_cpu(n->header.nr_entries);

	if (nr_entries == 0) {
		return 0;
	}

	i = lower_bound(n->keys, nr_entries, thin_begin);
	if (i < 0)
		i = 0;

	key = le64_to_cpu(n->keys[i]);
	m = n->values + i;
	len = le32_to_cpu(m->len);

	if (key < thin_begin && (key + len) > thin_end) {
		/* case e */
		struct dm_mapping back_half;
		back_half.thin_begin = thin_end;
		back_half.data_begin = le64_to_cpu(m->data_begin) + (thin_end - thin_begin);
		back_half.len = len - (thin_end - thin_begin);
		back_half.time = m->time;

		/* truncate the front half */
		m->len = cpu_to_le32(thin_begin - key);

		/* insert new back half entry */
		insert_into_leaf(n, i + 1, &back_half);
	} else {
		if (key + len <= thin_begin) {
			/* case a */
			i++;
		} else if ((key < thin_begin)) {
			/* case b */
			dm_block_t delta = thin_begin - key;
			dm_block_t data_begin = le64_to_cpu(m->data_begin + delta);
			dm_block_t data_end = le64_to_cpu(m->data_begin) + len;
			r = dm_sm_dec_blocks(data_sm, data_begin, data_end);
			if (r)
				return r;
			m->len = cpu_to_le32(thin_begin - key);
			i++;
		}

		/* Collect entries that are entirely within the remove range */
		within_start = i;
		for (; i < nr_entries; i++) {
			m = n->values + i;
			key = le64_to_cpu(n->keys[i]);
			len = le32_to_cpu(m->len);

			if (key + len > thin_end)
				break;

			/* case c */
			{
	                        dm_block_t data_begin = le64_to_cpu(m->data_begin);
	                        dm_block_t data_end = data_begin + len;
	                        r = dm_sm_dec_blocks(data_sm, data_begin, data_end);
	                        if (r)
		                        return r;
			}
		}
		within_end = i;

		if (within_end - within_start)
			erase_leaf_entries(n, within_start, within_end);

		if (i < nr_entries) {
			key = le64_to_cpu(n->keys[i]);
			len = le32_to_cpu(m->len);
			m = n->values + i;
			if (key < thin_end) {
				/* case d */
				pr_alert("case d");
				dm_block_t data_begin = le64_to_cpu(m->data_begin);
				r = dm_sm_dec_blocks(data_sm, data_begin, thin_end);
				if (r)
					return r;
				m->data_begin = cpu_to_le64(thin_end);
				m->len = cpu_to_le32(len - (thin_end - key));
			}
		}
	}

	/*
         * We need to reread nr_entries, since erase ops from above may have
         * changed it.
         */
        nr_entries = le32_to_cpu(n->header.nr_entries);

	/* adjust the node_end, which may have changed */
	if (nr_entries) {
		struct disk_mapping *m = n->values + nr_entries - 1;
		n->header.node_end = cpu_to_le64(le64_to_cpu(n->keys[nr_entries - 1]) + le32_to_cpu(m->len));
	}

	return 0;
}

// FIXME: removing the middle of a mapping can cause an extra entry to
// be inserted.  So we need to ensure there's enough space.
static int remove_(struct dm_transaction_manager *tm,
                   struct dm_space_map *data_sm,
                   dm_block_t b, struct dm_block *parent, unsigned parent_index,
                   dm_block_t thin_begin, dm_block_t thin_end,
                   dm_block_t *new_root)
{
	int r, inc;
	uint32_t nr_entries;
	struct node_header *h;
	struct dm_block *block;

	r = dm_tm_shadow_block(tm, b, &validator, &block, &inc);
	if (r)
		return r;

	if (inc)
		inc_children(tm, data_sm, block);

	/* patch up parent */
	if (parent) {
		struct internal_node *pn = dm_block_data(parent);
		pn->values[parent_index] = cpu_to_le64(dm_block_location(block));
	}

	h = dm_block_data(block);
	nr_entries = le32_to_cpu(h->nr_entries);

	if (le32_to_cpu(h->flags) & INTERNAL_NODE)
		r = remove_internal_(tm, data_sm, block, thin_begin, thin_end, new_root);
	else
		r = remove_leaf_(tm, data_sm, block, thin_begin, thin_end);

	if (!r && !parent)
		*new_root = dm_block_location(block);
	dm_tm_unlock(tm, block);

	return r;
}
#endif

// FIXME: we need to know how many mappings were removed.
int dm_rtree_remove(struct dm_transaction_manager *tm,
                    struct dm_space_map *data_sm,
                    dm_block_t b,
                    dm_block_t thin_begin, dm_block_t thin_end,
                    dm_block_t *new_root)
{
	return -EINVAL;
}
EXPORT_SYMBOL_GPL(dm_rtree_remove);

int dm_rtree_find_highest_key(struct dm_transaction_manager *tm, dm_block_t root,
			      dm_block_t *thin_block_result)
{
	return -EINVAL;
}
EXPORT_SYMBOL_GPL(dm_rtree_find_highest_key);

/*----------------------------------------------------------------*/
