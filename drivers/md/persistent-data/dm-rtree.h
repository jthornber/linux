/*
 * Copyright (C) 2021 Red Hat, Inc.
 *
 * This file is released under the GPL.
 */
#ifndef _LINUX_DM_RTREE_H
#define _LINUX_DM_RTREE_H

#include "dm-block-manager.h"
#include "dm-transaction-manager.h"

/*----------------------------------------------------------------*/

struct dm_mapping {
	dm_block_t thin_begin;
	dm_block_t data_begin;
	uint32_t len;
	uint32_t time;
};

/*
 * Set up an empty tree.  O(1).
 */
int dm_rtree_empty(struct dm_transaction_manager *tm, dm_block_t *root);

/*
 * Delete a tree.  O(n) - this is the slow one!  It can also block, so
 * please don't call it on an IO path.
 */
int dm_rtree_del(struct dm_transaction_manager *tm,
                 struct dm_space_map *data_sm, dm_block_t root);

/*
 * All the lookup functions return -ENODATA if the key cannot be found.
 */

/*
 * Tries to find a key that matches exactly.  O(ln(n))
 */
int dm_rtree_lookup(struct dm_transaction_manager *tm, dm_block_t root,
                    dm_block_t key,
                    struct dm_mapping *result);

/*
 * Insertion (or overwrite an existing value).  O(ln(n))
 */
int dm_rtree_insert(struct dm_transaction_manager *tm,
                    struct dm_space_map *data_sm,
                    dm_block_t root,
                    struct dm_mapping *value,
                    dm_block_t *new_root,
                    unsigned *nr_inserts);

/*
 * Remove a key if present.  O(ln(n)).
 */
int dm_rtree_remove(struct dm_transaction_manager *tm,
                    struct dm_space_map *data_sm,
                    dm_block_t root,
                    dm_block_t thin_begin, dm_block_t thin_end,
                    dm_block_t *new_root); 

/*
 * Returns < 0 on failure.  Otherwise the number of key entries that have
 * been filled out.  Remember trees can have zero entries, and as such have
 * no highest key.
 */
int dm_rtree_find_highest_key(struct dm_transaction_manager *tm, dm_block_t root,
			      dm_block_t *thin_block_result);

/*----------------------------------------------------------------*/

#endif	/* _LINUX_DM_RTREE_H */
