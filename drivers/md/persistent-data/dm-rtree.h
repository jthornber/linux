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

/**
 * struct dm_mapping - Represents a mapping between a range of thin blocks and
 * a range of data blocks.
 *
 * @thin_begin: The first thin block in the range.
 * @data_begin: The first data block in the range.
 * @len: The number of blocks in the range.
 * @time: A timestamp indicating when the mapping was last modified.
 */
struct dm_mapping {
	dm_block_t thin_begin;
	dm_block_t data_begin;
	uint32_t len;
	uint32_t time;
};

/**
 * dm_rtree_empty - Set up an empty rtree.
 *
 * @tm: The transaction manager to use.
 * @root: This will be updated with the new root.
 *
 * This function sets up an empty rtree by allocating a new root
 * block and initializing it with empty nodes.
 */
int dm_rtree_empty(struct dm_transaction_manager *tm, dm_block_t * root);

/**
 * dm_rtree_del - Delete an rtree.
 *
 * @tm: The transaction manager to use.
 * @data_sm: The data space map to use.
 * @root: The root block of the rtree to delete.
 *
 * This function deletes an rtree by recursively deleting all of its nodes
 * and freeing their blocks.
 *
 * This function has O(nr nodes) complexity and can block, so it should not
 * be called on an IO path.
 */
int dm_rtree_del(struct dm_transaction_manager *tm,
		 struct dm_space_map *data_sm, dm_block_t root);

/**
 * dm_rtree_lookup - Look up a key in an rtree.
 *
 * @tm: The transaction manager to use.
 * @info: The rtree info.
 * @key: The key to look up.
 * @result: Pointer to a mapping that will be filled out if an entry is found.
 *
 * Returns:
 *  - 0 if the key is found and @value is set to the associated value
 *  - -ENODATA if the key cannot be found
 *  - other negative errno codes on other errors
 */
int dm_rtree_lookup(struct dm_transaction_manager *tm, dm_block_t root,
		    dm_block_t key, struct dm_mapping *result);

/**
 * dm_rtree_look_next - Find the first key which is not less than the given one.
 */
int dm_rtree_lookup_next(struct dm_transaction_manager *tm, dm_block_t root,
		         dm_block_t key, struct dm_mapping *result);

/**
 * dm_rtree_insert - Insert or overwrite a value in an rtree.
 *
 * @tm: The transaction manager to use.
 * @data_sm: The data space map to use.
 * @root: The root block of the rtree to insert into.
 * @value: The value to insert.
 * @new_root: Pointer to a variable that will be set to the block number of the new
 *            root block if the tree grows.
 * @nr_inserts: Pointer to a variable that will be incremented if a new value
 *              is inserted.
 */
int dm_rtree_insert(struct dm_transaction_manager *tm,
		    struct dm_space_map *data_sm, dm_block_t root,
		    struct dm_mapping *value, dm_block_t * new_root,
		    unsigned *nr_inserts);

/**
 * dm_rtree_remove - Remove a range of keys from an rtree.
 *
 * @tm: The transaction manager to use.
 * @data_sm: The data space map to use.
 * @root: The root block of the rtree to remove keys from.
 * @thin_begin: The first thin block in the range to remove.
 * @thin_end: The last thin block in the range to remove.
 * @new_root: Pointer to a variable that will be set to the block number of the new
 *            root block if the tree shrinks.
 */
int dm_rtree_remove(struct dm_transaction_manager *tm,
		    struct dm_space_map *data_sm, dm_block_t root,
		    dm_block_t thin_begin, dm_block_t thin_end,
		    dm_block_t * new_root);

/**
 * dm_rtree_find_highest_key - Find the highest key in an rtree.
 *
 * @tm: The transaction manager to use.
 * @root: The root block of the rtree to search.
 * @thin_block_result: Pointer to a variable that will be set to the highest thin
 *                     block in the rtree.
 *
 * Returns:
 *  - The number of key entries that have been filled out, or 0 if the tree is empty.
 *  - Negative errno codes on error.
 */
int dm_rtree_find_highest_key(struct dm_transaction_manager *tm,
			      dm_block_t root, dm_block_t * thin_block_result);

/*----------------------------------------------------------------*/

#endif				/* _LINUX_DM_RTREE_H */
