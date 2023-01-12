// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/address.h
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_ADDRESS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_ADDRESS_H_

/**
 * This file provides an interface for working with SPHINCS+ hypertree
 * addresses. For details, see section 2.7.3 of the round 3.1 SPHINCS+ NIST
 * competition submission:
 *    https://sphincs.org/data/sphincs+-r3.1-specification.pdf
 *
 * Quick overview based on that document:
 * - All addresses are 256 bits (= 8 32-bit words).
 * - Numeric fields are stored in big-endian form.
 * - Addresses have five different formats depending on their use case.
 * - Three fields are shared across all formats (layer, tree, and type).
 *   - The type field indicates which format the address uses.
 * - All fields are aligned to 32-bit word boundaries within the address
 *   (meaning some are oversized for the data they contain).
 *
 * Common format of addresses:
 * +---------+---------------+--------------+
 * | size    | field         | address bits |
 * +=========+===============+==============+
 * | 8 bits  | layer address | 0..31        |
 * +---------+---------------+--------------+
 * | 64 bits | tree address  | 32..127      |
 * +---------+---------------+--------------+
 * | 8 bits  | type          | 128..159     |
 * +---------+---------------+--------------+
 * | 96 bits | flexible      | 160..255     |
 * |         | (see below)   |              |
 * +---------+---------------+--------------+
 *
 * WOTS+ hash address flexible fields:
 * +---------+------------------+----------+
 * | 16 bits | key pair address | 160..191 |
 * +---------+------------------+----------+
 * | 8 bits  | chain address    | 192..223 |
 * +---------+------------------+----------+
 * | 8 bits  | hash address     | 224..255 |
 * +---------+------------------+----------+
 *
 * WOTS+ public key compression flexible fields:
 * +---------+-------------------+----------+
 * | 16 bits | key pair address  | 160..191 |
 * +---------+-------------------+----------+
 * | 64 bits | unused (always 0) | 192..255 |
 * +---------+-------------------+----------+
 *
 * Main Merkle tree flexible fields:
 * +---------+-------------------+----------+
 * | 32 bits | unused (always 0) | 160..191 |
 * +---------+-------------------+----------+
 * | 8 bits  | tree height       | 192..223 |
 * +---------+-------------------+----------+
 * | 32 bits | tree index        | 224..255 |
 * +---------+-------------------+----------+
 *
 * FORS hash address flexible fields:
 * +---------+------------------+----------+
 * | 16 bits | key pair address | 160..191 |
 * +---------+------------------+----------+
 * | 8 bits  | tree height      | 192..223 |
 * +---------+------------------+----------+
 * | 32 bits | tree index       | 224..255 |
 * +---------+------------------+----------+
 *
 * FORS tree root compression flexible fields:
 * +---------+-------------------+----------+
 * | 16 bits | key pair address  | 160..191 |
 * +---------+-------------------+----------+
 * | 64 bits | unused (always 0) | 192..255 |
 * +---------+-------------------+----------+
 */

#include <stdint.h>

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Hash types for `spx_addr_type_set`.
 *
 * Note: The values here are more like compile-time constants than true enums;
 * changing the values will cause test failures since they are hashed directly
 * as part of the address.
 */
typedef enum spx_addr_type {
  kSpxAddrTypeWots = 0,
  kSpxAddrTypeWotsPk = 1,
  kSpxAddrTypeHashTree = 2,
  kSpxAddrTypeForsTree = 3,
  kSpxAddrTypeForsPk = 4,
  kSpxAddrTypeWotsPrf = 5,
  kSpxAddrTypeForsPrf = 6,
} spx_addr_type_t;

/**
 * Hypertree address.
 */
typedef struct spx_addr {
  uint32_t addr[8];
} spx_addr_t;

/**
 * Set the layer field in a hypertree address.
 *
 * Appears in reference code as `set_layer_addr`.
 *
 * @param addr Hypertree address.
 * @param layer Layer value to set in the address.
 */
void spx_addr_layer_set(spx_addr_t *addr, uint8_t layer);

/**
 * Set the tree field for a hypertree address.
 *
 * The `tree` value will be converted to big-endian form before being stored in
 * the address.
 *
 * Appears in reference code as `set_tree_addr`.
 *
 * @param addr Hypertree address.
 * @param tree Tree value to set in the address.
 */
void spx_addr_tree_set(spx_addr_t *addr, uint64_t tree);

/**
 * Set the type field for a hypertree address.
 *
 * Appears in reference code as `set_type_addr`.
 *
 * @param addr Hypertree address.
 * @param type Type value to set in the address.
 */
void spx_addr_type_set(spx_addr_t *addr, spx_addr_type_t type);

/**
 * Copies the layer and tree parts of one address into the other.
 *
 * This is used to do multiple types of hashes within the same Merkle tree.
 *
 * Appears in reference code as `copy_subtree_addr`.
 *
 * @param out Address to copy to.
 * @param in Address to copy from.
 */
void spx_addr_subtree_copy(spx_addr_t *out, const spx_addr_t *in);

/**
 * Set the keypair field of a WOTS or FORS address.
 *
 * Appears in reference code as `set_keypair_addr`.
 *
 * @param addr Hypertree address.
 * @param keypair Keypair value to set in the address.
 */
void spx_addr_keypair_set(spx_addr_t *addr, uint32_t keypair);

/**
 * Set the chain field of a WOTS or FORS address.
 *
 * Appears in reference code as `set_chain_addr`.
 *
 * @param addr Hypertree address.
 * @param chain Chain value to set in the address.
 */
void spx_addr_chain_set(spx_addr_t *addr, uint8_t chain);

/**
 * Set the hash field of a WOTS or FORS address.
 *
 * Appears in reference code as `set_hash_addr`.
 *
 * @param addr Hypertree address.
 * @param hash Hash value to set in the address.
 */
void spx_addr_hash_set(spx_addr_t *addr, uint8_t hash);

/**
 * Copies the layer, tree, and keypair parts of a WOTS or FORS address.
 *
 * This is used to do multiple things with the same OTS keypair.
 *
 * Appears in reference code as `copy_keypair_addr`.
 *
 * @param out Address to copy to.
 * @param in Address to copy from.
 */
void spx_addr_keypair_copy(spx_addr_t *out, const spx_addr_t *in);

/**
 * Set the tree height field of a hash tree address.
 *
 * Appears in reference code as `set_tree_height`.
 *
 * @param addr Hypertree address.
 * @param tree_height Tree height value to set in the address.
 */
void spx_addr_tree_height_set(spx_addr_t *addr, uint8_t tree_height);

/**
 * Set the tree index field of a hash tree address.
 *
 * The `tree_index` value will be converted to big-endian form before being
 * stored in the address.
 *
 * Appears in reference code as `set_tree_index`.
 *
 * @param addr Hypertree address.
 * @param tree_index Tree index value to set in the address.
 */
void spx_addr_tree_index_set(spx_addr_t *addr, uint32_t tree_index);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SIGVERIFY_SPHINCSPLUS_ADDRESS_H_
