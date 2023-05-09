// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Derived from code in the SPHINCS+ reference implementation (CC0 license):
// https://github.com/sphincs/sphincsplus/blob/ed15dd78658f63288c7492c00260d86154b84637/ref/address.h

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"

static_assert(kSpxTreeHeight * (kSpxD - 1) <= 64,
              "Subtree addressing is currently limited to at most 2^64 trees.");

// Specifies whether we need one or two bytes to represent the keypair.
#define SPX_ADDR_TWO_BYTE_KEYPAIR ((kSpxFullHeight / kSpxD) > 8)

/**
 * Sets a single byte within the internal buffer of an address.
 *
 * Use with the `kSpxOffset...` constant offsets.
 *
 * @param addr Adress in which to set a byte.
 * @param offset Byte-offset within the internal buffer.
 * @param value New value of byte.
 */
static void spx_addr_set_byte(spx_addr_t *addr, size_t offset,
                              unsigned char value) {
  unsigned char *buf = (unsigned char *)addr->addr;
  buf[offset] = value;
}

void spx_addr_layer_set(spx_addr_t *addr, uint8_t layer) {
  spx_addr_set_byte(addr, kSpxOffsetLayer, layer);
}

void spx_addr_tree_set(spx_addr_t *addr, uint64_t tree) {
  unsigned char *buf = (unsigned char *)addr->addr;
  // Reverse bytes in the integer so it will appear in big-endian form.
  uint64_t tree_be = __builtin_bswap64(tree);
  memcpy(buf + kSpxOffsetTree, &tree_be, sizeof(uint64_t));
}

void spx_addr_type_set(spx_addr_t *addr, spx_addr_type_t type) {
  spx_addr_set_byte(addr, kSpxOffsetType, (unsigned char)type);
}

void spx_addr_subtree_copy(spx_addr_t *out, const spx_addr_t *in) {
  unsigned char *in_buf = (unsigned char *)in->addr;
  unsigned char *out_buf = (unsigned char *)out->addr;

  // Copy the entire 32-bit field representing the layer, even though only one
  // byte is used.
  size_t layer_field_offset =
      (kSpxOffsetLayer / sizeof(uint32_t)) * sizeof(uint32_t);
  memcpy(out_buf + layer_field_offset, in_buf + layer_field_offset,
         sizeof(uint32_t));

  // Copy the entire 64-bit field representing the tree.
  memcpy(out_buf + kSpxOffsetTree, in_buf + kSpxOffsetTree, sizeof(uint64_t));
}

void spx_addr_keypair_set(spx_addr_t *addr, uint32_t keypair) {
  spx_addr_set_byte(addr, kSpxOffsetKpAddr1, (keypair & 0xff));
  if (SPX_ADDR_TWO_BYTE_KEYPAIR) {
    spx_addr_set_byte(addr, kSpxOffsetKpAddr2, ((keypair >> 8) & 0xff));
  }
}

void spx_addr_keypair_copy(spx_addr_t *out, const spx_addr_t *in) {
  spx_addr_subtree_copy(out, in);
  unsigned char *in_buf = (unsigned char *)in->addr;
  spx_addr_set_byte(out, kSpxOffsetKpAddr1, in_buf[kSpxOffsetKpAddr1]);
  if (SPX_ADDR_TWO_BYTE_KEYPAIR) {
    spx_addr_set_byte(out, kSpxOffsetKpAddr2, in_buf[kSpxOffsetKpAddr2]);
  }
}

void spx_addr_chain_set(spx_addr_t *addr, uint8_t chain) {
  spx_addr_set_byte(addr, kSpxOffsetChainAddr, chain);
}

void spx_addr_hash_set(spx_addr_t *addr, uint8_t hash) {
  spx_addr_set_byte(addr, kSpxOffsetHashAddr, hash);
}

void spx_addr_tree_height_set(spx_addr_t *addr, uint8_t tree_height) {
  spx_addr_set_byte(addr, kSpxOffsetTreeHeight, tree_height);
}

void spx_addr_tree_index_set(spx_addr_t *addr, uint32_t tree_index) {
  unsigned char *buf = (unsigned char *)addr->addr;
  // Reverse bytes in the integer so it will appear in big-endian form.
  uint32_t index_be = __builtin_bswap32(tree_index);
  memcpy(buf + kSpxOffsetTreeIndex, &index_be, sizeof(uint32_t));
}
