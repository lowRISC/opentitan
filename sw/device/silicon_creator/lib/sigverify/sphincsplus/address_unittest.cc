// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"

#include <array>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace spx_addr_unittest {
namespace {

class SpxAddrTest : public rom_test::RomTest {
 protected:
  /**
   * Fetch a specific byte from the internal address buffer.
   *
   * @param addr Hypertree address.
   * @param offset Index of byte to get.
   * @return Value of the byte within the internal buffer.
   */
  uint8_t ByteGet(const spx_addr_t *addr, size_t offset) {
    unsigned char *buf = (unsigned char *)addr->addr;
    return buf[offset];
  }

  /**
   * Get the 64-bit `tree` field from the address.
   *
   * @param addr Hypertree address.
   * @return Value of the `tree` field.
   */
  uint64_t TreeGet(const spx_addr_t *addr) {
    unsigned char *buf = (unsigned char *)addr->addr;
    uint64_t tree = 0;
    memcpy(&tree, buf + kSpxOffsetTree, sizeof(uint64_t));
    return tree;
  }

  /**
   * Get the 32-bit `tree_index` field from the address.
   *
   * @param addr Hypertree address.
   * @return Value of the `tree_index` field.
   */
  uint32_t TreeIndexGet(const spx_addr_t *addr) {
    unsigned char *buf = (unsigned char *)addr->addr;
    uint32_t tree_index = 0;
    memcpy(&tree_index, buf + kSpxOffsetTreeIndex, sizeof(uint32_t));
    return tree_index;
  }

  /**
   * Checks if the given byte is the same in two addresses.
   *
   * @param addr1 First address.
   * @param addr2 Second address.
   * @param offset Index of byte to check.
   */
  void ExpectByteEq(const spx_addr_t *addr1, const spx_addr_t *addr2,
                    size_t offset) {
    EXPECT_EQ(ByteGet(addr1, offset), ByteGet(addr2, offset));
  }

  /**
   * Checks if the two addresses are exactly equal.
   *
   * @param addr1 First address.
   * @param addr2 Second address.
   * @param offset Index of byte to check.
   */
  void ExpectAddrEq(const spx_addr_t *addr1, const spx_addr_t *addr2) {
    EXPECT_EQ(memcmp(addr1->addr, addr2->addr, sizeof(addr1->addr)), 0);
  }

  /**
   * Initializes a default test address.
   *
   * The test address is chosen so that all bytes are distinct. This way, if
   * some address routine mistakenly writes or copies the wrong byte, it will
   * be more obvious than, for instance, if most bytes were 0.
   */
  void TestAddrInit(spx_addr_t *addr) {
    // Test assumption.
    EXPECT_LE(sizeof(addr->addr), UINT8_MAX);

    unsigned char *buf = (unsigned char *)addr->addr;
    for (size_t i = 0; i < sizeof(addr->addr); i++) {
      buf[i] = UINT8_MAX - i;
    }
  }

  bool two_byte_keypair_ = (kSpxFullHeight / kSpxD) > 8;
};

TEST_F(SpxAddrTest, LayerSetTest) {
  uint8_t layer = 0xf0;
  spx_addr_t test_addr;
  TestAddrInit(&test_addr);
  spx_addr_layer_set(&test_addr, layer);
  EXPECT_EQ(ByteGet(&test_addr, kSpxOffsetLayer), layer);
}

TEST_F(SpxAddrTest, TreeSetTest) {
  uint64_t tree = 0x0102030405060708;
  // Same data in big-endian form.
  uint64_t tree_be = 0x0807060504030201;
  spx_addr_t test_addr;
  TestAddrInit(&test_addr);
  spx_addr_tree_set(&test_addr, tree);

  // Expect the tree to be in big-endian form.
  EXPECT_EQ(TreeGet(&test_addr), tree_be);
}

TEST_F(SpxAddrTest, TypeSetTest) {
  spx_addr_t test_addr;
  TestAddrInit(&test_addr);

  // Set the type and check its value.
  spx_addr_type_set(&test_addr, kSpxAddrTypeWotsPk);
  EXPECT_EQ(ByteGet(&test_addr, kSpxOffsetType), kSpxAddrTypeWotsPk);

  // Set and check a second time.
  spx_addr_type_set(&test_addr, kSpxAddrTypeHashTree);
  EXPECT_EQ(ByteGet(&test_addr, kSpxOffsetType), kSpxAddrTypeHashTree);
}

TEST_F(SpxAddrTest, SubtreeCopyTest) {
  spx_addr_t src_addr;
  TestAddrInit(&src_addr);
  spx_addr_t dest_addr = {.addr = {1, 2, 3, 4, 5, 6, 7, 8}};

  // Make a copy of `dest_addr` to preserve the original values.
  spx_addr_t dest_addr_orig;
  memcpy(dest_addr_orig.addr, dest_addr.addr, sizeof(dest_addr.addr));

  // Copy subtree.
  spx_addr_subtree_copy(&dest_addr, &src_addr);

  // After copying, the layer and tree should match.
  ExpectByteEq(&dest_addr, &src_addr, kSpxOffsetLayer);
  EXPECT_EQ(TreeGet(&dest_addr), TreeGet(&src_addr));

  // Other fields be unmodified.
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetType);
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetKpAddr2);
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetKpAddr1);
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetChainAddr);
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetHashAddr);
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetTreeHeight);
  EXPECT_EQ(TreeIndexGet(&dest_addr), TreeIndexGet(&dest_addr_orig));
}

TEST_F(SpxAddrTest, SubtreeCopySelf) {
  spx_addr_t test_addr;
  TestAddrInit(&test_addr);

  // Make a copy to preserve the original values.
  spx_addr_t test_addr_orig;
  memcpy(test_addr_orig.addr, test_addr.addr, sizeof(test_addr.addr));

  // Copy subtree.
  spx_addr_subtree_copy(&test_addr, &test_addr);

  // After copying, the entire underlying buffer should match the original.
  ExpectAddrEq(&test_addr, &test_addr_orig);
}

TEST_F(SpxAddrTest, KeypairSetTest) {
  spx_addr_t test_addr;
  TestAddrInit(&test_addr);

  // Set keypair.
  spx_addr_keypair_set(&test_addr, 0xffaa);

  // Check result.
  EXPECT_EQ(ByteGet(&test_addr, kSpxOffsetKpAddr1), 0xaa);
  if (two_byte_keypair_) {
    EXPECT_EQ(ByteGet(&test_addr, kSpxOffsetKpAddr2), 0xff);
  }
}

TEST_F(SpxAddrTest, ChainSetTest) {
  uint8_t chain = 0xf0;
  spx_addr_t test_addr;
  TestAddrInit(&test_addr);

  // Set chain and check result.
  spx_addr_chain_set(&test_addr, chain);
  EXPECT_EQ(ByteGet(&test_addr, kSpxOffsetChainAddr), chain);
}

TEST_F(SpxAddrTest, HashSetTest) {
  uint8_t hash = 0xf0;
  spx_addr_t test_addr;
  TestAddrInit(&test_addr);

  // Set hash and check result.
  spx_addr_hash_set(&test_addr, hash);
  EXPECT_EQ(ByteGet(&test_addr, kSpxOffsetHashAddr), hash);
}

TEST_F(SpxAddrTest, KeypairCopyTest) {
  spx_addr_t src_addr;
  TestAddrInit(&src_addr);
  spx_addr_t dest_addr = {.addr = {1, 2, 3, 4, 5, 6, 7, 8}};

  // Make a copy of `dest_addr` to preserve the original values.
  spx_addr_t dest_addr_orig;
  memcpy(dest_addr_orig.addr, dest_addr.addr, sizeof(dest_addr.addr));

  // Copy subtree.
  spx_addr_keypair_copy(&dest_addr, &src_addr);

  // After copying, the layer and tree should match.
  ExpectByteEq(&dest_addr, &src_addr, kSpxOffsetLayer);
  EXPECT_EQ(TreeGet(&dest_addr), TreeGet(&src_addr));

  // After copying, the 1-2 keypair bytes should match.
  ExpectByteEq(&dest_addr, &src_addr, kSpxOffsetKpAddr1);
  if (two_byte_keypair_) {
    ExpectByteEq(&dest_addr, &src_addr, kSpxOffsetKpAddr2);
  }

  // Other fields be unmodified.
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetType);
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetChainAddr);
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetHashAddr);
  ExpectByteEq(&dest_addr, &dest_addr_orig, kSpxOffsetTreeHeight);
  EXPECT_EQ(TreeIndexGet(&dest_addr), TreeIndexGet(&dest_addr_orig));
}

TEST_F(SpxAddrTest, TreeHeightSetTest) {
  uint8_t tree_height = 0xf0;
  spx_addr_t test_addr;
  TestAddrInit(&test_addr);

  // Set tree height and check result.
  spx_addr_tree_height_set(&test_addr, tree_height);
  EXPECT_EQ(ByteGet(&test_addr, kSpxOffsetTreeHeight), tree_height);
}

TEST_F(SpxAddrTest, TreeIndexSetTest) {
  uint32_t tree_index = 0x01020304;
  // Same data in big-endian form.
  uint32_t tree_index_be = 0x04030201;
  spx_addr_t test_addr;
  TestAddrInit(&test_addr);

  // Set tree index and check result.
  spx_addr_tree_index_set(&test_addr, tree_index);
  EXPECT_EQ(TreeIndexGet(&test_addr), tree_index_be);
}

}  // namespace
}  // namespace spx_addr_unittest
