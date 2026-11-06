// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/fips_kat_table.h"

#include <sys/mman.h>
#include <unistd.h>

#include "gtest/gtest.h"

namespace {

// Helper struct for a table with 2 entries and attached payload data.
struct TestTableLayout {
  struct {
    uint32_t magic;
    uint32_t version;
    uint32_t entry_count;
    uint32_t total_size;
    fips_kat_entry_t entries[2];
  } table;

  struct {
    uint32_t key_len;
    uint32_t msg_len;
    uint32_t digest_len;
    uint8_t data[35];
    uint8_t padding[1];
  } sha256;

  struct {
    uint32_t key_len;
    uint32_t iv_len;
    uint32_t aad_len;
    uint32_t pt_len;
    uint32_t ct_len;
    uint32_t tag_len;
    uint8_t data[80];
  } aes;
};

class FipsKatTableTest : public ::testing::Test {
 protected:
  void *mmap_base_ = MAP_FAILED;

  void SetUp() override {
    // Map memory covering FIPS_KAT_DESCRIPTOR_PTR_ADDR (0x6FF7C) on host for
    // testing get_fips_descriptor_table().
    mmap_base_ =
        mmap(reinterpret_cast<void *>(0x40000), 0x30000, PROT_READ | PROT_WRITE,
             MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
  }

  void TearDown() override {
    if (mmap_base_ != MAP_FAILED) {
      munmap(mmap_base_, 0x30000);
      mmap_base_ = MAP_FAILED;
    }
  }

  void SetDescriptorPointer(const fips_kat_descriptor_table_t *table) {
    if (mmap_base_ != MAP_FAILED) {
      *reinterpret_cast<const fips_kat_descriptor_table_t **>(
          FIPS_KAT_DESCRIPTOR_PTR_ADDR) = table;
    }
  }
};

TEST_F(FipsKatTableTest, ValidateTableSuccess) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 2;
  layout.table.total_size = sizeof(layout);

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);

  // Test get_fips_descriptor_table_from_address directly
  const fips_kat_descriptor_table_t *ptr = table;
  EXPECT_EQ(
      get_fips_descriptor_table_from_address(reinterpret_cast<uintptr_t>(&ptr)),
      table);

  // Test get_fips_descriptor_table() via mapped pointer slot
  if (mmap_base_ != MAP_FAILED) {
    SetDescriptorPointer(table);
    EXPECT_EQ(get_fips_descriptor_table(), table);
  }
}

TEST_F(FipsKatTableTest, ValidateTableInvalidMagic) {
  TestTableLayout layout{};
  layout.table.magic = 0x12345678;  // Invalid magic
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_descriptor_table_t *ptr = table;
  EXPECT_EQ(
      get_fips_descriptor_table_from_address(reinterpret_cast<uintptr_t>(&ptr)),
      nullptr);

  if (mmap_base_ != MAP_FAILED) {
    SetDescriptorPointer(table);
    EXPECT_EQ(get_fips_descriptor_table(), nullptr);
  }
}

TEST_F(FipsKatTableTest, ValidateTableInvalidVersion) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = 2;  // Unsupported version
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_descriptor_table_t *ptr = table;
  EXPECT_EQ(
      get_fips_descriptor_table_from_address(reinterpret_cast<uintptr_t>(&ptr)),
      nullptr);

  if (mmap_base_ != MAP_FAILED) {
    SetDescriptorPointer(table);
    EXPECT_EQ(get_fips_descriptor_table(), nullptr);
  }
}

TEST_F(FipsKatTableTest, ValidateTableZeroTotalSize) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = 0;  // Invalid size

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_descriptor_table_t *ptr = table;
  EXPECT_EQ(
      get_fips_descriptor_table_from_address(reinterpret_cast<uintptr_t>(&ptr)),
      nullptr);

  if (mmap_base_ != MAP_FAILED) {
    SetDescriptorPointer(table);
    EXPECT_EQ(get_fips_descriptor_table(), nullptr);
  }
}

TEST_F(FipsKatTableTest, ValidateTableTotalSizeTooSmall) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(fips_kat_descriptor_table_t) - 1;

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_descriptor_table_t *ptr = table;
  EXPECT_EQ(
      get_fips_descriptor_table_from_address(reinterpret_cast<uintptr_t>(&ptr)),
      nullptr);
}

TEST_F(FipsKatTableTest, ValidateTableExcessiveEntryCount) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);
  uint32_t max_entries =
      (layout.table.total_size - sizeof(fips_kat_descriptor_table_t)) /
      sizeof(fips_kat_entry_t);
  layout.table.entry_count = max_entries + 1;

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_descriptor_table_t *ptr = table;
  EXPECT_EQ(
      get_fips_descriptor_table_from_address(reinterpret_cast<uintptr_t>(&ptr)),
      nullptr);
}

TEST_F(FipsKatTableTest, ValidateTableUnalignedPointerSlot) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  const fips_kat_descriptor_table_t *ptr =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  uintptr_t addr = reinterpret_cast<uintptr_t>(&ptr);
  EXPECT_EQ(get_fips_descriptor_table_from_address(addr + 1), nullptr);
  EXPECT_EQ(get_fips_descriptor_table_from_address(addr + 2), nullptr);
  EXPECT_EQ(get_fips_descriptor_table_from_address(addr + 3), nullptr);
}

TEST_F(FipsKatTableTest, ValidateTableUnalignedTablePointer) {
  alignas(uint32_t) uint8_t buffer[sizeof(TestTableLayout) + 4];
  uintptr_t aligned_addr = (reinterpret_cast<uintptr_t>(buffer) + 3) & ~3ULL;
  uintptr_t unaligned_addr = aligned_addr + 1;

  auto *unaligned_table =
      reinterpret_cast<fips_kat_descriptor_table_t *>(unaligned_addr);
  unaligned_table->magic = kFipsKatDescriptorMagic;
  unaligned_table->version = kFipsKatDescriptorVersion1;
  unaligned_table->entry_count = 1;
  unaligned_table->total_size = sizeof(TestTableLayout);

  const fips_kat_descriptor_table_t *ptr = unaligned_table;
  EXPECT_EQ(
      get_fips_descriptor_table_from_address(reinterpret_cast<uintptr_t>(&ptr)),
      nullptr);
}

TEST_F(FipsKatTableTest, ValidateTableNullPointerSlot) {
  EXPECT_EQ(get_fips_descriptor_table_from_address(0), nullptr);

  if (mmap_base_ != MAP_FAILED) {
    SetDescriptorPointer(nullptr);
    EXPECT_EQ(get_fips_descriptor_table(), nullptr);
  }
}

TEST(FipsKatTableSearchTest, FindEntry) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 2;
  layout.table.total_size = sizeof(layout);

  layout.table.entries[0].algorithm_id = kFipsKatAlgSha2_256;
  layout.table.entries[0].offset = offsetof(TestTableLayout, sha256);
  layout.table.entries[0].size = sizeof(layout.sha256);

  layout.table.entries[1].algorithm_id = kFipsKatAlgAesEcb256Decrypt;
  layout.table.entries[1].offset = offsetof(TestTableLayout, aes);
  layout.table.entries[1].size = sizeof(layout.aes);

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);

  // Find existing entries
  const fips_kat_entry_t *entry_sha =
      find_fips_entry(table, kFipsKatAlgSha2_256);
  ASSERT_NE(entry_sha, nullptr);
  EXPECT_EQ(entry_sha->algorithm_id, kFipsKatAlgSha2_256);
  EXPECT_EQ(entry_sha->offset, offsetof(TestTableLayout, sha256));

  const fips_kat_entry_t *entry_aes =
      find_fips_entry(table, kFipsKatAlgAesEcb256Decrypt);
  ASSERT_NE(entry_aes, nullptr);
  EXPECT_EQ(entry_aes->algorithm_id, kFipsKatAlgAesEcb256Decrypt);
  EXPECT_EQ(entry_aes->offset, offsetof(TestTableLayout, aes));

  // Non-existent algorithm
  EXPECT_EQ(find_fips_entry(table, kFipsKatAlgSha2_512), nullptr);
  EXPECT_EQ(find_fips_entry(table, kFipsKatAlgNone), nullptr);

  // Null table
  EXPECT_EQ(find_fips_entry(nullptr, kFipsKatAlgSha2_256), nullptr);
}

TEST(FipsKatTableSearchTest, DefensiveChecks) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 2;
  layout.table.total_size = sizeof(layout);
  layout.table.entries[0].algorithm_id = kFipsKatAlgSha2_256;

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);

  // Unaligned table pointer
  const auto *unaligned_table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(
          reinterpret_cast<uintptr_t>(table) + 1);
  EXPECT_EQ(find_fips_entry(unaligned_table, kFipsKatAlgSha2_256), nullptr);

  // total_size too small
  layout.table.total_size = sizeof(fips_kat_descriptor_table_t) - 1;
  EXPECT_EQ(find_fips_entry(table, kFipsKatAlgSha2_256), nullptr);

  // entry_count exceeds capacity of total_size
  layout.table.total_size = sizeof(layout);
  uint32_t max_entries =
      (layout.table.total_size - sizeof(fips_kat_descriptor_table_t)) /
      sizeof(fips_kat_entry_t);
  layout.table.entry_count = max_entries + 1;
  EXPECT_EQ(find_fips_entry(table, kFipsKatAlgSha2_256), nullptr);
}

TEST(FipsKatTableDataTest, GetDataSuccess) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  layout.table.entries[0].algorithm_id = kFipsKatAlgSha2_256;
  layout.table.entries[0].offset = offsetof(TestTableLayout, sha256);
  layout.table.entries[0].size = sizeof(layout.sha256);

  layout.sha256.key_len = 0;
  layout.sha256.msg_len = 3;
  layout.sha256.digest_len = 32;
  layout.sha256.data[0] = 'a';
  layout.sha256.data[1] = 'b';
  layout.sha256.data[2] = 'c';

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgSha2_256);
  ASSERT_NE(entry, nullptr);

  const void *data = get_fips_data(table, entry);
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data, reinterpret_cast<const void *>(&layout.sha256));

  const auto *hmac_data = static_cast<const hmac_kat_data_t *>(data);
  EXPECT_EQ(hmac_data->key_len, 0);
  EXPECT_EQ(hmac_data->msg_len, 3);
  EXPECT_EQ(hmac_data->digest_len, 32);
  EXPECT_EQ(hmac_data->data[0], 'a');
  EXPECT_EQ(hmac_data->data[1], 'b');
  EXPECT_EQ(hmac_data->data[2], 'c');
}

TEST(FipsKatTableDataTest, GetEcdhDataSuccess) {
  struct Layout {
    struct {
      uint32_t magic;
      uint32_t version;
      uint32_t entry_count;
      uint32_t total_size;
      fips_kat_entry_t entries[1];
    } table;
    struct {
      uint32_t priv_key_len;
      uint32_t pub_key_len1;
      uint32_t pub_key_len2;
      uint32_t shared_secret_len;
      uint8_t data[128];
    } ecdh;
  } layout{};

  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  layout.table.entries[0].algorithm_id = kFipsKatAlgEcdhP256;
  layout.table.entries[0].offset = offsetof(Layout, ecdh);
  layout.table.entries[0].size = sizeof(layout.ecdh);

  layout.ecdh.priv_key_len = 32;
  layout.ecdh.pub_key_len1 = 32;
  layout.ecdh.pub_key_len2 = 32;
  layout.ecdh.shared_secret_len = 32;
  layout.ecdh.data[0] = 0x71;

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgEcdhP256);
  ASSERT_NE(entry, nullptr);

  const void *data = get_fips_data(table, entry);
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data, reinterpret_cast<const void *>(&layout.ecdh));

  const auto *ecdh_data = static_cast<const ecdh_kat_data_t *>(data);
  EXPECT_EQ(ecdh_data->priv_key_len, 32);
  EXPECT_EQ(ecdh_data->pub_key_len1, 32);
  EXPECT_EQ(ecdh_data->pub_key_len2, 32);
  EXPECT_EQ(ecdh_data->shared_secret_len, 32);
  EXPECT_EQ(ecdh_data->data[0], 0x71);
}

TEST(FipsKatTableDataTest, GetDataMldsa87) {
  struct Layout {
    struct {
      uint32_t magic;
      uint32_t version;
      uint32_t entry_count;
      uint32_t total_size;
      fips_kat_entry_t entries[1];
    } table;
    mldsa_kat_data_t mldsa;
  } layout{};

  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  layout.table.entries[0].algorithm_id = kFipsKatAlgMldsa87;
  layout.table.entries[0].offset = offsetof(Layout, mldsa);
  layout.table.entries[0].size = sizeof(layout.mldsa);

  layout.mldsa.num_cases = 5;
  layout.mldsa.cases[0].seed[0] = 0x0D;
  layout.mldsa.cases[0].mprime[0] = 0x3A;
  layout.mldsa.cases[0].expected_sig_hash[0] = 0x50;

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgMldsa87);
  ASSERT_NE(entry, nullptr);

  const void *data = get_fips_data(table, entry);
  ASSERT_NE(data, nullptr);
  EXPECT_EQ(data, reinterpret_cast<const void *>(&layout.mldsa));

  const auto *mldsa_data = static_cast<const mldsa_kat_data_t *>(data);
  EXPECT_EQ(mldsa_data->num_cases, 5);
  EXPECT_EQ(mldsa_data->cases[0].seed[0], 0x0D);
  EXPECT_EQ(mldsa_data->cases[0].mprime[0], 0x3A);
  EXPECT_EQ(mldsa_data->cases[0].expected_sig_hash[0], 0x50);
}

TEST(FipsKatTableBoundsCheckTest, RejectOutOfBounds) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);

  // Offset + size exceeds total_size (word-aligned offset)
  fips_kat_entry_t oob_entry{
      .algorithm_id = kFipsKatAlgSha2_256,
      .offset = static_cast<uint32_t>(sizeof(layout) - 8),
      .size = 12,  // exceeds by 4 bytes
  };
  EXPECT_EQ(get_fips_data(table, &oob_entry), nullptr);

  // Offset itself exceeds total_size
  fips_kat_entry_t oob_offset_entry{
      .algorithm_id = kFipsKatAlgSha2_256,
      .offset = static_cast<uint32_t>(sizeof(layout) + 4),
      .size = 10,
  };
  EXPECT_EQ(get_fips_data(table, &oob_offset_entry), nullptr);

  // Integer overflow in offset + size
  fips_kat_entry_t overflow_entry{
      .algorithm_id = kFipsKatAlgSha2_256,
      .offset = 0xFFFFFFF0u,
      .size = 0x20u,
  };
  EXPECT_EQ(get_fips_data(table, &overflow_entry), nullptr);

  // Null pointers
  EXPECT_EQ(get_fips_data(nullptr, &oob_entry), nullptr);
  EXPECT_EQ(get_fips_data(table, nullptr), nullptr);
}

TEST(FipsKatTableAlignmentTest, RejectUnalignedPointersAndOffsets) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);
  layout.table.entries[0].algorithm_id = kFipsKatAlgSha2_256;
  layout.table.entries[0].offset = offsetof(TestTableLayout, sha256);
  layout.table.entries[0].size = sizeof(layout.sha256);

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_entry_t *entry = &layout.table.entries[0];

  // Valid baseline
  EXPECT_NE(get_fips_data(table, entry), nullptr);

  // Unaligned table pointer
  const auto *unaligned_table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(
          reinterpret_cast<uintptr_t>(table) + 1);
  EXPECT_EQ(get_fips_data(unaligned_table, entry), nullptr);

  // Unaligned entry pointer
  const auto *unaligned_entry = reinterpret_cast<const fips_kat_entry_t *>(
      reinterpret_cast<uintptr_t>(entry) + 1);
  EXPECT_EQ(get_fips_data(table, unaligned_entry), nullptr);

  // Unaligned offset in entry
  fips_kat_entry_t unaligned_offset_entry = *entry;
  unaligned_offset_entry.offset += 1;
  EXPECT_EQ(get_fips_data(table, &unaligned_offset_entry), nullptr);
  unaligned_offset_entry.offset = entry->offset + 2;
  EXPECT_EQ(get_fips_data(table, &unaligned_offset_entry), nullptr);
  unaligned_offset_entry.offset = entry->offset + 3;
  EXPECT_EQ(get_fips_data(table, &unaligned_offset_entry), nullptr);
}

}  // namespace
