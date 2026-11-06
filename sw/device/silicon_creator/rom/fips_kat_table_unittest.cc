// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/fips_kat_table.h"

#include <sys/mman.h>
#include <unistd.h>

#include "gtest/gtest.h"

namespace {

// Helper struct for a table with 1 entry and dummy payload data.
struct TestTableLayout {
  struct {
    uint32_t magic;
    uint32_t version;
    uint32_t entry_count;
    uint32_t total_size;
    fips_kat_entry_t entries[1];
  } table;

  struct {
    uint32_t field1;
    uint32_t field2;
    uint8_t data[8];
  } payload;
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
  layout.table.entry_count = 1;
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
}

TEST_F(FipsKatTableTest, ValidateTableZeroTotalSize) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 0;
  layout.table.total_size = 0;

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_descriptor_table_t *ptr = table;
  EXPECT_EQ(
      get_fips_descriptor_table_from_address(reinterpret_cast<uintptr_t>(&ptr)),
      nullptr);
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
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  layout.table.entries[0].algorithm_id = 1;
  layout.table.entries[0].offset = offsetof(TestTableLayout, payload);
  layout.table.entries[0].size = sizeof(layout.payload);

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);

  // Find existing entries
  const fips_kat_entry_t *entry =
      find_fips_entry(table, static_cast<fips_kat_alg_id_t>(1));
  ASSERT_NE(entry, nullptr);
  EXPECT_EQ(entry->algorithm_id, 1);
  EXPECT_EQ(entry->offset, offsetof(TestTableLayout, payload));
  EXPECT_EQ(entry->size, sizeof(layout.payload));

  // Non-existent algorithms
  EXPECT_EQ(find_fips_entry(table, static_cast<fips_kat_alg_id_t>(99)),
            nullptr);
  EXPECT_EQ(find_fips_entry(table, kFipsKatAlgNone), nullptr);
  EXPECT_EQ(find_fips_entry(nullptr, static_cast<fips_kat_alg_id_t>(1)),
            nullptr);
}

TEST(FipsKatTableSearchTest, DefensiveChecks) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);
  layout.table.entries[0].algorithm_id = 1;

  // Unaligned table pointer
  uintptr_t unaligned_addr =
      reinterpret_cast<uintptr_t>(&layout.table) + 1;
  const auto *unaligned_table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(
          unaligned_addr);
  EXPECT_EQ(
      find_fips_entry(unaligned_table, static_cast<fips_kat_alg_id_t>(1)),
      nullptr);

  // Invalid total size
  layout.table.total_size = sizeof(fips_kat_descriptor_table_t) - 1;
  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  EXPECT_EQ(find_fips_entry(table, static_cast<fips_kat_alg_id_t>(1)),
            nullptr);
}

TEST(FipsKatTableDataTest, GetDataSuccess) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  layout.table.entries[0].algorithm_id = 1;
  layout.table.entries[0].offset = offsetof(TestTableLayout, payload);
  layout.table.entries[0].size = sizeof(layout.payload);

  layout.payload.field1 = 0x12345678;
  layout.payload.field2 = 0x9abcdef0;

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, static_cast<fips_kat_alg_id_t>(1));
  ASSERT_NE(entry, nullptr);

  const void *data = get_fips_data(table, entry);
  ASSERT_NE(data, nullptr);
  const auto *payload =
      reinterpret_cast<const decltype(layout.payload) *>(data);
  EXPECT_EQ(payload->field1, 0x12345678);
  EXPECT_EQ(payload->field2, 0x9abcdef0);
}

TEST(FipsKatTableBoundsCheckTest, RejectOutOfBounds) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);

  // Offset past total_size
  layout.table.entries[0].offset = sizeof(layout) + 4;
  layout.table.entries[0].size = 4;
  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  EXPECT_EQ(get_fips_data(table, &layout.table.entries[0]), nullptr);

  // Offset + size overflows total_size
  layout.table.entries[0].offset = sizeof(layout) - 4;
  layout.table.entries[0].size = 8;
  EXPECT_EQ(get_fips_data(table, &layout.table.entries[0]), nullptr);

  // Arithmetic overflow (offset + size wraps uint32_t)
  layout.table.entries[0].offset = 0xFFFFFFF0;
  layout.table.entries[0].size = 0x20;
  EXPECT_EQ(get_fips_data(table, &layout.table.entries[0]), nullptr);
}

TEST(FipsKatTableAlignmentTest, RejectUnalignedPointersAndOffsets) {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 1;
  layout.table.total_size = sizeof(layout);
  layout.table.entries[0].offset = offsetof(TestTableLayout, payload);
  layout.table.entries[0].size = sizeof(layout.payload);

  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);

  // Unaligned table pointer
  const auto *unaligned_table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(
          reinterpret_cast<uintptr_t>(table) + 1);
  EXPECT_EQ(get_fips_data(unaligned_table, &layout.table.entries[0]), nullptr);

  // Unaligned entry pointer
  const auto *unaligned_entry = reinterpret_cast<const fips_kat_entry_t *>(
      reinterpret_cast<uintptr_t>(&layout.table.entries[0]) + 1);
  EXPECT_EQ(get_fips_data(table, unaligned_entry), nullptr);

  // Unaligned offset
  layout.table.entries[0].offset = offsetof(TestTableLayout, payload) + 1;
  EXPECT_EQ(get_fips_data(table, &layout.table.entries[0]), nullptr);
}

}  // namespace
