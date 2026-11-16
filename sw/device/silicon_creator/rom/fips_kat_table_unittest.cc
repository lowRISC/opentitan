// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/fips_kat_table.h"

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <set>
#include <utility>
#include <vector>

#include "gtest/gtest.h"

extern "C" const fips_kat_descriptor_table_t *
fips_kat_get_rom_table_for_host_test(void);

namespace {

// Synthetic table layout with 2 entries and 4-byte aligned sub-field payloads.
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
    uint8_t data[36];  // pad4(3) + pad4(32)
  } sha256;

  struct {
    uint32_t key_len;
    uint32_t iv_len;
    uint32_t aad_len;
    uint32_t pt_len;
    uint32_t ct_len;
    uint32_t tag_len;
    uint8_t data[64];  // 32 + 16 + 16
  } aes;
};

TestTableLayout MakeValidLayout() {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 2;
  layout.table.total_size = sizeof(layout);

  layout.table.entries[0] = {
      .algorithm_id = 1u,
      .offset = static_cast<uint32_t>(offsetof(TestTableLayout, sha256)),
      .size = sizeof(layout.sha256),
  };
  layout.table.entries[1] = {
      .algorithm_id = 7u,
      .offset = static_cast<uint32_t>(offsetof(TestTableLayout, aes)),
      .size = sizeof(layout.aes),
  };

  layout.sha256.key_len = 0;
  layout.sha256.msg_len = 3;
  layout.sha256.digest_len = 32;
  layout.sha256.data[0] = 'a';
  layout.sha256.data[1] = 'b';
  layout.sha256.data[2] = 'c';
  layout.sha256.data[4] = 0xba;  // Digest starts at pad4(3) = 4

  layout.aes.key_len = 32;
  layout.aes.pt_len = 16;
  layout.aes.ct_len = 16;
  layout.aes.data[0] = 0x60;
  layout.aes.data[32] = 0x6b;
  layout.aes.data[48] = 0xf3;
  return layout;
}

TEST(FipsKatTableValidationTest, ValidTable) {
  TestTableLayout layout = MakeValidLayout();
  const auto *table =
      get_fips_descriptor_table_from_region(&layout, kFipsKatRegionSize);
  ASSERT_NE(table, nullptr);
  EXPECT_EQ(table, reinterpret_cast<const fips_kat_descriptor_table_t *>(
                       &layout.table));
  EXPECT_TRUE(validate_fips_descriptor_table(table, sizeof(layout)));
}

TEST(FipsKatTableValidationTest, RejectZeroedLegacyRomRegion) {
  alignas(uint32_t) std::array<uint8_t, 256> zero_rom{};
  EXPECT_EQ(
      get_fips_descriptor_table_from_region(zero_rom.data(), zero_rom.size()),
      nullptr);
}

TEST(FipsKatTableValidationTest, RejectInvalidMagicVersionAndSize) {
  TestTableLayout layout = MakeValidLayout();

  layout.table.magic = 0x12345678;
  EXPECT_EQ(get_fips_descriptor_table_from_region(&layout, sizeof(layout)),
            nullptr);

  layout = MakeValidLayout();
  layout.table.version = 2;
  EXPECT_EQ(get_fips_descriptor_table_from_region(&layout, sizeof(layout)),
            nullptr);

  layout = MakeValidLayout();
  layout.table.total_size = 0;
  EXPECT_EQ(get_fips_descriptor_table_from_region(&layout, sizeof(layout)),
            nullptr);

  layout = MakeValidLayout();
  layout.table.total_size = sizeof(fips_kat_descriptor_table_t) - 1;
  EXPECT_EQ(get_fips_descriptor_table_from_region(&layout, sizeof(layout)),
            nullptr);

  // Unaligned total_size (not a multiple of 4).
  layout = MakeValidLayout();
  layout.table.total_size = sizeof(layout) - 2;
  EXPECT_EQ(get_fips_descriptor_table_from_region(&layout, sizeof(layout)),
            nullptr);

  // total_size exceeds region_size.
  layout = MakeValidLayout();
  EXPECT_EQ(get_fips_descriptor_table_from_region(&layout, sizeof(layout) - 4),
            nullptr);

  // region_size smaller than header.
  EXPECT_EQ(get_fips_descriptor_table_from_region(
                &layout, sizeof(fips_kat_descriptor_table_t) - 4),
            nullptr);

  // Excessive entry_count overflowing total_size.
  layout = MakeValidLayout();
  const uint32_t max_entries =
      (layout.table.total_size - sizeof(fips_kat_descriptor_table_t)) /
      sizeof(fips_kat_entry_t);
  layout.table.entry_count = max_entries + 1;
  EXPECT_EQ(get_fips_descriptor_table_from_region(&layout, sizeof(layout)),
            nullptr);
}

TEST(FipsKatTableValidationTest, RejectNullAndUnalignedRegionBase) {
  EXPECT_EQ(get_fips_descriptor_table_from_region(nullptr, kFipsKatRegionSize),
            nullptr);

  // Use memcpy into a byte buffer so UBSan never sees an unaligned struct
  // write.
  TestTableLayout valid = MakeValidLayout();
  alignas(uint32_t) std::array<uint8_t, sizeof(TestTableLayout) + 4> buf{};
  for (size_t misalign = 1; misalign <= 3; ++misalign) {
    std::memcpy(buf.data() + misalign, &valid, sizeof(valid));
    EXPECT_EQ(get_fips_descriptor_table_from_region(buf.data() + misalign,
                                                    sizeof(valid)),
              nullptr);
  }
}

TEST(FipsKatTableSecurityTest, RejectCorruptEntryBoundsAliasingAndWraparound) {
  TestTableLayout layout = MakeValidLayout();
  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const size_t reg = sizeof(layout);
  const uint32_t header_size =
      sizeof(fips_kat_descriptor_table_t) + 2 * sizeof(fips_kat_entry_t);

  // Baseline valid.
  ASSERT_NE(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // Foreign entry pointer outside table->entries[].
  fips_kat_entry_t stack_entry = layout.table.entries[0];
  EXPECT_EQ(get_fips_data(table, reg, &stack_entry), nullptr);

  // Interior misaligned entry pointer (4 bytes into entries[0], not an
  // element).
  const auto *shifted_entry = reinterpret_cast<const fips_kat_entry_t *>(
      reinterpret_cast<uintptr_t>(&layout.table.entries[0]) + 4);
  EXPECT_EQ(get_fips_data(table, reg, shifted_entry), nullptr);

  // Zero-size entry.
  layout = MakeValidLayout();
  layout.table.entries[0].size = 0;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // Unaligned size.
  layout = MakeValidLayout();
  layout.table.entries[0].size = 14;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // Unaligned offset.
  for (uint32_t mis = 1; mis <= 3; ++mis) {
    layout = MakeValidLayout();
    layout.table.entries[0].offset = header_size + mis;
    EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);
  }

  // Header aliasing: offset < header_size.
  for (uint32_t bad_off : {0u, 16u, header_size - 4u}) {
    layout = MakeValidLayout();
    layout.table.entries[0].offset = bad_off;
    layout.table.entries[0].size = 4;
    EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);
  }

  // One-past-the-end: offset == total_size.
  layout = MakeValidLayout();
  layout.table.entries[0].offset = sizeof(layout);
  layout.table.entries[0].size = 4;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // Offset + size exceeds total_size by 4 bytes.
  layout = MakeValidLayout();
  layout.table.entries[0].offset = sizeof(layout) - 8;
  layout.table.entries[0].size = 12;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // True 32-bit unsigned wraparound: valid offset (header_size <= total_size)
  // combined with huge size such that (uint32_t)(offset + size) < total_size.
  layout = MakeValidLayout();
  layout.table.entries[0].offset = header_size;
  layout.table.entries[0].size = 0xFFFFFFFCu;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // Null pointers and region_size smaller than total_size.
  layout = MakeValidLayout();
  EXPECT_EQ(get_fips_data(nullptr, reg, &layout.table.entries[0]), nullptr);
  EXPECT_EQ(get_fips_data(table, reg, nullptr), nullptr);
  EXPECT_EQ(get_fips_data(table, sizeof(layout) - 4, &layout.table.entries[0]),
            nullptr);
}

TEST(FipsKatRealRomBlobTest, ValidateAll31EmbeddedRomEntries) {
  const fips_kat_descriptor_table_t *raw_table =
      fips_kat_get_rom_table_for_host_test();
  ASSERT_NE(raw_table, nullptr);

  const fips_kat_descriptor_table_t *table =
      get_fips_descriptor_table_from_region(raw_table, kFipsKatRegionSize);
  ASSERT_NE(table, nullptr);
  EXPECT_EQ(table->magic, kFipsKatDescriptorMagic);
  EXPECT_EQ(table->version, kFipsKatDescriptorVersion1);
  EXPECT_EQ(table->entry_count, 9u);
  EXPECT_LE(table->total_size, kFipsKatRegionSize);
  EXPECT_EQ(table->total_size % 4u, 0u);

  std::set<uint32_t> seen_ids;
  std::vector<std::pair<uint32_t, uint32_t>> intervals;

  for (uint32_t id : std::vector<uint32_t>{1, 2, 3, 4, 5, 6, 7, 8, 9}) {
    const auto alg_id = static_cast<fips_kat_alg_id_t>(id);
    const fips_kat_entry_t *entry =
        find_fips_entry(table, kFipsKatRegionSize, alg_id);
    ASSERT_NE(entry, nullptr) << "Missing algorithm_id " << id;
    EXPECT_TRUE(seen_ids.insert(entry->algorithm_id).second)
        << "Duplicate algorithm_id " << id;

    const void *payload = get_fips_data(table, kFipsKatRegionSize, entry);
    ASSERT_NE(payload, nullptr) << "Invalid payload for algorithm_id " << id;
    EXPECT_EQ(reinterpret_cast<uintptr_t>(payload) & 3u, 0u);
    intervals.emplace_back(entry->offset, entry->offset + entry->size);

    switch (alg_id) {
      case kFipsKatAlgSha2_256:
      case kFipsKatAlgSha2_512:
      case kFipsKatAlgHmacSha2_256:
      case kFipsKatAlgHmacSha2_512:
      case kFipsKatAlgShake256: {

        const auto *kat = static_cast<const hmac_kat_data_t *>(payload);
        EXPECT_EQ(entry->size, fips_kat_hmac_expected_size(kat))
            << "alg_id=" << id;
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_hmac_key(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_hmac_msg(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_hmac_digest(kat)) & 3u,
                  0u);
        break;
      }
      case kFipsKatAlgKmac256: {

        const auto *kat = static_cast<const kdf_kat_data_t *>(payload);
        EXPECT_EQ(entry->size, fips_kat_kdf_expected_size(kat))
            << "alg_id=" << id;
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_kdf_key(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_kdf_label(kat)) & 3u,
                  0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_kdf_context(kat)) & 3u,
                  0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_kdf_out(kat)) & 3u, 0u);
        break;
      }
      case kFipsKatAlgAesEcb256Decrypt:
      case kFipsKatAlgAesCbc256Decrypt:
      case kFipsKatAlgAesKwp256Wrap: {

        const auto *kat = static_cast<const aes_kat_data_t *>(payload);
        EXPECT_EQ(entry->size, fips_kat_aes_expected_size(kat))
            << "alg_id=" << id;
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_aes_key(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_aes_iv(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_aes_aad(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_aes_pt(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_aes_ct(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_aes_tag(kat)) & 3u, 0u);
        break;
      }
      default:
        FAIL() << "Unhandled algorithm_id " << id;
    }
  }

  // Confirm all payload intervals are strictly non-overlapping.
  std::sort(intervals.begin(), intervals.end());
  for (size_t i = 1; i < intervals.size(); ++i) {
    EXPECT_LE(intervals[i - 1].second, intervals[i].first)
        << "Overlapping payloads at sorted index " << i;
  }
}

}  // namespace
