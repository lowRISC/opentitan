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
struct alignas(uint32_t) TestTableLayout {
  struct {
    uint32_t magic;
    uint32_t version;
    uint32_t entry_count;
    uint32_t total_size;
    fips_kat_entry_t entries[2];
  } table;

  struct {
    uint16_t key_len;
    uint16_t msg_len;
    uint16_t digest_len;
    uint16_t reserved;
    uint8_t data[36];  // pad4(3) + pad4(32)
  } sha256;

  struct {
    uint16_t key_len;
    uint16_t iv_len;
    uint16_t aad_len;
    uint16_t pt_len;
    uint16_t ct_len;
    uint16_t tag_len;
    uint8_t data[64];  // 32 + 16 + 16
  } aes;
};

static_assert(sizeof(TestTableLayout) % 4 == 0,
              "TestTableLayout must be 4-byte aligned in size");
static_assert(offsetof(TestTableLayout, sha256) % 4 == 0,
              "TestTableLayout.sha256 must be 4-byte aligned");
static_assert(offsetof(TestTableLayout, aes) % 4 == 0,
              "TestTableLayout.aes must be 4-byte aligned");

TestTableLayout MakeValidLayout() {
  TestTableLayout layout{};
  layout.table.magic = kFipsKatDescriptorMagic;
  layout.table.version = kFipsKatDescriptorVersion1;
  layout.table.entry_count = 2;
  layout.table.total_size = sizeof(layout);

  layout.table.entries[0] = {
      .algorithm_id = static_cast<uint16_t>(kFipsKatAlgSha2_256),
      .reserved = 0,
      .offset = static_cast<uint16_t>(offsetof(TestTableLayout, sha256)),
      .size = static_cast<uint16_t>(sizeof(layout.sha256)),
  };
  layout.table.entries[1] = {
      .algorithm_id = static_cast<uint16_t>(kFipsKatAlgAesEcb256Decrypt),
      .reserved = 0,
      .offset = static_cast<uint16_t>(offsetof(TestTableLayout, aes)),
      .size = static_cast<uint16_t>(sizeof(layout.aes)),
  };

  layout.sha256.key_len = 0;
  layout.sha256.msg_len = 3;
  layout.sha256.digest_len = 32;
  layout.sha256.reserved = 0;
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
  EXPECT_EQ(kFipsKatRomEndOffset, 0x2000u);
  EXPECT_EQ(kFipsKatRegionSize, 0x2000u);
  EXPECT_EQ(kFipsKatChipInfoReservedBytes, 128u);
  EXPECT_EQ(kFipsKatMaxTableSize, 0x1F80u);
  EXPECT_EQ(kFipsKatSparseChunkBytes, 16u);

  TestTableLayout layout = MakeValidLayout();
  const auto *table =
      get_fips_descriptor_table_from_region(&layout, kFipsKatMaxTableSize);
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

  // Header claiming total_size == kFipsKatRegionSize (0x2000) must be rejected
  // when validated against kFipsKatMaxTableSize (0x1F80), protecting
  // .chip_info and ECC-poisoned rom_ctrl digest words.
  layout = MakeValidLayout();
  layout.table.total_size = kFipsKatRegionSize;
  EXPECT_EQ(
      get_fips_descriptor_table_from_region(&layout, kFipsKatMaxTableSize),
      nullptr);

  // region_size smaller than header.
  layout = MakeValidLayout();
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
  EXPECT_EQ(
      get_fips_descriptor_table_from_region(nullptr, kFipsKatMaxTableSize),
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

TEST(FipsKatTableLookupTest, FindEntryAndResolveData) {
  TestTableLayout layout = MakeValidLayout();
  const auto *table =
      get_fips_descriptor_table_from_region(&layout, sizeof(layout));
  ASSERT_NE(table, nullptr);

  const fips_kat_entry_t *sha_entry =
      find_fips_entry(table, sizeof(layout), kFipsKatAlgSha2_256);
  ASSERT_NE(sha_entry, nullptr);
  EXPECT_EQ(sha_entry->algorithm_id, kFipsKatAlgSha2_256);
  EXPECT_EQ(sha_entry->reserved, 0u);

  const void *sha_ptr = get_fips_data(table, sizeof(layout), sha_entry);
  ASSERT_NE(sha_ptr, nullptr);
  const auto *sha = static_cast<const hmac_kat_data_t *>(sha_ptr);
  EXPECT_EQ(sha_entry->size, fips_kat_hmac_expected_size(sha));
  EXPECT_EQ(fips_kat_hmac_msg(sha)[0], 'a');
  EXPECT_EQ(fips_kat_hmac_digest(sha)[0], 0xba);
  EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_hmac_digest(sha)) & 3u, 0u);

  const fips_kat_entry_t *aes_entry =
      find_fips_entry(table, sizeof(layout), kFipsKatAlgAesEcb256Decrypt);
  ASSERT_NE(aes_entry, nullptr);
  const void *aes_ptr = get_fips_data(table, sizeof(layout), aes_entry);
  ASSERT_NE(aes_ptr, nullptr);
  const auto *aes = static_cast<const aes_kat_data_t *>(aes_ptr);
  EXPECT_EQ(aes_entry->size, fips_kat_aes_expected_size(aes));
  EXPECT_EQ(fips_kat_aes_key(aes)[0], 0x60);
  EXPECT_EQ(fips_kat_aes_pt(aes)[0], 0x6b);
  EXPECT_EQ(fips_kat_aes_ct(aes)[0], 0xf3);

  // Missing entry, kFipsKatAlgNone, and out-of-uint16-range alg_id.
  EXPECT_EQ(find_fips_entry(table, sizeof(layout), kFipsKatAlgNone), nullptr);
  EXPECT_EQ(find_fips_entry(table, sizeof(layout), kFipsKatAlgRsa4096),
            nullptr);
  EXPECT_EQ(find_fips_entry(
                table, sizeof(layout),
                static_cast<fips_kat_alg_id_t>(0x10000u + kFipsKatAlgSha2_256)),
            nullptr);

  // Even if a corrupt table entry has algorithm_id == kFipsKatAlgNone,
  // find_fips_entry() must reject kFipsKatAlgNone.
  layout.table.entries[0].algorithm_id = static_cast<uint16_t>(kFipsKatAlgNone);
  EXPECT_EQ(find_fips_entry(table, sizeof(layout), kFipsKatAlgNone), nullptr);
}

TEST(FipsKatTableSecurityTest, RejectCorruptEntryBoundsAliasingAndWraparound) {
  TestTableLayout layout = MakeValidLayout();
  const auto *table =
      reinterpret_cast<const fips_kat_descriptor_table_t *>(&layout.table);
  const size_t reg = sizeof(layout);
  const uint16_t header_size = static_cast<uint16_t>(
      sizeof(fips_kat_descriptor_table_t) + 2 * sizeof(fips_kat_entry_t));

  // Baseline valid.
  ASSERT_NE(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // Non-zero reserved field in entry must be rejected.
  layout = MakeValidLayout();
  layout.table.entries[0].reserved = 1;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  layout = MakeValidLayout();
  layout.table.entries[0].reserved = 0xFFFF;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // Foreign 4-byte-aligned entry pointer outside table->entries[] (exercises
  // the pointer range check rather than alignment rejection).
  layout = MakeValidLayout();
  alignas(uint32_t) fips_kat_entry_t stack_entry = layout.table.entries[0];
  EXPECT_EQ(get_fips_data(table, reg, &stack_entry), nullptr);

  // Unaligned entry pointer (+2 bytes into entries[0], fails 4-byte alignment
  // check).
  const auto *unaligned_entry = reinterpret_cast<const fips_kat_entry_t *>(
      reinterpret_cast<uintptr_t>(&layout.table.entries[0]) + 2);
  EXPECT_EQ(get_fips_data(table, reg, unaligned_entry), nullptr);

  // Interior misaligned entry pointer (4 bytes into 8-byte entries[0], not an
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
  for (uint16_t mis = 1; mis <= 3; ++mis) {
    layout = MakeValidLayout();
    layout.table.entries[0].offset = static_cast<uint16_t>(header_size + mis);
    EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);
  }

  // Header aliasing: offset < header_size.
  for (uint16_t bad_off :
       {uint16_t{0}, uint16_t{16}, static_cast<uint16_t>(header_size - 4)}) {
    layout = MakeValidLayout();
    layout.table.entries[0].offset = bad_off;
    layout.table.entries[0].size = 4;
    EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);
  }

  // One-past-the-end: offset == total_size.
  layout = MakeValidLayout();
  layout.table.entries[0].offset = static_cast<uint16_t>(sizeof(layout));
  layout.table.entries[0].size = 4;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // Offset + size exceeds total_size by 4 bytes.
  layout = MakeValidLayout();
  layout.table.entries[0].offset = static_cast<uint16_t>(sizeof(layout) - 8);
  layout.table.entries[0].size = 12;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // True 16-bit unsigned wraparound: valid offset (header_size <= total_size)
  // combined with huge uint16_t size such that
  // (uint16_t)(offset + size) < total_size.
  layout = MakeValidLayout();
  layout.table.entries[0].offset = header_size;
  layout.table.entries[0].size = 0xFFFCu;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // 16-bit unsigned wraparound with large offset and small size.
  layout = MakeValidLayout();
  layout.table.entries[0].offset = 0xFFFCu;
  layout.table.entries[0].size = 8u;
  EXPECT_EQ(get_fips_data(table, reg, &layout.table.entries[0]), nullptr);

  // Null pointers and region_size smaller than total_size.
  layout = MakeValidLayout();
  EXPECT_EQ(get_fips_data(nullptr, reg, &layout.table.entries[0]), nullptr);
  EXPECT_EQ(get_fips_data(table, reg, nullptr), nullptr);
  EXPECT_EQ(get_fips_data(table, sizeof(layout) - 4, &layout.table.entries[0]),
            nullptr);
}

TEST(FipsKatSparseSigTest, UnpackRealRomSlhDsaEntry) {
  const fips_kat_descriptor_table_t *table =
      get_fips_descriptor_table_from_region(
          fips_kat_get_rom_table_for_host_test(), kFipsKatMaxTableSize);
  ASSERT_NE(table, nullptr);

  const fips_kat_entry_t *entry = find_fips_entry(
      table, kFipsKatMaxTableSize, kFipsKatAlgSphincsPlusSha2_128sVerify);
  ASSERT_NE(entry, nullptr);
  EXPECT_EQ(entry->size, 384u);
  EXPECT_EQ(entry->reserved, 0u);

  const auto *kat = static_cast<const sparse_verify_kat_data_t *>(
      get_fips_data(table, kFipsKatMaxTableSize, entry));
  ASSERT_NE(kat, nullptr);
  EXPECT_EQ(kat->pub_key_len, 32u);
  EXPECT_EQ(kat->msg_len, 1u);
  EXPECT_EQ(kat->sig_len, 7856u);
  EXPECT_EQ(kat->num_chunks, 17u);
  EXPECT_EQ(entry->size, fips_kat_sparse_verify_expected_size(kat));

  const uint8_t *pk = fips_kat_sparse_verify_pub_key(kat);
  const uint8_t *msg = fips_kat_sparse_verify_msg(kat);
  const fips_kat_sparse_chunk_t *chunks = fips_kat_sparse_verify_chunks(kat);
  EXPECT_EQ(reinterpret_cast<uintptr_t>(pk) & 3u, 0u);
  EXPECT_EQ(reinterpret_cast<uintptr_t>(msg) & 3u, 0u);
  EXPECT_EQ(reinterpret_cast<uintptr_t>(chunks) & 3u, 0u);

  // Verify public key and message contents.
  for (size_t i = 0; i < 16; ++i) {
    EXPECT_EQ(pk[i], 0x00u);
  }
  EXPECT_EQ(pk[16], 0x36u);
  EXPECT_EQ(pk[31], 0x03u);
  EXPECT_EQ(msg[0], 0x01u);

  // Pre-fill output buffer with non-zero sentinel to ensure unpack zeroes gaps.
  std::array<uint8_t, 7856> sig{};
  sig.fill(0xAA);
  ASSERT_TRUE(
      fips_kat_sparse_sig_unpack(kat, entry->size, sig.data(), sig.size()));

  // Count non-zero bytes: 261 in signature (+ 16 in pk + 1 in msg = 278 total).
  size_t sig_nonzero = 0;
  for (uint8_t b : sig) {
    if (b != 0) {
      ++sig_nonzero;
    }
  }
  size_t pk_nonzero = 0;
  for (size_t i = 0; i < kat->pub_key_len; ++i) {
    if (pk[i] != 0) {
      ++pk_nonzero;
    }
  }
  size_t msg_nonzero = 0;
  for (size_t i = 0; i < kat->msg_len; ++i) {
    if (msg[i] != 0) {
      ++msg_nonzero;
    }
  }
  EXPECT_EQ(sig_nonzero, 261u);
  EXPECT_EQ(pk_nonzero + msg_nonzero + sig_nonzero, 278u);

  // Spot-check zero gaps and exact chunk boundaries.
  for (size_t i = 0; i < 7146; ++i) {
    ASSERT_EQ(sig[i], 0x00u) << "Expected zero gap at sig[" << i << "]";
  }
  // Chunk 0 (aligned at 7136): leading 10 zeros + non-zero bytes at [7146,
  // 7152)
  EXPECT_EQ(sig[7146], 0x03u);
  EXPECT_EQ(sig[7147], 0xf6u);
  EXPECT_EQ(sig[7151], 0x14u);
  // Zero gap [7152, 7168)
  for (size_t i = 7152; i < 7168; ++i) {
    EXPECT_EQ(sig[i], 0x00u) << "Expected zero gap at sig[" << i << "]";
  }
  // Chunks 1..3: [7168, 7216)
  EXPECT_EQ(sig[7168], 0x06u);
  EXPECT_EQ(sig[7215], 0x17u);
  // Zero gap [7216, 7264)
  for (size_t i = 7216; i < 7264; ++i) {
    EXPECT_EQ(sig[i], 0x00u) << "Expected zero gap at sig[" << i << "]";
  }
  // Chunk 4: [7264, 7280) (contains internal 0x00 byte at index 6)
  EXPECT_EQ(sig[7264], 0x2au);
  EXPECT_EQ(sig[7270], 0x00u);
  EXPECT_EQ(sig[7279], 0xfcu);
  // Chunks 14..16: [7584, 7632)
  EXPECT_EQ(sig[7584], 0xc5u);
  EXPECT_EQ(sig[7631], 0x08u);
  // Trailing zero gap [7632, 7856)
  for (size_t i = 7632; i < sig.size(); ++i) {
    ASSERT_EQ(sig[i], 0x00u) << "Expected trailing zero at sig[" << i << "]";
  }
}

TEST(FipsKatSparseSigTest, SyntheticEdgeAndNegativeCases) {
  struct alignas(uint32_t) TwoChunkSparse {
    uint16_t pub_key_len;
    uint16_t msg_len;
    uint16_t sig_len;
    uint16_t num_chunks;
    uint8_t pk[4];
    uint8_t msg[4];
    fips_kat_sparse_chunk_t chunks[2];
  };
  static_assert(sizeof(TwoChunkSparse) == 56, "Unexpected synthetic size");

  auto make_valid = []() {
    TwoChunkSparse s{};
    s.pub_key_len = 4;
    s.msg_len = 1;
    s.sig_len = 64;
    s.num_chunks = 2;
    s.chunks[0].offset = 16;
    s.chunks[0].reserved = 0;
    for (uint8_t i = 0; i < kFipsKatSparseChunkBytes; ++i) {
      s.chunks[0].data[i] = static_cast<uint8_t>(0x10u + i);
    }
    // Immediately adjacent to chunks[0] end (16 + 16 = 32): allowed.
    s.chunks[1].offset = 32;
    s.chunks[1].reserved = 0;
    for (uint8_t i = 0; i < kFipsKatSparseChunkBytes; ++i) {
      s.chunks[1].data[i] = static_cast<uint8_t>(0xA0u + i);
    }
    return s;
  };

  std::array<uint8_t, 64> out{};
  auto expect_all_zero = [](const uint8_t *buf, size_t len) {
    for (size_t i = 0; i < len; ++i) {
      EXPECT_EQ(buf[i], 0x00u) << "Expected wiped byte at index " << i;
    }
  };

  // Baseline valid unpack with adjacent fixed 16-byte chunks.
  TwoChunkSparse valid = make_valid();
  const auto *kat = reinterpret_cast<const sparse_verify_kat_data_t *>(&valid);
  EXPECT_EQ(fips_kat_sparse_verify_expected_size(kat), sizeof(valid));
  ASSERT_TRUE(
      fips_kat_sparse_sig_unpack(kat, sizeof(valid), out.data(), out.size()));
  EXPECT_EQ(out[15], 0x00u);
  EXPECT_EQ(out[16], 0x10u);
  EXPECT_EQ(out[31], 0x1Fu);
  EXPECT_EQ(out[32], 0xA0u);
  EXPECT_EQ(out[47], 0xAFu);
  EXPECT_EQ(out[48], 0x00u);

  // Valid chunk at offset 0 with immediately adjacent chunk at offset 16.
  {
    TwoChunkSparse at_zero = make_valid();
    at_zero.chunks[0].offset = 0;
    at_zero.chunks[1].offset = 16;
    out.fill(0xFF);
    ASSERT_TRUE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&at_zero),
        sizeof(at_zero), out.data(), out.size()));
    EXPECT_EQ(out[0], 0x10u);
    EXPECT_EQ(out[15], 0x1Fu);
    EXPECT_EQ(out[16], 0xA0u);
    EXPECT_EQ(out[31], 0xAFu);
    expect_all_zero(out.data() + 32, out.size() - 32);
  }

  // Valid 0-chunk all-zero signature when entry_size == expected_size.
  {
    TwoChunkSparse empty = make_valid();
    empty.num_chunks = 0;
    out.fill(0xFF);
    const size_t empty_size = offsetof(TwoChunkSparse, chunks);
    EXPECT_TRUE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&empty), empty_size,
        out.data(), out.size()));
    expect_all_zero(out.data(), out.size());
  }

  // NULL pointers.
  EXPECT_FALSE(
      fips_kat_sparse_sig_unpack(nullptr, sizeof(valid), out.data(), 64));
  EXPECT_FALSE(fips_kat_sparse_sig_unpack(kat, sizeof(valid), nullptr, 64));

  // Misaligned kat pointer.
  {
    alignas(uint32_t) std::array<uint8_t, sizeof(TwoChunkSparse) + 4> buf{};
    for (size_t mis = 1; mis <= 3; ++mis) {
      std::memcpy(buf.data() + mis, &valid, sizeof(valid));
      EXPECT_FALSE(fips_kat_sparse_sig_unpack(
          reinterpret_cast<const sparse_verify_kat_data_t *>(buf.data() + mis),
          sizeof(valid), out.data(), out.size()));
    }
  }

  // Wrong out_sig_len or zero out_sig_len.
  EXPECT_FALSE(fips_kat_sparse_sig_unpack(kat, sizeof(valid), out.data(), 0));
  EXPECT_FALSE(fips_kat_sparse_sig_unpack(kat, sizeof(valid), out.data(), 63));
  EXPECT_FALSE(fips_kat_sparse_sig_unpack(kat, sizeof(valid), out.data(), 65));

  // entry_size too small / mismatch (< header, truncated, or trailing bytes).
  EXPECT_FALSE(fips_kat_sparse_sig_unpack(kat, 4, out.data(), out.size()));
  EXPECT_FALSE(fips_kat_sparse_sig_unpack(kat, 12, out.data(), out.size()));
  EXPECT_FALSE(fips_kat_sparse_sig_unpack(kat, sizeof(valid) - 4, out.data(),
                                          out.size()));
  {
    alignas(uint32_t) std::array<uint8_t, sizeof(TwoChunkSparse) + 4> padded{};
    std::memcpy(padded.data(), &valid, sizeof(valid));
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(padded.data()),
        padded.size(), out.data(), out.size()));

    // num_chunks == 0 with trailing chunk bytes.
    TwoChunkSparse bad = make_valid();
    bad.num_chunks = 0;
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad), sizeof(bad),
        out.data(), out.size()));

    // Non-truncation regression guard: num_chunks = 0xFFFF must not wrap in
    // expected_size calculation and must be rejected against TwoChunkSparse.
    bad = make_valid();
    bad.num_chunks = 0xFFFFu;
    const auto *bad_kat =
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad);
    EXPECT_EQ(fips_kat_sparse_verify_expected_size(bad_kat),
              8u + 4u + 4u + 65535u * 20u);
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(bad_kat, sizeof(TwoChunkSparse),
                                            out.data(), out.size()));
  }

  // Non-zero chunk->reserved rejected (and output wiped).
  {
    TwoChunkSparse bad = make_valid();
    bad.chunks[1].reserved = 1;
    out.fill(0x55);
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad), sizeof(bad),
        out.data(), out.size()));
    expect_all_zero(out.data(), out.size());
  }

  // Non-16-byte-aligned offset rejected (and output wiped).
  for (uint16_t mis : {uint16_t{1}, uint16_t{4}, uint16_t{8}, uint16_t{15}}) {
    TwoChunkSparse bad = make_valid();
    bad.chunks[1].offset = static_cast<uint16_t>(32u + mis);
    out.fill(0x55);
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad), sizeof(bad),
        out.data(), out.size()));
    expect_all_zero(out.data(), out.size());
  }

  // Out-of-bounds offset (> out_sig_len, offset + 16 > out_sig_len,
  // partial-tail OOB where offset < sig_len but sig_len - offset < 16, and
  // 16-bit wraparound offset = 0xFFF0 where (uint16_t)(0xFFF0 + 16) == 0).
  {
    TwoChunkSparse bad = make_valid();
    bad.chunks[1].offset = 64;  // 64 + 16 = 80 > 64
    out.fill(0x55);
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad), sizeof(bad),
        out.data(), out.size()));
    expect_all_zero(out.data(), out.size());

    bad = make_valid();
    bad.chunks[1].offset = 80;  // > out_sig_len
    out.fill(0x55);
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad), sizeof(bad),
        out.data(), out.size()));
    expect_all_zero(out.data(), out.size());

    bad = make_valid();
    bad.sig_len = 56;
    bad.chunks[1].offset = 48;  // 48 < 56, but 56 - 48 = 8 < 16
    out.fill(0x55);
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad), sizeof(bad),
        out.data(), 56));
    expect_all_zero(out.data(), 56);

    bad = make_valid();
    bad.chunks[1].offset = 0xFFF0u;
    out.fill(0x55);
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad), sizeof(bad),
        out.data(), out.size()));
    expect_all_zero(out.data(), out.size());
  }

  // Duplicate / overlapping chunk offset (chunks[1].offset ==
  // chunks[0].offset).
  {
    TwoChunkSparse bad = make_valid();
    bad.chunks[1].offset = 16;
    out.fill(0x55);
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad), sizeof(bad),
        out.data(), out.size()));
    expect_all_zero(out.data(), out.size());
  }

  // Unsorted chunk offset (chunks[1].offset < chunks[0].offset).
  {
    TwoChunkSparse bad = make_valid();
    bad.chunks[1].offset = 0;
    out.fill(0x55);
    EXPECT_FALSE(fips_kat_sparse_sig_unpack(
        reinterpret_cast<const sparse_verify_kat_data_t *>(&bad), sizeof(bad),
        out.data(), out.size()));
    expect_all_zero(out.data(), out.size());
  }
}

TEST(FipsKatRealRomBlobTest, ValidateAll30EmbeddedRomEntries) {
  const fips_kat_descriptor_table_t *raw_table =
      fips_kat_get_rom_table_for_host_test();
  ASSERT_NE(raw_table, nullptr);

  const fips_kat_descriptor_table_t *table =
      get_fips_descriptor_table_from_region(raw_table, kFipsKatMaxTableSize);
  ASSERT_NE(table, nullptr);
  EXPECT_EQ(table->magic, kFipsKatDescriptorMagic);
  EXPECT_EQ(table->version, kFipsKatDescriptorVersion1);
  EXPECT_EQ(table->entry_count, 30u);
  EXPECT_LE(table->total_size, kFipsKatMaxTableSize);
  EXPECT_EQ(table->total_size, 7448u);
  EXPECT_EQ(table->total_size % 4u, 0u);

  // Reserved ID 14 (merged into kFipsKatAlgRsa4096) must not exist.
  EXPECT_EQ(find_fips_entry(table, kFipsKatMaxTableSize,
                            static_cast<fips_kat_alg_id_t>(14)),
            nullptr);

  std::set<uint32_t> seen_ids;
  std::vector<std::pair<uint32_t, uint32_t>> intervals;

  for (uint32_t id = 1; id <= 31; ++id) {
    if (id == 14) {
      continue;
    }
    const auto alg_id = static_cast<fips_kat_alg_id_t>(id);
    const fips_kat_entry_t *entry =
        find_fips_entry(table, kFipsKatMaxTableSize, alg_id);
    ASSERT_NE(entry, nullptr) << "Missing algorithm_id " << id;
    EXPECT_EQ(entry->reserved, 0u) << "Non-zero reserved for alg_id " << id;
    EXPECT_TRUE(seen_ids.insert(entry->algorithm_id).second)
        << "Duplicate algorithm_id " << id;

    const void *payload = get_fips_data(table, kFipsKatMaxTableSize, entry);
    ASSERT_NE(payload, nullptr) << "Invalid payload for algorithm_id " << id;
    EXPECT_EQ(reinterpret_cast<uintptr_t>(payload) & 3u, 0u);
    intervals.emplace_back(entry->offset,
                           static_cast<uint32_t>(entry->offset) +
                               static_cast<uint32_t>(entry->size));

    switch (alg_id) {
      case kFipsKatAlgSha2_256:
      case kFipsKatAlgSha2_512:
      case kFipsKatAlgHmacSha2_256:
      case kFipsKatAlgHmacSha2_512:
      case kFipsKatAlgShake256:
      case kFipsKatAlgEntropySrcSha3Conditioning:
      case kFipsKatAlgSha2_384: {
        const auto *kat = static_cast<const hmac_kat_data_t *>(payload);
        EXPECT_EQ(kat->reserved, 0u) << "alg_id=" << id;
        EXPECT_EQ(entry->size, fips_kat_hmac_expected_size(kat))
            << "alg_id=" << id;
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_hmac_key(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_hmac_msg(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_hmac_digest(kat)) & 3u,
                  0u);
        break;
      }
      case kFipsKatAlgKmac256:
      case kFipsKatAlgKdfHmacSha2_256:
      case kFipsKatAlgKdfKmac256: {
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
      case kFipsKatAlgAesKwp256Wrap:
      case kFipsKatAlgAesGcm256Encrypt: {
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
      case kFipsKatAlgRsa2048Verify:
      case kFipsKatAlgEcdsaP256Verify:
      case kFipsKatAlgEcdsaP384Verify:
      case kFipsKatAlgEd25519Verify: {
        const auto *kat =
            static_cast<const asymmetric_verify_kat_data_t *>(payload);
        EXPECT_EQ(kat->reserved, 0u) << "alg_id=" << id;
        EXPECT_EQ(entry->size, fips_kat_asym_verify_expected_size(kat))
            << "alg_id=" << id;
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_verify_pub_key1(kat)) &
                3u,
            0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_verify_pub_key2(kat)) &
                3u,
            0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_verify_msg(kat)) & 3u,
            0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_verify_sig1(kat)) & 3u,
            0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_verify_sig2(kat)) & 3u,
            0u);
        break;
      }
      case kFipsKatAlgSphincsPlusSha2_128sVerify: {
        const auto *kat =
            static_cast<const sparse_verify_kat_data_t *>(payload);
        EXPECT_EQ(entry->size, 384u);
        EXPECT_EQ(entry->size, fips_kat_sparse_verify_expected_size(kat));
        EXPECT_EQ(kat->pub_key_len, 32u);
        EXPECT_EQ(kat->msg_len, 1u);
        EXPECT_EQ(kat->sig_len, 7856u);
        EXPECT_EQ(kat->num_chunks, 17u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_sparse_verify_pub_key(kat)) &
                3u,
            0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_sparse_verify_msg(kat)) & 3u,
            0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_sparse_verify_chunks(kat)) &
                3u,
            0u);
        std::vector<uint8_t> expanded(kat->sig_len);
        EXPECT_TRUE(fips_kat_sparse_sig_unpack(
            kat, entry->size, expanded.data(), expanded.size()));
        break;
      }
      case kFipsKatAlgRsa4096: {
        const auto *kat =
            static_cast<const asymmetric_sign_kat_data_t *>(payload);
        EXPECT_EQ(kat->reserved, 0u);
        EXPECT_EQ(entry->size, 1568u);
        EXPECT_EQ(entry->size, fips_kat_asym_sign_expected_size(kat));
        EXPECT_EQ(kat->priv_key_len, 1024u);
        EXPECT_EQ(kat->ephemeral_len, 4u);
        EXPECT_EQ(kat->msg_len, 13u);
        EXPECT_EQ(kat->sig_len1, 512u);
        EXPECT_EQ(kat->sig_len2, 0u);
        const uint8_t *e = fips_kat_asym_sign_ephemeral(kat);
        EXPECT_EQ(e[0], 0x01u);
        EXPECT_EQ(e[1], 0x00u);
        EXPECT_EQ(e[2], 0x01u);
        EXPECT_EQ(e[3], 0x00u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_sign_priv_key(kat)) & 3u,
            0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(e) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_asym_sign_msg(kat)) & 3u,
                  0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_sign_sig1(kat)) & 3u, 0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_sign_sig2(kat)) & 3u, 0u);
        break;
      }
      case kFipsKatAlgEcdsaP256Sign:
      case kFipsKatAlgEcdsaP384Sign:
      case kFipsKatAlgEd25519Sign: {
        const auto *kat =
            static_cast<const asymmetric_sign_kat_data_t *>(payload);
        EXPECT_EQ(kat->reserved, 0u) << "alg_id=" << id;
        EXPECT_EQ(entry->size, fips_kat_asym_sign_expected_size(kat))
            << "alg_id=" << id;
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_sign_priv_key(kat)) & 3u,
            0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_sign_ephemeral(kat)) & 3u,
            0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_asym_sign_msg(kat)) & 3u,
                  0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_sign_sig1(kat)) & 3u, 0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_asym_sign_sig2(kat)) & 3u, 0u);
        break;
      }
      case kFipsKatAlgEcdhP256:
      case kFipsKatAlgEcdhP384:
      case kFipsKatAlgX25519: {
        const auto *kat = static_cast<const ecdh_kat_data_t *>(payload);
        EXPECT_EQ(entry->size, fips_kat_ecdh_expected_size(kat))
            << "alg_id=" << id;
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_ecdh_priv_key(kat)) & 3u,
                  0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_ecdh_pub_key1(kat)) & 3u,
                  0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_ecdh_pub_key2(kat)) & 3u,
                  0u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_ecdh_shared_secret(kat)) & 3u,
            0u);
        break;
      }
      case kFipsKatAlgMldsa87: {
        const auto *kat = static_cast<const mldsa_kat_data_t *>(payload);
        EXPECT_EQ(kat->num_cases, 5u);
        EXPECT_EQ(kat->reserved, 0u);
        EXPECT_EQ(entry->size, fips_kat_mldsa_expected_size(kat));
        break;
      }
      case kFipsKatAlgMlkem1024: {
        const auto *kat = static_cast<const kem_kat_data_t *>(payload);
        EXPECT_EQ(entry->size, fips_kat_kem_expected_size(kat));
        EXPECT_EQ(kat->exp_pk_hash_len, 32u);
        EXPECT_EQ(kat->exp_ct_hash_len, 32u);
        EXPECT_EQ(kat->exp_ss_len, 32u);
        EXPECT_EQ(
            reinterpret_cast<uintptr_t>(fips_kat_kem_exp_pk_hash(kat)) & 3u,
            0u);
        break;
      }
      case kFipsKatAlgDrbgAes256: {
        const auto *kat = static_cast<const drbg_kat_data_t *>(payload);
        EXPECT_EQ(entry->size, sizeof(drbg_kat_data_t));
        EXPECT_EQ(kat->seed_len, 48u);
        EXPECT_EQ(kat->expected_output_len, 64u);
        EXPECT_EQ(kat->state_instantiate.reseed_counter, 0u);
        EXPECT_EQ(kat->state_generate1.reseed_counter, 1u);
        EXPECT_EQ(kat->state_generate2.reseed_counter, 1u);
        break;
      }
      case kFipsKatAlgHkdfSha2_384: {
        const auto *kat = static_cast<const hkdf_kat_data_t *>(payload);
        EXPECT_EQ(kat->reserved, 0u);
        EXPECT_EQ(entry->size, fips_kat_hkdf_expected_size(kat));
        EXPECT_EQ(kat->ikm_len, 48u);
        EXPECT_EQ(kat->salt_len, 13u);
        EXPECT_EQ(kat->info_len, 10u);
        EXPECT_EQ(kat->prk_len, 48u);
        EXPECT_EQ(kat->okm_len, 64u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_hkdf_prk(kat)) & 3u, 0u);
        EXPECT_EQ(reinterpret_cast<uintptr_t>(fips_kat_hkdf_okm(kat)) & 3u, 0u);
        break;
      }
      default:
        FAIL() << "Unhandled algorithm_id " << id;
    }
  }

  EXPECT_EQ(seen_ids.size(), 30u);

  // Confirm all 30 payload intervals are strictly non-overlapping.
  std::sort(intervals.begin(), intervals.end());
  for (size_t i = 1; i < intervals.size(); ++i) {
    EXPECT_LE(intervals[i - 1].second, intervals[i].first)
        << "Overlapping payloads at sorted index " << i;
  }
}

}  // namespace
