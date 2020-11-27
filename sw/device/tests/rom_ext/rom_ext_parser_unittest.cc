// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/rom_exts/rom_ext_manifest_parser.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"
#include "sw/device/rom_exts/manifest.h"

namespace rom_ext_parser_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Each;
using testing::ElementsAreArray;
using testing::Eq;
using testing::Test;

class ParserTest : public Test, public MmioTest {
 protected:
  rom_ext_manifest_t params_ = {
      .base_addr =
          (mmio_region_t){
              .mock = dev().region(),
          },
      .slot = kRomExtManifestSlotA,
  };
};

class IdentifierGetTest : public ParserTest {};

TEST_F(IdentifierGetTest, Success) {
  EXPECT_READ32(ROM_EXT_MANIFEST_IDENTIFIER_OFFSET, 0xa5a5a5a5);
  EXPECT_EQ(rom_ext_get_identifier(params_), 0xa5a5a5a5);
}

class SignatureGetTest : public ParserTest {
 protected:
  SignatureGetTest() {
    for (uint32_t i = 0; i < kSizeInWords_; ++i) {
      src_.data[i] = dev().GarbageMemory<uint32_t>();
    }
  }

  const uint32_t kSizeInWords_ = ROM_EXT_IMAGE_SIGNATURE_SIZE_WORDS;
  rom_ext_signature_t src_;
};

TEST_F(SignatureGetTest, NullArgs) {
  EXPECT_FALSE(rom_ext_get_signature(params_, nullptr));
}

TEST_F(SignatureGetTest, Success) {
  rom_ext_signature_t dst;

  auto offset_word_0 = ROM_EXT_IMAGE_SIGNATURE_OFFSET;
  for (size_t i = 0; i < kSizeInWords_; ++i) {
    auto offset = offset_word_0 + (i * sizeof(uint32_t));
    EXPECT_READ32(offset, src_.data[i]);
  }

  EXPECT_TRUE(rom_ext_get_signature(params_, &dst));
  EXPECT_THAT(src_.data, ElementsAreArray(dst.data));
}

class RangesGetTest : public ParserTest {
 protected:
  testing::Matcher<rom_ext_ranges_t> EqualsRanges(const rom_ext_ranges_t &rhs) {
    return testing::AllOf(
        testing::Field("image_start", &rom_ext_ranges_t::image_start,
                       rhs.image_start),
        testing::Field("signed_area_start",
                       &rom_ext_ranges_t::signed_area_start,
                       rhs.signed_area_start),
        testing::Field("image_end", &rom_ext_ranges_t::image_end,
                       rhs.image_end));
  }
};

TEST_F(RangesGetTest, Success) {
  EXPECT_READ32(ROM_EXT_IMAGE_LENGTH_OFFSET, 0xa5a5a5a5);

  rom_ext_ranges_t expected = {
      .image_start = kRomExtManifestSlotA,
      .signed_area_start =
          kRomExtManifestSlotA + ROM_EXT_SIGNED_AREA_START_OFFSET,
      .image_end = kRomExtManifestSlotA + 0xa5a5a5a5,
  };

  EXPECT_THAT(rom_ext_get_ranges(params_), EqualsRanges(expected));
}

class ImageVersionGetTest : public ParserTest {};

TEST_F(ImageVersionGetTest, Success) {
  EXPECT_READ32(ROM_EXT_IMAGE_VERSION_OFFSET, 0xa5a5a5a5);
  EXPECT_EQ(rom_ext_get_version(params_), 0xa5a5a5a5);
}

class ImageTimestampGetTest : public ParserTest {};

TEST_F(ImageTimestampGetTest, Success) {
  EXPECT_READ32(ROM_EXT_IMAGE_TIMESTAMP_OFFSET, 0xcdcdcdcd);
  EXPECT_READ32(ROM_EXT_IMAGE_TIMESTAMP_OFFSET + sizeof(uint32_t), 0xabababab);

  EXPECT_EQ(rom_ext_get_timestamp(params_), 0xababababcdcdcdcd);
}

class SignatureKeyPublicExponentGetTest : public ParserTest {};

TEST_F(SignatureKeyPublicExponentGetTest, Success) {
  EXPECT_READ32(ROM_EXT_SIGNATURE_KEY_PUBLIC_EXPONENT_OFFSET, 0xa5a5a5a5);
  EXPECT_EQ(rom_ext_get_signature_key_public_exponent(params_), 0xa5a5a5a5);
}

class UsageConstraintsGetTest : public ParserTest {};

TEST_F(UsageConstraintsGetTest, Success) {
  EXPECT_READ32(ROM_EXT_USAGE_CONSTRAINTS_OFFSET, 0xa5a5a5a5);
  EXPECT_EQ(rom_ext_get_usage_constraints(params_), 0xa5a5a5a5);
}

class PeripheralLockdownInfoGetTest : public ParserTest {
 protected:
  PeripheralLockdownInfoGetTest() {
    for (uint32_t i = 0; i < kSizeInWords_; ++i) {
      src_.data[i] = dev().GarbageMemory<uint32_t>();
    }
  }

  const uint32_t kSizeInWords_ = ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_WORDS;
  rom_ext_lockdown_info_t src_;
};

TEST_F(PeripheralLockdownInfoGetTest, NullArgs) {
  EXPECT_FALSE(rom_ext_get_peripheral_lockdown_info(params_, nullptr));
}

TEST_F(PeripheralLockdownInfoGetTest, Success) {
  rom_ext_lockdown_info_t dst;

  auto offset_word_0 = ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_OFFSET;
  for (size_t i = 0; i < kSizeInWords_; ++i) {
    auto offset = offset_word_0 + (i * sizeof(uint32_t));
    EXPECT_READ32(offset, src_.data[i]);
  }

  EXPECT_TRUE(rom_ext_get_peripheral_lockdown_info(params_, &dst));
  EXPECT_THAT(src_.data, ElementsAreArray(dst.data));
}

class SignatureKeyModulusGetTest : public ParserTest {
 protected:
  SignatureKeyModulusGetTest() {
    for (uint32_t i = 0; i < kSizeInWords_; ++i) {
      src_.data[i] = dev().GarbageMemory<uint32_t>();
    }
  }

  const uint32_t kSizeInWords_ = ROM_EXT_SIGNATURE_KEY_MODULUS_SIZE_WORDS;
  rom_ext_signature_key_modulus_t src_;
};

TEST_F(SignatureKeyModulusGetTest, NullArgs) {
  EXPECT_FALSE(rom_ext_get_signature_key_modulus(params_, nullptr));
}

TEST_F(SignatureKeyModulusGetTest, Success) {
  rom_ext_signature_key_modulus_t dst;

  auto offset_word_0 = ROM_EXT_SIGNATURE_KEY_MODULUS_OFFSET;
  for (size_t i = 0; i < kSizeInWords_; ++i) {
    auto offset = offset_word_0 + (i * sizeof(uint32_t));
    EXPECT_READ32(offset, src_.data[i]);
  }

  EXPECT_TRUE(rom_ext_get_signature_key_modulus(params_, &dst));
  EXPECT_THAT(src_.data, ElementsAreArray(dst.data));
}

class ExtensionGetTest : public ParserTest {
 protected:
  testing::Matcher<rom_ext_extension_t> Eq(const rom_ext_extension_t &rhs) {
    return testing::AllOf(
        testing::Field("checksum", &rom_ext_extension_t::checksum,
                       rhs.checksum),
        testing::Field("address", &rom_ext_extension_t::address, rhs.address));
  }
};

TEST_F(ExtensionGetTest, NullArgs) {
  EXPECT_FALSE(rom_ext_get_extension(params_, kRomExtExtensionId0, nullptr));
  EXPECT_FALSE(rom_ext_get_extension(params_, kRomExtExtensionId1, nullptr));
  EXPECT_FALSE(rom_ext_get_extension(params_, kRomExtExtensionId2, nullptr));
  EXPECT_FALSE(rom_ext_get_extension(params_, kRomExtExtensionId3, nullptr));
}

TEST_F(ExtensionGetTest, Success) {
  EXPECT_READ32(ROM_EXT_EXTENSION0_OFFSET_OFFSET, 0x10);
  EXPECT_READ32(ROM_EXT_EXTENSION0_CHECKSUM_OFFSET, 0xbbbbbbbb);

  rom_ext_extension_t ext0;
  rom_ext_extension_t ext0_expected = {
      .address = (void *)(kRomExtManifestSlotA + 0x10), .checksum = 0xbbbbbbbb,
  };
  EXPECT_TRUE(rom_ext_get_extension(params_, kRomExtExtensionId0, &ext0));
  EXPECT_THAT(ext0, Eq(ext0_expected));

  EXPECT_READ32(ROM_EXT_EXTENSION1_OFFSET_OFFSET, 0x20);
  EXPECT_READ32(ROM_EXT_EXTENSION1_CHECKSUM_OFFSET, 0xdddddddd);

  rom_ext_extension_t ext1;
  rom_ext_extension_t ext1_expected = {
      .address = (void *)(kRomExtManifestSlotA + 0x20), .checksum = 0xdddddddd,
  };
  EXPECT_TRUE(rom_ext_get_extension(params_, kRomExtExtensionId1, &ext1));
  EXPECT_THAT(ext1, Eq(ext1_expected));

  EXPECT_READ32(ROM_EXT_EXTENSION2_OFFSET_OFFSET, 0x30);
  EXPECT_READ32(ROM_EXT_EXTENSION2_CHECKSUM_OFFSET, 0xffffffff);

  rom_ext_extension_t ext2;
  rom_ext_extension_t ext2_expected = {
      .address = (void *)(kRomExtManifestSlotA + 0x30), .checksum = 0xffffffff,
  };
  EXPECT_TRUE(rom_ext_get_extension(params_, kRomExtExtensionId2, &ext2));
  EXPECT_THAT(ext2, Eq(ext2_expected));

  EXPECT_READ32(ROM_EXT_EXTENSION3_OFFSET_OFFSET, 0x40);
  EXPECT_READ32(ROM_EXT_EXTENSION3_CHECKSUM_OFFSET, 0x66666666);

  rom_ext_extension_t ext3;
  rom_ext_extension_t ext3_expected = {
      .address = (void *)(kRomExtManifestSlotA + 0x40), .checksum = 0x66666666,
  };
  EXPECT_TRUE(rom_ext_get_extension(params_, kRomExtExtensionId3, &ext3));
  EXPECT_THAT(ext3, Eq(ext3_expected));
}

class EntryGetTest : public ParserTest {};

TEST_F(EntryGetTest, Success) {
  EXPECT_EQ(rom_ext_get_entry(params_),
            kRomExtManifestSlotA + ROM_EXT_ENTRY_POINT_OFFSET);
}

class InterruptVectorGetTest : public ParserTest {};

TEST_F(InterruptVectorGetTest, Success) {
  uintptr_t mtvec_val = rom_ext_get_interrupt_vector(params_);
  uintptr_t vec_addr = kRomExtManifestSlotA + ROM_EXT_INTERRUPT_VECTOR_OFFSET;

  const bitfield_field32_t most_significant_30_bits = {
      .mask = 0x3fffffff,
      .index = 2,
  };

  const bitfield_field32_t least_significant_2_bits = {
      .mask = 0x3,
      .index = 0,
  };

  EXPECT_EQ(bitfield_field32_read(mtvec_val, most_significant_30_bits),
            bitfield_field32_read(vec_addr, most_significant_30_bits));
  EXPECT_EQ(bitfield_field32_read(mtvec_val, least_significant_2_bits), 0x1);
}

}  // namespace
}  // namespace rom_ext_parser_unittest
