// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#include <set>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "sw/device/lib/dif/dif_padctrl.h"
#include "padctrl_regs.h"  // Generated.

/**
 * Helper macros for commonly repeated patterns in tests below, they are
 * implemented as macros rather than functions so error messages generated with
 * __LINE__ relate to the actual test. Macros are used to make the test intent
 * easier to read
 */

/**
 * Expect a device init that succeeds. This sets up an instance of
 * `dif_padctrl_t` for further testing
 */
#define EXPECT_DEVICE_INIT_OK \
  EXPECT_EQ(dif_padctrl_init(dev().region(), &dif_padctrl_), kDifPadctrlOk)

/**
 * Expect a read of the REGEN register to check the lock bit
 *
 * @param locked Whether REGEN will report padctrl is locked or not
 */
#define EXPECT_LOCK_CHECK(locked) \
  EXPECT_READ32(PADCTRL_REGEN_REG_OFFSET, locked ? 0 : 1)

namespace dif_padctrl_test {
namespace {

class DifPadctrlTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  /**
   * Attribute field informtion for a pad (MIO or DIO)
   */
  struct AttrField {
    ptrdiff_t reg_offset; /**< Register offset for register holding field. */
    uintptr_t bit_mask;   /**< Bit mask of field. */
    uintptr_t bit_offset; /**< Offset of field within register. */
    uint32_t pad_num;     /**< Which pad it corresponds to. */
  };

  // Setup attribute field info for all DIO and MIO pads.
  // This is intentionally simple and straight-forward, just manually putting
  // all of the auto-generated register info into AttrField structs rather than
  // generating it in the obvious way to avoid some issue around the calcuation
  // of the AttrField data occurring. This way we're guaranteed we're using what
  // reggen has output (and generated RTL based on).
  std::vector<AttrField> dio_attr_fields_ = {
      {PADCTRL_DIO_PADS0_REG_OFFSET, PADCTRL_DIO_PADS0_ATTR0_MASK,
       PADCTRL_DIO_PADS0_ATTR0_OFFSET, 0},
      {PADCTRL_DIO_PADS0_REG_OFFSET, PADCTRL_DIO_PADS0_ATTR1_MASK,
       PADCTRL_DIO_PADS0_ATTR1_OFFSET, 1},
      {PADCTRL_DIO_PADS0_REG_OFFSET, PADCTRL_DIO_PADS0_ATTR2_MASK,
       PADCTRL_DIO_PADS0_ATTR2_OFFSET, 2},
      {PADCTRL_DIO_PADS0_REG_OFFSET, PADCTRL_DIO_PADS0_ATTR3_MASK,
       PADCTRL_DIO_PADS0_ATTR3_OFFSET, 3},
      {PADCTRL_DIO_PADS1_REG_OFFSET, PADCTRL_DIO_PADS1_ATTR4_MASK,
       PADCTRL_DIO_PADS1_ATTR4_OFFSET, 4},
      {PADCTRL_DIO_PADS1_REG_OFFSET, PADCTRL_DIO_PADS1_ATTR5_MASK,
       PADCTRL_DIO_PADS1_ATTR5_OFFSET, 5},
      {PADCTRL_DIO_PADS1_REG_OFFSET, PADCTRL_DIO_PADS1_ATTR6_MASK,
       PADCTRL_DIO_PADS1_ATTR6_OFFSET, 6},
      {PADCTRL_DIO_PADS1_REG_OFFSET, PADCTRL_DIO_PADS1_ATTR7_MASK,
       PADCTRL_DIO_PADS1_ATTR7_OFFSET, 7},
      {PADCTRL_DIO_PADS2_REG_OFFSET, PADCTRL_DIO_PADS2_ATTR8_MASK,
       PADCTRL_DIO_PADS2_ATTR8_OFFSET, 8},
      {PADCTRL_DIO_PADS2_REG_OFFSET, PADCTRL_DIO_PADS2_ATTR9_MASK,
       PADCTRL_DIO_PADS2_ATTR9_OFFSET, 9},
      {PADCTRL_DIO_PADS2_REG_OFFSET, PADCTRL_DIO_PADS2_ATTR10_MASK,
       PADCTRL_DIO_PADS2_ATTR10_OFFSET, 10},
      {PADCTRL_DIO_PADS2_REG_OFFSET, PADCTRL_DIO_PADS2_ATTR11_MASK,
       PADCTRL_DIO_PADS2_ATTR11_OFFSET, 11},
      {PADCTRL_DIO_PADS3_REG_OFFSET, PADCTRL_DIO_PADS3_ATTR12_MASK,
       PADCTRL_DIO_PADS3_ATTR12_OFFSET, 12},
      {PADCTRL_DIO_PADS3_REG_OFFSET, PADCTRL_DIO_PADS3_ATTR13_MASK,
       PADCTRL_DIO_PADS3_ATTR13_OFFSET, 13},
      {PADCTRL_DIO_PADS3_REG_OFFSET, PADCTRL_DIO_PADS3_ATTR14_MASK,
       PADCTRL_DIO_PADS3_ATTR14_OFFSET, 14},
  };

  std::vector<AttrField> mio_attr_fields_ = {
      {PADCTRL_MIO_PADS0_REG_OFFSET, PADCTRL_MIO_PADS0_ATTR0_MASK,
       PADCTRL_MIO_PADS0_ATTR0_OFFSET, 0},
      {PADCTRL_MIO_PADS0_REG_OFFSET, PADCTRL_MIO_PADS0_ATTR1_MASK,
       PADCTRL_MIO_PADS0_ATTR1_OFFSET, 1},
      {PADCTRL_MIO_PADS0_REG_OFFSET, PADCTRL_MIO_PADS0_ATTR2_MASK,
       PADCTRL_MIO_PADS0_ATTR2_OFFSET, 2},
      {PADCTRL_MIO_PADS0_REG_OFFSET, PADCTRL_MIO_PADS0_ATTR3_MASK,
       PADCTRL_MIO_PADS0_ATTR3_OFFSET, 3},
      {PADCTRL_MIO_PADS1_REG_OFFSET, PADCTRL_MIO_PADS1_ATTR4_MASK,
       PADCTRL_MIO_PADS1_ATTR4_OFFSET, 4},
      {PADCTRL_MIO_PADS1_REG_OFFSET, PADCTRL_MIO_PADS1_ATTR5_MASK,
       PADCTRL_MIO_PADS1_ATTR5_OFFSET, 5},
      {PADCTRL_MIO_PADS1_REG_OFFSET, PADCTRL_MIO_PADS1_ATTR6_MASK,
       PADCTRL_MIO_PADS1_ATTR6_OFFSET, 6},
      {PADCTRL_MIO_PADS1_REG_OFFSET, PADCTRL_MIO_PADS1_ATTR7_MASK,
       PADCTRL_MIO_PADS1_ATTR7_OFFSET, 7},
      {PADCTRL_MIO_PADS2_REG_OFFSET, PADCTRL_MIO_PADS2_ATTR8_MASK,
       PADCTRL_MIO_PADS2_ATTR8_OFFSET, 8},
      {PADCTRL_MIO_PADS2_REG_OFFSET, PADCTRL_MIO_PADS2_ATTR9_MASK,
       PADCTRL_MIO_PADS2_ATTR9_OFFSET, 9},
      {PADCTRL_MIO_PADS2_REG_OFFSET, PADCTRL_MIO_PADS2_ATTR10_MASK,
       PADCTRL_MIO_PADS2_ATTR10_OFFSET, 10},
      {PADCTRL_MIO_PADS2_REG_OFFSET, PADCTRL_MIO_PADS2_ATTR11_MASK,
       PADCTRL_MIO_PADS2_ATTR11_OFFSET, 11},
      {PADCTRL_MIO_PADS3_REG_OFFSET, PADCTRL_MIO_PADS3_ATTR12_MASK,
       PADCTRL_MIO_PADS3_ATTR12_OFFSET, 12},
      {PADCTRL_MIO_PADS3_REG_OFFSET, PADCTRL_MIO_PADS3_ATTR13_MASK,
       PADCTRL_MIO_PADS3_ATTR13_OFFSET, 13},
      {PADCTRL_MIO_PADS3_REG_OFFSET, PADCTRL_MIO_PADS3_ATTR14_MASK,
       PADCTRL_MIO_PADS3_ATTR14_OFFSET, 14},
      {PADCTRL_MIO_PADS3_REG_OFFSET, PADCTRL_MIO_PADS3_ATTR15_MASK,
       PADCTRL_MIO_PADS3_ATTR15_OFFSET, 15},
      {PADCTRL_MIO_PADS4_REG_OFFSET, PADCTRL_MIO_PADS4_ATTR16_MASK,
       PADCTRL_MIO_PADS4_ATTR16_OFFSET, 16},
      {PADCTRL_MIO_PADS4_REG_OFFSET, PADCTRL_MIO_PADS4_ATTR17_MASK,
       PADCTRL_MIO_PADS4_ATTR17_OFFSET, 17},
      {PADCTRL_MIO_PADS4_REG_OFFSET, PADCTRL_MIO_PADS4_ATTR18_MASK,
       PADCTRL_MIO_PADS4_ATTR18_OFFSET, 18},
      {PADCTRL_MIO_PADS4_REG_OFFSET, PADCTRL_MIO_PADS4_ATTR19_MASK,
       PADCTRL_MIO_PADS4_ATTR19_OFFSET, 19},
      {PADCTRL_MIO_PADS5_REG_OFFSET, PADCTRL_MIO_PADS5_ATTR20_MASK,
       PADCTRL_MIO_PADS5_ATTR20_OFFSET, 20},
      {PADCTRL_MIO_PADS5_REG_OFFSET, PADCTRL_MIO_PADS5_ATTR21_MASK,
       PADCTRL_MIO_PADS5_ATTR21_OFFSET, 21},
      {PADCTRL_MIO_PADS5_REG_OFFSET, PADCTRL_MIO_PADS5_ATTR22_MASK,
       PADCTRL_MIO_PADS5_ATTR22_OFFSET, 22},
      {PADCTRL_MIO_PADS5_REG_OFFSET, PADCTRL_MIO_PADS5_ATTR23_MASK,
       PADCTRL_MIO_PADS5_ATTR23_OFFSET, 23},
      {PADCTRL_MIO_PADS6_REG_OFFSET, PADCTRL_MIO_PADS6_ATTR24_MASK,
       PADCTRL_MIO_PADS6_ATTR24_OFFSET, 24},
      {PADCTRL_MIO_PADS6_REG_OFFSET, PADCTRL_MIO_PADS6_ATTR25_MASK,
       PADCTRL_MIO_PADS6_ATTR25_OFFSET, 25},
      {PADCTRL_MIO_PADS6_REG_OFFSET, PADCTRL_MIO_PADS6_ATTR26_MASK,
       PADCTRL_MIO_PADS6_ATTR26_OFFSET, 26},
      {PADCTRL_MIO_PADS6_REG_OFFSET, PADCTRL_MIO_PADS6_ATTR27_MASK,
       PADCTRL_MIO_PADS6_ATTR27_OFFSET, 27},
      {PADCTRL_MIO_PADS7_REG_OFFSET, PADCTRL_MIO_PADS7_ATTR28_MASK,
       PADCTRL_MIO_PADS7_ATTR28_OFFSET, 28},
      {PADCTRL_MIO_PADS7_REG_OFFSET, PADCTRL_MIO_PADS7_ATTR29_MASK,
       PADCTRL_MIO_PADS7_ATTR29_OFFSET, 29},
      {PADCTRL_MIO_PADS7_REG_OFFSET, PADCTRL_MIO_PADS7_ATTR30_MASK,
       PADCTRL_MIO_PADS7_ATTR30_OFFSET, 30},
      {PADCTRL_MIO_PADS7_REG_OFFSET, PADCTRL_MIO_PADS7_ATTR31_MASK,
       PADCTRL_MIO_PADS7_ATTR31_OFFSET, 31},
  };

  // Vector of all attributes, initialise with the basic attributes.
  std::vector<dif_padctrl_attr_t> attributes_ = {
      kDifPadctrlAttrIOInvert, kDifPadctrlAttrOpenDrain,
      kDifPadctrlAttrPullDown, kDifPadctrlAttrPullUp,
      kDifPadctrlAttrKeeper,   kDifPadctrlAttrWeakDrive,
  };

  /**
   * Expect a sequence of writes that reset all attributes to the given
   * `reset_val`
   */
  void ExpectReset(uint32_t reset_val) {
    // Extract unique register offsets from dio_attr_fields_.
    // std::set is required to keep ordering.
    std::set<ptrdiff_t> dio_pad_reg_offsets;
    for (auto dio_attr_field : dio_attr_fields_) {
      dio_pad_reg_offsets.insert(dio_attr_field.reg_offset);
    }

    // Iterate through in ascending order, expecting a write of 0 to each.
    for (auto dio_reg_offset : dio_pad_reg_offsets) {
      EXPECT_WRITE32(dio_reg_offset, reset_val);
    }

    // Extract unique register offsets from mio_attr_fields_
    std::set<ptrdiff_t> mio_pad_reg_offsets;
    for (auto mio_attr_field : mio_attr_fields_) {
      mio_pad_reg_offsets.insert(mio_attr_field.reg_offset);
    }

    // Iterate through in ascending order, expecting a write of 0 to each.
    for (auto mio_reg_offset : mio_pad_reg_offsets) {
      EXPECT_WRITE32(mio_reg_offset, reset_val);
    }
  }

  /**
   * Expects the read required to read an attribute field.
   *
   * @param attr_field Which attribute field we expect to read
   * @param existing_attrs What existing attributes will be in the read
   * @return The bits seen by the read
   */
  uint32_t ExpectAttrFieldRead(const AttrField &attr_field,
                               dif_padctrl_attr_t existing_attrs) {
    EXPECT_EQ(existing_attrs & ~attr_field.bit_mask, 0);

    uint32_t other_field_bits = dev().GarbageMemory<uint32_t>() &
                                ~(attr_field.bit_mask << attr_field.bit_offset);
    uint32_t existing_reg_bits =
        other_field_bits | (existing_attrs << attr_field.bit_offset);
    EXPECT_READ32(attr_field.reg_offset, existing_reg_bits);

    return existing_reg_bits;
  }

  /**
   * Attribute field update kinds
   */
  enum AttrFieldUpdateKind {
    kAttrFieldUpdateEnable,  /**< Enable attributes corresponding to set bits */
    kAttrFieldUpdateDisable, /**< Disable attributes corresponding to set bits
                              */
    kAttrFieldUpdateWrite,   /**< Set attributes to provided bits */
  };

  /**
   * Expects a read and write sequence required to update attributes
   *
   * @param attr_field Which attribute field we expect to update
   * @param existing_attrs What existing attributes will be seen in the
   * initial read
   * @param update_attrs Attribute update to apply, how these are applied
   * depends upon `update_kind`
   * @param update_kind What kind of update to do
   */
  void ExpectAttrFieldUpdate(const AttrField &attr_field,
                             dif_padctrl_attr_t existing_attrs,
                             dif_padctrl_attr_t update_attrs,
                             AttrFieldUpdateKind update_kind) {
    // Check the attributes we want to update are valid
    EXPECT_EQ(update_attrs & ~attr_field.bit_mask, 0);
    EXPECT_LOCK_CHECK(false);

    // Expect a read that will give us the existing attributes, retaining the
    // bits the that will be returned from that read.
    uint32_t existing_reg_bits =
        ExpectAttrFieldRead(attr_field, existing_attrs);
    uint32_t attr_field_update_bits = update_attrs << attr_field.bit_offset;

    // Update the bits from the read to include the attribute update.
    uint32_t new_reg_bits;
    switch (update_kind) {
      case kAttrFieldUpdateEnable:
        new_reg_bits = existing_reg_bits | attr_field_update_bits;
        break;
      case kAttrFieldUpdateDisable:
        new_reg_bits = existing_reg_bits & ~attr_field_update_bits;
        break;
      case kAttrFieldUpdateWrite:
        new_reg_bits = (existing_reg_bits &
                        ~(attr_field.bit_mask << attr_field.bit_offset)) |
                       attr_field_update_bits;
        break;
    }

    // Expect a write to perform the attribute update.
    EXPECT_WRITE32(attr_field.reg_offset, new_reg_bits);
  }

  /**
   * Tests various attribute enables for success
   *
   * @param attr_field The attribute field to test
   * @param pad_kind What kind of pad `attr_field` is for
   */
  void TestEnableAttrSuccess(const AttrField &attr_field,
                             dif_padctrl_pad_kind_t pad_kind) {
    EXPECT_DEVICE_INIT_OK;

    dif_padctrl_attr_t initial_attrs = static_cast<dif_padctrl_attr_t>(
        kDifPadctrlAttrIOInvert | kDifPadctrlAttrWeakDrive);
    dif_padctrl_attr_t enable_attrs = static_cast<dif_padctrl_attr_t>(
        kDifPadctrlAttrPullDown | kDifPadctrlAttrKeeper);

    // Test enabling attributes when others are already enabled.
    ExpectAttrFieldUpdate(attr_field, initial_attrs, enable_attrs,
                          kAttrFieldUpdateEnable);
    EXPECT_EQ(dif_padctrl_enable_attrs(&dif_padctrl_, pad_kind,
                                       attr_field.pad_num, enable_attrs),
              kDifPadctrlChangeAttrOk);

    // For every attribute test enabling when no other attributes are enabled
    for (auto attr : attributes_) {
      ExpectAttrFieldUpdate(attr_field, kDifPadctrlAttrNone, attr,
                            kAttrFieldUpdateEnable);
      EXPECT_EQ(dif_padctrl_enable_attrs(&dif_padctrl_, pad_kind,
                                         attr_field.pad_num, attr),
                kDifPadctrlChangeAttrOk);
    }
  }

  /**
   * Tests various attribute disables for success
   *
   * @param attr_field The attribute field to test
   * @param pad_kind What kind of pad `attr_field` is for
   */
  void TestDisableAttrSuccess(const AttrField &attr_field,
                              dif_padctrl_pad_kind_t pad_kind) {
    EXPECT_DEVICE_INIT_OK;

    // Test disabling attributes when others are already enabled.
    dif_padctrl_attr_t initial_attrs = static_cast<dif_padctrl_attr_t>(
        kDifPadctrlAttrIOInvert | kDifPadctrlAttrWeakDrive |
        kDifPadctrlAttrPullDown | kDifPadctrlAttrKeeper);
    dif_padctrl_attr_t disable_attrs = static_cast<dif_padctrl_attr_t>(
        kDifPadctrlAttrIOInvert | kDifPadctrlAttrKeeper);
    ExpectAttrFieldUpdate(attr_field, initial_attrs, disable_attrs,
                          kAttrFieldUpdateDisable);
    EXPECT_EQ(dif_padctrl_disable_attrs(&dif_padctrl_, pad_kind,
                                        attr_field.pad_num, disable_attrs),
              kDifPadctrlChangeAttrOk);

    // For every attribute test disabling it when only it is enabled.
    for (auto attr : attributes_) {
      ExpectAttrFieldUpdate(attr_field, attr, attr, kAttrFieldUpdateDisable);
      EXPECT_EQ(dif_padctrl_disable_attrs(&dif_padctrl_, pad_kind,
                                          attr_field.pad_num, attr),
                kDifPadctrlChangeAttrOk);
    }
  }

  /**
   * Tests various attribute writes for success
   *
   * @param attr_field The attribute field to test
   * @param pad_kind What kind of pad `attr_field` is for
   */
  void TestWriteAttrSuccess(const AttrField &attr_field,
                            dif_padctrl_pad_kind_t pad_kind) {
    EXPECT_DEVICE_INIT_OK;

    // Test writing attributes when others are already enabled.
    dif_padctrl_attr_t initial_attrs = static_cast<dif_padctrl_attr_t>(
        kDifPadctrlAttrIOInvert | kDifPadctrlAttrWeakDrive);
    dif_padctrl_attr_t new_attrs = static_cast<dif_padctrl_attr_t>(
        kDifPadctrlAttrPullDown | kDifPadctrlAttrKeeper);
    ExpectAttrFieldUpdate(attr_field, initial_attrs, new_attrs,
                          kAttrFieldUpdateWrite);
    EXPECT_EQ(dif_padctrl_write_attrs(&dif_padctrl_, pad_kind,
                                      attr_field.pad_num, new_attrs),
              kDifPadctrlChangeAttrOk);

    // For every attribute test writing it when other attributes are already
    // enabled
    for (auto attr : attributes_) {
      ExpectAttrFieldUpdate(attr_field, initial_attrs, attr,
                            kAttrFieldUpdateWrite);
      EXPECT_EQ(dif_padctrl_write_attrs(&dif_padctrl_, pad_kind,
                                        attr_field.pad_num, attr),
                kDifPadctrlChangeAttrOk);
    }
  }

  /**
   * Tests a failure to enable an attribute due to a conflict
   *
   * @param attr_field The attribute field to test
   * @param pad_kind What kind of pad `attr_field` is for
   */
  void TestEnableAttrFailureConflict(const AttrField &attr_field,
                                     dif_padctrl_pad_kind_t pad_kind) {
    EXPECT_DEVICE_INIT_OK;
    EXPECT_LOCK_CHECK(false);

    // Expect a read of `attr_field` with a couple of attributes set.
    dif_padctrl_attr_t initial_attrs = static_cast<dif_padctrl_attr_t>(
        kDifPadctrlAttrIOInvert | kDifPadctrlAttrPullUp);
    ExpectAttrFieldRead(attr_field, initial_attrs);

    // Attempt to set an attribute that conflicts with the currently set ones
    // expecting the appropriate error.
    EXPECT_EQ(
        dif_padctrl_enable_attrs(&dif_padctrl_, pad_kind, attr_field.pad_num,
                                 kDifPadctrlAttrPullDown),
        kDifPadctrlChangeAttrConflict);
  }

  /**
   * Tests a failure to write attributes due to a conflict
   *
   * @param attr_field The attribute field to test
   * @param pad_kind What kind of pad `attr_field` is for
   */
  void TestWriteAttrFailureConflict(const AttrField &attr_field,
                                    dif_padctrl_pad_kind_t pad_kind) {
    EXPECT_DEVICE_INIT_OK;
    EXPECT_LOCK_CHECK(false);

    // Expect a read of `attr_field` with an attribute set.
    ExpectAttrFieldRead(attr_field,
                        dif_padctrl_attr_t(kDifPadctrlAttrIOInvert));

    // Write back attributes that conflict with each other and not the attribute
    // that was initially set expecting the appropriate error.
    dif_padctrl_attr_t conflicting_attrs =
        dif_padctrl_attr_t(kDifPadctrlAttrPullUp | kDifPadctrlAttrPullDown);
    EXPECT_EQ(dif_padctrl_write_attrs(&dif_padctrl_, pad_kind,
                                      attr_field.pad_num, conflicting_attrs),
              kDifPadctrlChangeAttrConflict);
  }

  dif_padctrl_t dif_padctrl_;
};

TEST_F(DifPadctrlTest, InitSuccess) { EXPECT_DEVICE_INIT_OK; }

TEST_F(DifPadctrlTest, InitFailureInvalidPadctrl) {
  mmio_region_t base_addr = dev().region();
  EXPECT_EQ(dif_padctrl_init(base_addr, nullptr), kDifPadctrlBadArg);
}

TEST_F(DifPadctrlTest, LockSuccess) {
  EXPECT_DEVICE_INIT_OK;
  EXPECT_WRITE32(PADCTRL_REGEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_padctrl_lock(&dif_padctrl_), kDifPadctrlOk);
}

TEST_F(DifPadctrlTest, LockFailureInvalidPadctrl) {
  EXPECT_EQ(dif_padctrl_lock(nullptr), kDifPadctrlBadArg);
}

TEST_F(DifPadctrlTest, ResetSuccess) {
  EXPECT_DEVICE_INIT_OK;
  EXPECT_LOCK_CHECK(false);

  dif_padctrl_attr_t reset_attrs =
      dif_padctrl_attr_t(kDifPadctrlAttrKeeper | kDifPadctrlAttrIOInvert);
  uint32_t replicated_attrs = reset_attrs |
                              (reset_attrs << PADCTRL_PARAM_ATTRDW) |
                              (reset_attrs << PADCTRL_PARAM_ATTRDW * 2) |
                              (reset_attrs << PADCTRL_PARAM_ATTRDW * 3);
  ExpectReset(replicated_attrs);
  EXPECT_EQ(dif_padctrl_reset(&dif_padctrl_, reset_attrs), kDifPadctrlResetOk);
}

TEST_F(DifPadctrlTest, ResetFailureBadPadctrl) {
  dif_padctrl_attr_t reset_attrs =
      dif_padctrl_attr_t(kDifPadctrlAttrKeeper | kDifPadctrlAttrIOInvert);
  EXPECT_EQ(dif_padctrl_reset(nullptr, reset_attrs), kDifPadctrlBadArg);
}

TEST_F(DifPadctrlTest, ResetFailureBadAttrs) {
  EXPECT_DEVICE_INIT_OK;

  dif_padctrl_attr_t reset_attrs = dif_padctrl_attr_t(-1);
  EXPECT_EQ(dif_padctrl_reset(&dif_padctrl_, reset_attrs), kDifPadctrlBadArg);
}

TEST_F(DifPadctrlTest, ResetFailedLocked) {
  EXPECT_DEVICE_INIT_OK;
  EXPECT_LOCK_CHECK(true);

  dif_padctrl_attr_t reset_attrs =
      dif_padctrl_attr_t(kDifPadctrlAttrKeeper | kDifPadctrlAttrIOInvert);
  EXPECT_EQ(dif_padctrl_reset(&dif_padctrl_, reset_attrs),
            kDifPadctrlResetLocked);
}

TEST_F(DifPadctrlTest, EnableAttrSuccess) {
  for (auto attr_field : mio_attr_fields_) {
    TestEnableAttrSuccess(attr_field, kDifPadctrlPadMio);
  }

  for (auto attr_field : dio_attr_fields_) {
    TestEnableAttrSuccess(attr_field, kDifPadctrlPadDio);
  }
}

TEST_F(DifPadctrlTest, DisableAttrSuccess) {
  for (auto attr_field : mio_attr_fields_) {
    TestDisableAttrSuccess(attr_field, kDifPadctrlPadMio);
  }

  for (auto attr_field : dio_attr_fields_) {
    TestDisableAttrSuccess(attr_field, kDifPadctrlPadDio);
  }
}

TEST_F(DifPadctrlTest, WriteAttrSuccess) {
  for (auto attr_field : mio_attr_fields_) {
    TestWriteAttrSuccess(attr_field, kDifPadctrlPadMio);
  }

  for (auto attr_field : dio_attr_fields_) {
    TestWriteAttrSuccess(attr_field, kDifPadctrlPadDio);
  }
}

TEST_F(DifPadctrlTest, EnableAttrFailureConflict) {
  for (auto attr_field : mio_attr_fields_) {
    TestEnableAttrFailureConflict(attr_field, kDifPadctrlPadMio);
  }

  for (auto attr_field : dio_attr_fields_) {
    TestEnableAttrFailureConflict(attr_field, kDifPadctrlPadDio);
  }
}

TEST_F(DifPadctrlTest, WriteAttrFailureConflict) {
  for (auto attr_field : mio_attr_fields_) {
    TestWriteAttrFailureConflict(attr_field, kDifPadctrlPadMio);
  }

  for (auto attr_field : dio_attr_fields_) {
    TestWriteAttrFailureConflict(attr_field, kDifPadctrlPadDio);
  }
}

TEST_F(DifPadctrlTest, EnableAttrFailureInvalidPad) {
  EXPECT_DEVICE_INIT_OK;

  EXPECT_EQ(
      dif_padctrl_enable_attrs(&dif_padctrl_, kDifPadctrlPadMio,
                               PADCTRL_PARAM_NMIOPADS, kDifPadctrlAttrPullUp),
      kDifPadctrlChangeAttrBadArg);
  EXPECT_EQ(
      dif_padctrl_enable_attrs(&dif_padctrl_, kDifPadctrlPadDio,
                               PADCTRL_PARAM_NDIOPADS, kDifPadctrlAttrPullUp),
      kDifPadctrlChangeAttrBadArg);
  EXPECT_EQ(dif_padctrl_enable_attrs(&dif_padctrl_, kDifPadctrlPadMio, -1,
                                     kDifPadctrlAttrPullUp),
            kDifPadctrlChangeAttrBadArg);
  EXPECT_EQ(dif_padctrl_enable_attrs(&dif_padctrl_, kDifPadctrlPadDio, -1,
                                     kDifPadctrlAttrPullUp),
            kDifPadctrlChangeAttrBadArg);
}

TEST_F(DifPadctrlTest, DisableAttrFailureInvalidPad) {
  EXPECT_DEVICE_INIT_OK;

  EXPECT_EQ(
      dif_padctrl_disable_attrs(&dif_padctrl_, kDifPadctrlPadMio,
                                PADCTRL_PARAM_NMIOPADS, kDifPadctrlAttrPullUp),
      kDifPadctrlChangeAttrBadArg);
  EXPECT_EQ(
      dif_padctrl_disable_attrs(&dif_padctrl_, kDifPadctrlPadDio,
                                PADCTRL_PARAM_NDIOPADS, kDifPadctrlAttrPullUp),
      kDifPadctrlChangeAttrBadArg);
  EXPECT_EQ(dif_padctrl_disable_attrs(&dif_padctrl_, kDifPadctrlPadMio, -1,
                                      kDifPadctrlAttrPullUp),
            kDifPadctrlChangeAttrBadArg);
  EXPECT_EQ(dif_padctrl_disable_attrs(&dif_padctrl_, kDifPadctrlPadDio, -1,
                                      kDifPadctrlAttrPullUp),
            kDifPadctrlChangeAttrBadArg);
}

TEST_F(DifPadctrlTest, WriteAttrFailureInvalidPad) {
  EXPECT_DEVICE_INIT_OK;

  EXPECT_EQ(
      dif_padctrl_write_attrs(&dif_padctrl_, kDifPadctrlPadMio,
                              PADCTRL_PARAM_NMIOPADS, kDifPadctrlAttrPullUp),
      kDifPadctrlChangeAttrBadArg);
  EXPECT_EQ(
      dif_padctrl_write_attrs(&dif_padctrl_, kDifPadctrlPadDio,
                              PADCTRL_PARAM_NDIOPADS, kDifPadctrlAttrPullUp),
      kDifPadctrlChangeAttrBadArg);
  EXPECT_EQ(dif_padctrl_write_attrs(&dif_padctrl_, kDifPadctrlPadMio, -1,
                                    kDifPadctrlAttrPullUp),
            kDifPadctrlChangeAttrBadArg);
  EXPECT_EQ(dif_padctrl_write_attrs(&dif_padctrl_, kDifPadctrlPadDio, -1,
                                    kDifPadctrlAttrPullUp),
            kDifPadctrlChangeAttrBadArg);
}

TEST_F(DifPadctrlTest, EnableAttrsFailureInvalidAttr) {
  EXPECT_DEVICE_INIT_OK;

  for (auto pad_kind : {kDifPadctrlPadMio, kDifPadctrlPadDio}) {
    dif_padctrl_attr_t bad_attrs_1 = dif_padctrl_attr_t(
        (1 << PADCTRL_PARAM_ATTRDW) | kDifPadctrlAttrOpenDrain);
    EXPECT_EQ(dif_padctrl_enable_attrs(&dif_padctrl_, pad_kind, 0, bad_attrs_1),
              kDifPadctrlChangeAttrBadArg);

    dif_padctrl_attr_t bad_attrs_2 = dif_padctrl_attr_t(-1);
    EXPECT_EQ(dif_padctrl_enable_attrs(&dif_padctrl_, pad_kind, 0, bad_attrs_2),
              kDifPadctrlChangeAttrBadArg);
  }
}

TEST_F(DifPadctrlTest, DisableAttrsFailureInvalidAttr) {
  EXPECT_DEVICE_INIT_OK;

  for (auto pad_kind : {kDifPadctrlPadMio, kDifPadctrlPadDio}) {
    dif_padctrl_attr_t bad_attrs_1 = dif_padctrl_attr_t(
        (1 << PADCTRL_PARAM_ATTRDW) | kDifPadctrlAttrOpenDrain);
    EXPECT_EQ(
        dif_padctrl_disable_attrs(&dif_padctrl_, pad_kind, 0, bad_attrs_1),
        kDifPadctrlChangeAttrBadArg);

    dif_padctrl_attr_t bad_attrs_2 = dif_padctrl_attr_t(-1);
    EXPECT_EQ(
        dif_padctrl_disable_attrs(&dif_padctrl_, pad_kind, 0, bad_attrs_2),
        kDifPadctrlChangeAttrBadArg);
  }
}

TEST_F(DifPadctrlTest, WriteAttrsFailureInvalidAttr) {
  EXPECT_DEVICE_INIT_OK;

  for (auto pad_kind : {kDifPadctrlPadMio, kDifPadctrlPadDio}) {
    dif_padctrl_attr_t bad_attrs_1 = dif_padctrl_attr_t(
        (1 << PADCTRL_PARAM_ATTRDW) | kDifPadctrlAttrOpenDrain);
    EXPECT_EQ(dif_padctrl_write_attrs(&dif_padctrl_, pad_kind, 0, bad_attrs_1),
              kDifPadctrlChangeAttrBadArg);

    dif_padctrl_attr_t bad_attrs_2 = dif_padctrl_attr_t(-1);
    EXPECT_EQ(dif_padctrl_write_attrs(&dif_padctrl_, pad_kind, 0, bad_attrs_2),
              kDifPadctrlChangeAttrBadArg);
  }
}

TEST_F(DifPadctrlTest, EnableAttrsFailureLocked) {
  EXPECT_DEVICE_INIT_OK;
  EXPECT_LOCK_CHECK(true);

  EXPECT_EQ(dif_padctrl_enable_attrs(&dif_padctrl_, kDifPadctrlPadMio, 0,
                                     kDifPadctrlAttrPullUp),
            kDifPadctrlChangeAttrLocked);
}

TEST_F(DifPadctrlTest, DisableAttrsFailureLocked) {
  EXPECT_DEVICE_INIT_OK;
  EXPECT_LOCK_CHECK(true);

  EXPECT_EQ(dif_padctrl_disable_attrs(&dif_padctrl_, kDifPadctrlPadMio, 0,
                                      kDifPadctrlAttrPullUp),
            kDifPadctrlChangeAttrLocked);
}

TEST_F(DifPadctrlTest, WriteAttrsFailureLocked) {
  EXPECT_DEVICE_INIT_OK;
  EXPECT_LOCK_CHECK(true);

  EXPECT_EQ(dif_padctrl_write_attrs(&dif_padctrl_, kDifPadctrlPadMio, 0,
                                    kDifPadctrlAttrPullUp),
            kDifPadctrlChangeAttrLocked);
}

TEST_F(DifPadctrlTest, EnableAttrsFailureInvalidPadctrl) {
  EXPECT_DEVICE_INIT_OK;

  EXPECT_EQ(dif_padctrl_enable_attrs(nullptr, kDifPadctrlPadMio, 0,
                                     kDifPadctrlAttrPullUp),
            kDifPadctrlBadArg);
}

TEST_F(DifPadctrlTest, DisableAttrsFailureInvalidPadctrl) {
  EXPECT_DEVICE_INIT_OK;

  EXPECT_EQ(dif_padctrl_disable_attrs(nullptr, kDifPadctrlPadMio, 0,
                                      kDifPadctrlAttrPullUp),
            kDifPadctrlBadArg);
}

TEST_F(DifPadctrlTest, WriteAttrsFailureInvalidPadctrl) {
  EXPECT_DEVICE_INIT_OK;

  EXPECT_EQ(dif_padctrl_write_attrs(nullptr, kDifPadctrlPadMio, 0,
                                    kDifPadctrlAttrPullUp),
            kDifPadctrlBadArg);
}

TEST_F(DifPadctrlTest, GetAttrsSuccess) {
  EXPECT_DEVICE_INIT_OK;

  for (auto attr_field : mio_attr_fields_) {
    dif_padctrl_attr_t expected_attrs =
        dif_padctrl_attr_t(kDifPadctrlAttrPullDown | kDifPadctrlAttrIOInvert);
    ExpectAttrFieldRead(attr_field, expected_attrs);

    dif_padctrl_attr_t seen_attrs;
    EXPECT_EQ(dif_padctrl_get_attrs(&dif_padctrl_, kDifPadctrlPadMio,
                                    attr_field.pad_num, &seen_attrs),
              kDifPadctrlOk);
    EXPECT_EQ(expected_attrs, seen_attrs);
  }

  for (auto attr_field : dio_attr_fields_) {
    dif_padctrl_attr_t expected_attrs =
        dif_padctrl_attr_t(kDifPadctrlAttrWeakDrive | kDifPadctrlAttrKeeper |
                           kDifPadctrlAttrIOInvert);
    ExpectAttrFieldRead(attr_field, expected_attrs);

    dif_padctrl_attr_t seen_attrs;
    EXPECT_EQ(dif_padctrl_get_attrs(&dif_padctrl_, kDifPadctrlPadDio,
                                    attr_field.pad_num, &seen_attrs),
              kDifPadctrlOk);
    EXPECT_EQ(expected_attrs, seen_attrs);
  }
}

TEST_F(DifPadctrlTest, GetAttrsFailureBadArg) {
  EXPECT_DEVICE_INIT_OK;

  dif_padctrl_attr_t seen_attrs;
  EXPECT_EQ(dif_padctrl_get_attrs(nullptr, kDifPadctrlPadMio, 0, &seen_attrs),
            kDifPadctrlBadArg);
  EXPECT_EQ(dif_padctrl_get_attrs(&dif_padctrl_, kDifPadctrlPadMio, 0, nullptr),
            kDifPadctrlBadArg);
}

}  // namespace
}  // namespace dif_padctrl_test
