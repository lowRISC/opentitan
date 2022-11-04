// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_rstmgr.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "rstmgr_regs.h"  // Generated.

namespace dif_rstmgr_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Each;
using testing::ElementsAreArray;
using testing::Eq;
using testing::IsSubsetOf;
using testing::Test;

class RstmgrTest : public Test, public MmioTest {
 protected:
  dif_rstmgr_t rstmgr_ = {.base_addr = dev().region()};
};

class ResetTest : public RstmgrTest {};

TEST_F(ResetTest, NullArgs) { EXPECT_DIF_BADARG(dif_rstmgr_reset(nullptr)); }

TEST_F(ResetTest, Success) {
  EXPECT_WRITE32(RSTMGR_RESET_INFO_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  for (uint32_t i = 0; i < RSTMGR_PARAM_NUM_SW_RESETS; i++) {
    EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_0_REG_OFFSET + 4 * i,
                   std::numeric_limits<uint32_t>::max());
  }

  EXPECT_DIF_OK(dif_rstmgr_reset(&rstmgr_));
}

class ResetLockTest : public RstmgrTest {};

TEST_F(ResetLockTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rstmgr_reset_lock(nullptr, 0));
}

TEST_F(ResetLockTest, BadPeripheral) {
  EXPECT_DIF_BADARG(
      dif_rstmgr_reset_lock(&rstmgr_, RSTMGR_PARAM_NUM_SW_RESETS));
}

TEST_F(ResetLockTest, Success) {
  for (uint32_t reg_index = 0; reg_index < RSTMGR_PARAM_NUM_SW_RESETS;
       ++reg_index) {
    // When reg is set to `0`, it means that the software reset for the
    // peripheral is locked.
    EXPECT_WRITE32(RSTMGR_SW_RST_REGWEN_0_REG_OFFSET + reg_index * 4, 0);

    EXPECT_DIF_OK(dif_rstmgr_reset_lock(&rstmgr_, reg_index));
  }
}

class ResetIsLockedTest : public RstmgrTest {};

TEST_F(ResetIsLockedTest, NullArgs) {
  bool is_locked;
  EXPECT_DIF_BADARG(dif_rstmgr_reset_is_locked(nullptr, 0, nullptr));
  EXPECT_DIF_BADARG(dif_rstmgr_reset_is_locked(nullptr, 0, &is_locked));
  EXPECT_DIF_BADARG(dif_rstmgr_reset_is_locked(&rstmgr_, 0, nullptr));
}

TEST_F(ResetIsLockedTest, BadPeripheral) {
  bool is_locked;
  EXPECT_DIF_BADARG(dif_rstmgr_reset_is_locked(
      &rstmgr_, RSTMGR_PARAM_NUM_SW_RESETS, &is_locked));
}

TEST_F(ResetIsLockedTest, Success) {
  for (uint32_t reg_index = 0; reg_index < RSTMGR_PARAM_NUM_SW_RESETS;
       ++reg_index) {
    // When bit is set to `0`, it means that the software reset for the
    // peripheral is locked.
    EXPECT_READ32(RSTMGR_SW_RST_REGWEN_0_REG_OFFSET + reg_index * 4, 0);

    bool is_locked = false;
    EXPECT_DIF_OK(dif_rstmgr_reset_is_locked(&rstmgr_, reg_index, &is_locked));
    EXPECT_TRUE(is_locked);

    is_locked = true;
    EXPECT_READ32(RSTMGR_SW_RST_REGWEN_0_REG_OFFSET + reg_index * 4, 1);
    EXPECT_DIF_OK(dif_rstmgr_reset_is_locked(&rstmgr_, reg_index, &is_locked));
    EXPECT_FALSE(is_locked);
  }
}

class ResetCausesGetTest : public RstmgrTest {
 protected:
  // Make sure that the test is up-to-date with the implementation.
  ResetCausesGetTest() {
    // Make sure that the last reset reason in the test matches the last reset
    // reason in the DIF at the time of writing this test.
    bitfield_field32_t last = reset_info_reasons_.back();
    uint32_t bitfield = bitfield_field32_write(0, last, last.mask);
    EXPECT_EQ(bitfield, kDifRstmgrResetInfoHwReq);

    // Number of reset reasons between test and the peripheral match at the
    // time of writing this test.
    EXPECT_EQ(reset_info_reasons_.size(), 3);
  }

  const std::vector<bitfield_field32_t> reset_info_reasons_{
      bitfield_bit32_to_field32(RSTMGR_RESET_INFO_POR_BIT),
      bitfield_bit32_to_field32(RSTMGR_RESET_INFO_LOW_POWER_EXIT_BIT),
      RSTMGR_RESET_INFO_HW_REQ_FIELD,
  };
};

TEST_F(ResetCausesGetTest, NullArgs) {
  dif_rstmgr_reset_info_bitfield_t info;
  EXPECT_DIF_BADARG(dif_rstmgr_reset_info_get(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_rstmgr_reset_info_get(nullptr, &info));
  EXPECT_DIF_BADARG(dif_rstmgr_reset_info_get(&rstmgr_, nullptr));
}

TEST_F(ResetCausesGetTest, Success) {
  // Single reason expectations.
  for (auto reason : reset_info_reasons_) {
    uint32_t bitfield = bitfield_field32_write(0, reason, reason.mask);
    EXPECT_READ32(RSTMGR_RESET_INFO_REG_OFFSET, bitfield);

    dif_rstmgr_reset_info_bitfield_t info;
    EXPECT_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr_, &info));
    EXPECT_EQ(info & bitfield, info);
  }

  // The first and the last reset causes.
  bitfield_field32_t first = reset_info_reasons_.front();
  bitfield_field32_t last = reset_info_reasons_.back();
  EXPECT_READ32(RSTMGR_RESET_INFO_REG_OFFSET, {
                                                  {first.index, first.mask},
                                                  {last.index, last.mask},
                                              });

  dif_rstmgr_reset_info_bitfield_t info;
  EXPECT_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr_, &info));

  // Make sure that `kDifRstmgrResetInfoPor` and `kDifRstmgrResetInfoHwReq`
  // reset causes are set.
  EXPECT_EQ(info & (kDifRstmgrResetInfoPor | kDifRstmgrResetInfoHwReq), info);
}

class ResetCausesClearTest : public RstmgrTest {};

TEST_F(ResetCausesClearTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rstmgr_reset_info_clear(nullptr));
}

TEST_F(ResetCausesClearTest, Success) {
  EXPECT_WRITE32(RSTMGR_RESET_INFO_REG_OFFSET,
                 std::numeric_limits<uint32_t>::max());

  EXPECT_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr_));
}

class AlertInfoSetTest : public RstmgrTest {};

TEST_F(AlertInfoSetTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_rstmgr_alert_info_set_enabled(nullptr, kDifToggleEnabled));
}

TEST_F(AlertInfoSetTest, Success) {
  // Expect a read of regwen.
  uint32_t alert_regwen =
      bitfield_bit32_write(std::numeric_limits<uint32_t>::max(), 0, true);
  EXPECT_READ32(RSTMGR_ALERT_REGWEN_REG_OFFSET, alert_regwen);

  // Enable.
  EXPECT_WRITE32(RSTMGR_ALERT_INFO_CTRL_REG_OFFSET,
                 {
                     {RSTMGR_ALERT_INFO_CTRL_EN_BIT, true},
                 });
  EXPECT_DIF_OK(dif_rstmgr_alert_info_set_enabled(&rstmgr_, kDifToggleEnabled));

  // Disable.
  EXPECT_READ32(RSTMGR_ALERT_REGWEN_REG_OFFSET, alert_regwen);
  EXPECT_WRITE32(RSTMGR_ALERT_INFO_CTRL_REG_OFFSET,
                 {
                     {RSTMGR_ALERT_INFO_CTRL_EN_BIT, false},
                 });
  EXPECT_DIF_OK(
      dif_rstmgr_alert_info_set_enabled(&rstmgr_, kDifToggleDisabled));
}

class AlertInfoGetTest : public RstmgrTest {};

TEST_F(AlertInfoGetTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_get_enabled(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_get_enabled(&rstmgr_, nullptr));
  dif_toggle_t state;
  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_get_enabled(nullptr, &state));
}

TEST_F(AlertInfoGetTest, Success) {
  // Enabled.
  EXPECT_READ32(RSTMGR_ALERT_INFO_CTRL_REG_OFFSET,
                {
                    {RSTMGR_ALERT_INFO_CTRL_EN_BIT, true},
                });

  dif_toggle_t state = kDifToggleDisabled;
  EXPECT_DIF_OK(dif_rstmgr_alert_info_get_enabled(&rstmgr_, &state));
  EXPECT_EQ(state, kDifToggleEnabled);

  // Disabled.
  //
  // Make sure that the only relevant `enabled` bit is read - set all bits
  // high apart from the `enabled` bit.
  uint32_t register_value =
      bitfield_bit32_write(std::numeric_limits<uint32_t>::max(),
                           RSTMGR_ALERT_INFO_CTRL_EN_BIT, false);
  EXPECT_READ32(RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, register_value);

  state = kDifToggleEnabled;
  EXPECT_DIF_OK(dif_rstmgr_alert_info_get_enabled(&rstmgr_, &state));
  EXPECT_EQ(state, kDifToggleDisabled);
}

class AlertInfoGetSizeTest : public RstmgrTest {};

TEST_F(AlertInfoGetSizeTest, Success) {
  EXPECT_READ32(RSTMGR_ALERT_INFO_ATTR_REG_OFFSET, 5);

  size_t size = 0;
  EXPECT_DIF_OK(dif_rstmgr_alert_info_get_size(&rstmgr_, &size));
  EXPECT_EQ(size, 5);
}

TEST_F(AlertInfoGetSizeTest, BadArgs) {
  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_get_size(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_get_size(&rstmgr_, nullptr));
  size_t size;
  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_get_size(nullptr, &size));
}

class AlertInfoDumpReadTest : public RstmgrTest {
 protected:
  AlertInfoDumpReadTest() {
    for (uint32_t i = 0; i < DIF_RSTMGR_ALERT_INFO_MAX_SIZE; ++i) {
      src_[i] = dev().GarbageMemory<uint32_t>();
    }
  }

  dif_rstmgr_alert_info_dump_segment_t src_[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
};

TEST_F(AlertInfoDumpReadTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_dump_read(
      nullptr, nullptr, DIF_RSTMGR_ALERT_INFO_MAX_SIZE, nullptr));

  size_t segments_read;
  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_dump_read(
      nullptr, nullptr, DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &segments_read));

  dif_rstmgr_alert_info_dump_segment_t dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_dump_read(
      nullptr, &dump[0], DIF_RSTMGR_ALERT_INFO_MAX_SIZE, nullptr));

  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_dump_read(
      nullptr, &dump[0], DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &segments_read));

  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_dump_read(
      &rstmgr_, nullptr, DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &segments_read));

  EXPECT_DIF_BADARG(dif_rstmgr_alert_info_dump_read(
      &rstmgr_, &dump[0], DIF_RSTMGR_ALERT_INFO_MAX_SIZE, nullptr));
}

TEST_F(AlertInfoDumpReadTest, BadDumpSize) {
  EXPECT_READ32(RSTMGR_ALERT_INFO_ATTR_REG_OFFSET,
                DIF_RSTMGR_ALERT_INFO_MAX_SIZE);

  size_t segments_read = 0xA5A5A5A5;
  dif_rstmgr_alert_info_dump_segment_t dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
  EXPECT_EQ(dif_rstmgr_alert_info_dump_read(&rstmgr_, &dump[0],
                                            DIF_RSTMGR_ALERT_INFO_MAX_SIZE - 1,
                                            &segments_read),
            kDifError);
  EXPECT_EQ(segments_read, 0xA5A5A5A5);
}

TEST_F(AlertInfoDumpReadTest, SuccessFullBuffer) {
  EXPECT_READ32(RSTMGR_ALERT_INFO_ATTR_REG_OFFSET,
                DIF_RSTMGR_ALERT_INFO_MAX_SIZE);
  EXPECT_READ32(RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 1);

  for (uint32_t i = 0; i < DIF_RSTMGR_ALERT_INFO_MAX_SIZE; ++i) {
    EXPECT_WRITE32(RSTMGR_ALERT_INFO_CTRL_REG_OFFSET,
                   {
                       {
                           RSTMGR_ALERT_INFO_CTRL_EN_BIT,
                           true,
                       },
                       {
                           RSTMGR_ALERT_INFO_CTRL_INDEX_OFFSET,
                           i,
                       },
                   });

    EXPECT_READ32(RSTMGR_ALERT_INFO_REG_OFFSET, src_[i]);
  }

  size_t segments_read = 0;
  dif_rstmgr_alert_info_dump_segment_t dump[DIF_RSTMGR_ALERT_INFO_MAX_SIZE];
  EXPECT_DIF_OK(dif_rstmgr_alert_info_dump_read(
      &rstmgr_, &dump[0], DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &segments_read));
  EXPECT_EQ(segments_read, DIF_RSTMGR_ALERT_INFO_MAX_SIZE);
  EXPECT_THAT(src_, ElementsAreArray(dump));
}

TEST_F(AlertInfoDumpReadTest, SuccessDumpSmaller) {
  constexpr uint32_t dump_size = DIF_RSTMGR_ALERT_INFO_MAX_SIZE - 1;

  EXPECT_READ32(RSTMGR_ALERT_INFO_ATTR_REG_OFFSET, dump_size);
  EXPECT_READ32(RSTMGR_ALERT_INFO_CTRL_REG_OFFSET, 1);

  for (uint32_t i = 0; i < dump_size; ++i) {
    EXPECT_WRITE32(RSTMGR_ALERT_INFO_CTRL_REG_OFFSET,
                   {
                       {
                           RSTMGR_ALERT_INFO_CTRL_EN_BIT,
                           true,
                       },
                       {
                           RSTMGR_ALERT_INFO_CTRL_INDEX_OFFSET,
                           i,
                       },
                   });

    EXPECT_READ32(RSTMGR_ALERT_INFO_REG_OFFSET, src_[i]);
  }

  size_t segments_read = 0;
  dif_rstmgr_alert_info_dump_segment_t dump[dump_size];
  EXPECT_DIF_OK(dif_rstmgr_alert_info_dump_read(
      &rstmgr_, &dump[0], DIF_RSTMGR_ALERT_INFO_MAX_SIZE, &segments_read));
  EXPECT_EQ(segments_read, dump_size);
  EXPECT_THAT(dump, IsSubsetOf(src_));
}

class CpuInfoSetTest : public RstmgrTest {};

TEST_F(CpuInfoSetTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_rstmgr_cpu_info_set_enabled(nullptr, kDifToggleEnabled));
}

TEST_F(CpuInfoSetTest, Success) {
  // Expect a read of regwen.
  uint32_t cpu_regwen =
      bitfield_bit32_write(std::numeric_limits<uint32_t>::max(), 0, true);
  EXPECT_READ32(RSTMGR_CPU_REGWEN_REG_OFFSET, cpu_regwen);

  // Enable.
  EXPECT_WRITE32(RSTMGR_CPU_INFO_CTRL_REG_OFFSET,
                 {
                     {RSTMGR_CPU_INFO_CTRL_EN_BIT, true},
                 });
  EXPECT_DIF_OK(dif_rstmgr_cpu_info_set_enabled(&rstmgr_, kDifToggleEnabled));

  // Disable.
  EXPECT_READ32(RSTMGR_CPU_REGWEN_REG_OFFSET, cpu_regwen);
  EXPECT_WRITE32(RSTMGR_CPU_INFO_CTRL_REG_OFFSET,
                 {
                     {RSTMGR_CPU_INFO_CTRL_EN_BIT, false},
                 });
  EXPECT_DIF_OK(dif_rstmgr_cpu_info_set_enabled(&rstmgr_, kDifToggleDisabled));
}

class CpuInfoGetTest : public RstmgrTest {};

TEST_F(CpuInfoGetTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_get_enabled(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_get_enabled(&rstmgr_, nullptr));
  dif_toggle_t state;
  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_get_enabled(nullptr, &state));
}

TEST_F(CpuInfoGetTest, Success) {
  // Enabled.
  EXPECT_READ32(RSTMGR_CPU_INFO_CTRL_REG_OFFSET,
                {
                    {RSTMGR_CPU_INFO_CTRL_EN_BIT, true},
                });

  dif_toggle_t state = kDifToggleDisabled;
  EXPECT_DIF_OK(dif_rstmgr_cpu_info_get_enabled(&rstmgr_, &state));
  EXPECT_EQ(state, kDifToggleEnabled);

  // Disabled.
  //
  // Make sure that the only relevant `enabled` bit is read - set all bits
  // high apart from the `enabled` bit.
  uint32_t register_value = bitfield_bit32_write(
      std::numeric_limits<uint32_t>::max(), RSTMGR_CPU_INFO_CTRL_EN_BIT, false);
  EXPECT_READ32(RSTMGR_CPU_INFO_CTRL_REG_OFFSET, register_value);

  state = kDifToggleEnabled;
  EXPECT_DIF_OK(dif_rstmgr_cpu_info_get_enabled(&rstmgr_, &state));
  EXPECT_EQ(state, kDifToggleDisabled);
}

class CpuInfoGetSizeTest : public RstmgrTest {};

TEST_F(CpuInfoGetSizeTest, Success) {
  EXPECT_READ32(RSTMGR_CPU_INFO_ATTR_REG_OFFSET, 5);

  size_t size = 0;
  EXPECT_DIF_OK(dif_rstmgr_cpu_info_get_size(&rstmgr_, &size));
  EXPECT_EQ(size, 5);
}

TEST_F(CpuInfoGetSizeTest, BadArgs) {
  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_get_size(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_get_size(&rstmgr_, nullptr));
  size_t size;
  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_get_size(nullptr, &size));
}

class CpuInfoDumpReadTest : public RstmgrTest {
 protected:
  CpuInfoDumpReadTest() {
    for (uint32_t i = 0; i < DIF_RSTMGR_CPU_INFO_MAX_SIZE; ++i) {
      src_[i] = dev().GarbageMemory<uint32_t>();
    }
  }

  dif_rstmgr_cpu_info_dump_segment_t src_[DIF_RSTMGR_CPU_INFO_MAX_SIZE];
};

TEST_F(CpuInfoDumpReadTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_dump_read(
      nullptr, nullptr, DIF_RSTMGR_CPU_INFO_MAX_SIZE, nullptr));

  size_t segments_read;
  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_dump_read(
      nullptr, nullptr, DIF_RSTMGR_CPU_INFO_MAX_SIZE, &segments_read));

  dif_rstmgr_cpu_info_dump_segment_t dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];
  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_dump_read(
      nullptr, &dump[0], DIF_RSTMGR_CPU_INFO_MAX_SIZE, nullptr));

  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_dump_read(
      nullptr, &dump[0], DIF_RSTMGR_CPU_INFO_MAX_SIZE, &segments_read));

  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_dump_read(
      &rstmgr_, nullptr, DIF_RSTMGR_CPU_INFO_MAX_SIZE, &segments_read));

  EXPECT_DIF_BADARG(dif_rstmgr_cpu_info_dump_read(
      &rstmgr_, &dump[0], DIF_RSTMGR_CPU_INFO_MAX_SIZE, nullptr));
}

TEST_F(CpuInfoDumpReadTest, BadDumpSize) {
  EXPECT_READ32(RSTMGR_CPU_INFO_ATTR_REG_OFFSET, DIF_RSTMGR_CPU_INFO_MAX_SIZE);

  size_t segments_read = 0xA5A5A5A5;
  dif_rstmgr_cpu_info_dump_segment_t dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];
  EXPECT_EQ(
      dif_rstmgr_cpu_info_dump_read(
          &rstmgr_, &dump[0], DIF_RSTMGR_CPU_INFO_MAX_SIZE - 1, &segments_read),
      kDifError);
  EXPECT_EQ(segments_read, 0xA5A5A5A5);
}

TEST_F(CpuInfoDumpReadTest, SuccessFullBuffer) {
  EXPECT_READ32(RSTMGR_CPU_INFO_ATTR_REG_OFFSET, DIF_RSTMGR_CPU_INFO_MAX_SIZE);
  EXPECT_READ32(RSTMGR_CPU_INFO_CTRL_REG_OFFSET, 1);

  for (uint32_t i = 0; i < DIF_RSTMGR_CPU_INFO_MAX_SIZE; ++i) {
    EXPECT_WRITE32(RSTMGR_CPU_INFO_CTRL_REG_OFFSET,
                   {
                       {
                           RSTMGR_CPU_INFO_CTRL_EN_BIT,
                           true,
                       },
                       {
                           RSTMGR_CPU_INFO_CTRL_INDEX_OFFSET,
                           i,
                       },
                   });

    EXPECT_READ32(RSTMGR_CPU_INFO_REG_OFFSET, src_[i]);
  }

  size_t segments_read = 0;
  dif_rstmgr_cpu_info_dump_segment_t dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];
  EXPECT_DIF_OK(dif_rstmgr_cpu_info_dump_read(
      &rstmgr_, &dump[0], DIF_RSTMGR_CPU_INFO_MAX_SIZE, &segments_read));
  EXPECT_EQ(segments_read, DIF_RSTMGR_CPU_INFO_MAX_SIZE);
  EXPECT_THAT(src_, ElementsAreArray(dump));
}

TEST_F(CpuInfoDumpReadTest, SuccessDumpSmaller) {
  constexpr uint32_t dump_size = DIF_RSTMGR_CPU_INFO_MAX_SIZE - 1;

  EXPECT_READ32(RSTMGR_CPU_INFO_ATTR_REG_OFFSET, dump_size);
  EXPECT_READ32(RSTMGR_CPU_INFO_CTRL_REG_OFFSET, 1);

  for (uint32_t i = 0; i < dump_size; ++i) {
    EXPECT_WRITE32(RSTMGR_CPU_INFO_CTRL_REG_OFFSET,
                   {
                       {
                           RSTMGR_CPU_INFO_CTRL_EN_BIT,
                           true,
                       },
                       {
                           RSTMGR_CPU_INFO_CTRL_INDEX_OFFSET,
                           i,
                       },
                   });

    EXPECT_READ32(RSTMGR_CPU_INFO_REG_OFFSET, src_[i]);
  }

  size_t segments_read = 0;
  dif_rstmgr_cpu_info_dump_segment_t dump[dump_size];
  EXPECT_DIF_OK(dif_rstmgr_cpu_info_dump_read(
      &rstmgr_, &dump[0], DIF_RSTMGR_CPU_INFO_MAX_SIZE, &segments_read));
  EXPECT_EQ(segments_read, dump_size);
  EXPECT_THAT(dump, IsSubsetOf(src_));
}

class SoftwareResetTest : public RstmgrTest {};

TEST_F(SoftwareResetTest, NullArgs) {
  EXPECT_DIF_BADARG(
      dif_rstmgr_software_reset(nullptr, 0, kDifRstmgrSoftwareReset));
}

TEST_F(SoftwareResetTest, BadPeripheral) {
  EXPECT_DIF_BADARG(dif_rstmgr_software_reset(
      &rstmgr_, RSTMGR_PARAM_NUM_SW_RESETS, kDifRstmgrSoftwareReset));
}

TEST_F(SoftwareResetTest, SoftwareResetIsLocked) {
  for (uint32_t reg_index = 0; reg_index < RSTMGR_PARAM_NUM_SW_RESETS;
       ++reg_index) {
    // When  set to `0`, it means that the software reset for the
    // peripheral is locked.
    EXPECT_READ32(RSTMGR_SW_RST_REGWEN_0_REG_OFFSET + reg_index * 4, 0);

    EXPECT_EQ(dif_rstmgr_software_reset(&rstmgr_, reg_index,
                                        kDifRstmgrSoftwareResetHold),
              kDifLocked);
  }
}

TEST_F(SoftwareResetTest, SuccessHold) {
  for (uint32_t reg_index = 0; reg_index < RSTMGR_PARAM_NUM_SW_RESETS;
       ++reg_index) {
    // Software reset is not locked for any of the supported peripherals.
    EXPECT_READ32(RSTMGR_SW_RST_REGWEN_0_REG_OFFSET + reg_index * 4, 1);

    // When reg is set to `0`, it means that the peripheral is held in reset.
    EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_0_REG_OFFSET + reg_index * 4, 0);

    EXPECT_DIF_OK(dif_rstmgr_software_reset(&rstmgr_, reg_index,
                                            kDifRstmgrSoftwareResetHold));
  }
}

TEST_F(SoftwareResetTest, SuccessRelease) {
  for (uint32_t reg_index = 0; reg_index < RSTMGR_PARAM_NUM_SW_RESETS;
       ++reg_index) {
    // Software reset is not locked for any of the supported peripherals.
    EXPECT_READ32(RSTMGR_SW_RST_REGWEN_0_REG_OFFSET + reg_index * 4, 1);

    // Check that reset can be de-asserted for every supported peripheral.
    EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_0_REG_OFFSET + reg_index * 4, 1);

    EXPECT_DIF_OK(dif_rstmgr_software_reset(&rstmgr_, reg_index,
                                            kDifRstmgrSoftwareResetRelease));
  }
}

TEST_F(SoftwareResetTest, SuccessReset) {
  for (uint32_t reg_index = 0; reg_index < RSTMGR_PARAM_NUM_SW_RESETS;
       ++reg_index) {
    // Software reset is not locked for any of the supported peripherals.
    EXPECT_READ32(RSTMGR_SW_RST_REGWEN_0_REG_OFFSET + reg_index * 4, 1);

    // When bit is set to `0`, it means that the peripheral is held in reset.
    EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_0_REG_OFFSET + reg_index * 4, 0);

    // Check that reset can be de-asserted for every supported peripheral.
    EXPECT_WRITE32(RSTMGR_SW_RST_CTRL_N_0_REG_OFFSET + reg_index * 4, 1);

    EXPECT_DIF_OK(dif_rstmgr_software_reset(&rstmgr_, reg_index,
                                            kDifRstmgrSoftwareReset));
  }
}

class SoftwareResetIsHeldTest : public RstmgrTest {};

TEST_F(SoftwareResetIsHeldTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_rstmgr_software_reset_is_held(nullptr, 0, nullptr));

  bool asserted;
  EXPECT_DIF_BADARG(dif_rstmgr_software_reset_is_held(nullptr, 0, &asserted));

  EXPECT_DIF_BADARG(dif_rstmgr_software_reset_is_held(&rstmgr_, 0, nullptr));
}

TEST_F(SoftwareResetIsHeldTest, BadPeripheral) {
  bool asserted;
  EXPECT_DIF_BADARG(dif_rstmgr_software_reset_is_held(
      &rstmgr_, RSTMGR_PARAM_NUM_SW_RESETS, &asserted));
}

TEST_F(SoftwareResetIsHeldTest, Success) {
  for (uint32_t reg_index = 0; reg_index < RSTMGR_PARAM_NUM_SW_RESETS;
       ++reg_index) {
    // Check in turn that every peripheral is held in software reset.
    EXPECT_READ32(RSTMGR_SW_RST_CTRL_N_0_REG_OFFSET + reg_index * 4, 0);

    bool asserted = false;
    EXPECT_DIF_OK(
        dif_rstmgr_software_reset_is_held(&rstmgr_, reg_index, &asserted));
    EXPECT_TRUE(asserted);

    // Check in turn that every peripheral is not held in software reset.
    EXPECT_READ32(RSTMGR_SW_RST_CTRL_N_0_REG_OFFSET + reg_index * 4, 1);

    asserted = true;
    EXPECT_DIF_OK(
        dif_rstmgr_software_reset_is_held(&rstmgr_, reg_index, &asserted));
    EXPECT_FALSE(asserted);
  }
}
class FatalErrorTest : public RstmgrTest {};

TEST_F(FatalErrorTest, GetBadArgs) {
  dif_rstmgr_fatal_err_codes_t codes;
  EXPECT_DIF_BADARG(dif_rstmgr_fatal_err_code_get_codes(nullptr, nullptr));
  EXPECT_DIF_BADARG(dif_rstmgr_fatal_err_code_get_codes(nullptr, &codes));
  EXPECT_DIF_BADARG(dif_rstmgr_fatal_err_code_get_codes(&rstmgr_, nullptr));
}

TEST_F(FatalErrorTest, GetCodes) {
  dif_rstmgr_fatal_err_codes_t codes;
  EXPECT_READ32(RSTMGR_ERR_CODE_REG_OFFSET, 6);
  EXPECT_DIF_OK(dif_rstmgr_fatal_err_code_get_codes(&rstmgr_, &codes));
  EXPECT_EQ(codes, 6);
}

}  // namespace
}  // namespace dif_rstmgr_unittest
