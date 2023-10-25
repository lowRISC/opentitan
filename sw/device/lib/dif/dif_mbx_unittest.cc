// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_mbx.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

extern "C" {
#include "mbx_regs.h"  // Generated.
}  // extern "C"

namespace dif_mbx_test {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

// Base class for the rest fixtures in this file.
class MbxTest : public testing::Test, public mock_mmio::MmioTest {};

// Base class for the rest of the tests in this file, provides a
// `dif_mbx_t` instance.
class MbxTestInitialized : public MbxTest {
 protected:
  dif_mbx_t mbx_;

  MbxTestInitialized() { EXPECT_DIF_OK(dif_mbx_init(dev().region(), &mbx_)); }
};

class MemoryRangeSuccessTests
    : public MbxTestInitialized,
      public testing::WithParamInterface<dif_mbx_range_config_t> {};

TEST_P(MemoryRangeSuccessTests, SetSuccess) {
  dif_mbx_range_config_t range = GetParam();

  EXPECT_WRITE32(MBX_INBOUND_BASE_ADDRESS_REG_OFFSET, range.imbx_base_addr);
  EXPECT_WRITE32(MBX_INBOUND_LIMIT_ADDRESS_REG_OFFSET, range.imbx_limit_addr);
  EXPECT_WRITE32(MBX_OUTBOUND_BASE_ADDRESS_REG_OFFSET, range.ombx_base_addr);
  EXPECT_WRITE32(MBX_OUTBOUND_LIMIT_ADDRESS_REG_OFFSET, range.ombx_limit_addr);
  EXPECT_WRITE32(MBX_ADDRESS_RANGE_VALID_REG_OFFSET, 1);

  EXPECT_DIF_OK(dif_mbx_range_set(&mbx_, range));
}

INSTANTIATE_TEST_SUITE_P(MemoryRangeSuccessTests, MemoryRangeSuccessTests,
                         testing::ValuesIn(std::vector<dif_mbx_range_config_t>{{
                             {.imbx_base_addr = 0xD0CF2C50,
                              .imbx_limit_addr = 0xD1CF2C0F,
                              .ombx_base_addr = 0xD1CF3C0F,
                              .ombx_limit_addr = 0xD1CF3C10},
                             {.imbx_base_addr = 0x1000,
                              .imbx_limit_addr = 0x2000,
                              .ombx_base_addr = 0x3000,
                              .ombx_limit_addr = 0x4000},
                             {.imbx_base_addr = 0x1000,
                              .imbx_limit_addr = 0x1001,
                              .ombx_base_addr = 0x1001,
                              .ombx_limit_addr = 0x1002},
                         }}));

class MemoryRangeBadArgTests
    : public MbxTestInitialized,
      public testing::WithParamInterface<dif_mbx_range_config_t> {};

TEST_P(MemoryRangeBadArgTests, SetBadArg) {
  dif_mbx_range_config_t range = GetParam();

  EXPECT_DIF_BADARG(dif_mbx_range_set(&mbx_, range));
}

INSTANTIATE_TEST_SUITE_P(MemoryRangeBadArgTests, MemoryRangeBadArgTests,
                         testing::ValuesIn(std::vector<dif_mbx_range_config_t>{{
                             {.imbx_base_addr = 0x1000,
                              .imbx_limit_addr = 0,
                              .ombx_base_addr = 0x2000,
                              .ombx_limit_addr = 0x4000},
                             {.imbx_base_addr = 0x1000,
                              .imbx_limit_addr = 0x5000,
                              .ombx_base_addr = 0x4000,
                              .ombx_limit_addr = 0x4000},
                             {.imbx_base_addr = 0x1000,
                              .imbx_limit_addr = 0x2000,
                              .ombx_base_addr = 0x1500,
                              .ombx_limit_addr = 0x2500},
                             {.imbx_base_addr = 0x1500,
                              .imbx_limit_addr = 0x2500,
                              .ombx_base_addr = 0x1000,
                              .ombx_limit_addr = 0x2000},
                         }}));

TEST_F(MemoryRangeBadArgTests, GetBadArg) {
  dif_mbx_range_config_t range;

  EXPECT_DIF_BADARG(dif_mbx_range_set(nullptr, range));
}

class MemoryRangeTests : public MbxTestInitialized {};

TEST_F(MemoryRangeTests, GetSuccess) {
  dif_mbx_range_config_t range = {.imbx_base_addr = 0xD0CF2C50,
                                  .imbx_limit_addr = 0xD1CF2C0F,
                                  .ombx_base_addr = 0xD1CF3C0F,
                                  .ombx_limit_addr = 0xD1CF3C19};

  EXPECT_READ32(MBX_INBOUND_BASE_ADDRESS_REG_OFFSET, range.imbx_base_addr);
  EXPECT_READ32(MBX_INBOUND_LIMIT_ADDRESS_REG_OFFSET, range.imbx_limit_addr);
  EXPECT_READ32(MBX_OUTBOUND_BASE_ADDRESS_REG_OFFSET, range.ombx_base_addr);
  EXPECT_READ32(MBX_OUTBOUND_LIMIT_ADDRESS_REG_OFFSET, range.ombx_limit_addr);

  dif_mbx_range_config_t read_range;
  EXPECT_DIF_OK(dif_mbx_range_get(&mbx_, &read_range));

  EXPECT_EQ(read_range.imbx_base_addr, range.imbx_base_addr);
  EXPECT_EQ(read_range.imbx_limit_addr, range.imbx_limit_addr);
  EXPECT_EQ(read_range.ombx_base_addr, range.ombx_base_addr);
  EXPECT_EQ(read_range.ombx_limit_addr, range.ombx_limit_addr);
}

TEST_F(MemoryRangeTests, GetBadArg) {
  dif_mbx_range_config_t range;

  EXPECT_DIF_BADARG(dif_mbx_range_get(nullptr, &range));
  EXPECT_DIF_BADARG(dif_mbx_range_get(&mbx_, nullptr));
}


}  // namespace dif_mbx_test
