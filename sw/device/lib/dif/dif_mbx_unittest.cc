// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_mbx.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
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
  rom_test::MockAbsMmio mmio_;

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

// 'Limit' addresses are _inclusive_.
INSTANTIATE_TEST_SUITE_P(
    MemoryRangeSuccessTests, MemoryRangeSuccessTests,
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
         .imbx_limit_addr = 0x1003,  // Inbound mailbox is a single DWORD.
         .ombx_base_addr = 0x1004,
         .ombx_limit_addr = 0x1007},  // Single DWORD
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

typedef struct status_reg {
  uint32_t reg;
  bool is_busy;
} status_reg_t;

class ProcessBusyTests : public MbxTestInitialized,
                         public testing::WithParamInterface<status_reg_t> {};

TEST_P(ProcessBusyTests, GetSuccess) {
  status_reg_t status_arg = GetParam();

  EXPECT_READ32(MBX_STATUS_REG_OFFSET, status_arg.reg);

  bool is_busy = !status_arg.is_busy;

  EXPECT_DIF_OK(dif_mbx_is_busy(&mbx_, &is_busy));
  EXPECT_EQ(is_busy, status_arg.is_busy);
}

INSTANTIATE_TEST_SUITE_P(ProcessBusyTests, ProcessBusyTests,
                         testing::ValuesIn(std::vector<status_reg_t>{{
                             {0, false},
                             {1 << MBX_STATUS_BUSY_BIT, true},
                         }}));

TEST_F(ProcessBusyTests, GetBadArg) {
  bool is_busy;
  EXPECT_DIF_BADARG(dif_mbx_is_busy(nullptr, &is_busy));
  EXPECT_DIF_BADARG(dif_mbx_is_busy(&mbx_, nullptr));
}

class ProcessRequestTests : public MbxTestInitialized {};

TEST_F(ProcessRequestTests, Success) {
  dif_mbx_transaction_t request;
  uint32_t data[4];
  request.data_dwords = data;

  EXPECT_READ32(MBX_INBOUND_BASE_ADDRESS_REG_OFFSET, 0x1000);
  EXPECT_READ32(MBX_INBOUND_WRITE_PTR_REG_OFFSET, 0x1010);

  EXPECT_ABS_READ32(0x1000, 0x123456);
  EXPECT_ABS_READ32(0x1004, 0x456789);
  EXPECT_ABS_READ32(0x1008, 0xDEADBEEF);
  EXPECT_ABS_READ32(0x100C, 0xCAFEDEAD);

  EXPECT_DIF_OK(dif_mbx_process_request(&mbx_, &request));

  EXPECT_EQ(request.nr_dwords, 4);
  EXPECT_EQ(request.data_dwords[0], 0x123456);
  EXPECT_EQ(request.data_dwords[1], 0x456789);
  EXPECT_EQ(request.data_dwords[2], 0xDEADBEEF);
  EXPECT_EQ(request.data_dwords[3], 0xCAFEDEAD);
}

TEST_F(ProcessRequestTests, BadArg) {
  dif_mbx_transaction_t request;
  request.data_dwords = nullptr;
  request.nr_dwords = 1;

  EXPECT_DIF_BADARG(dif_mbx_process_request(nullptr, &request));
  EXPECT_DIF_BADARG(dif_mbx_process_request(&mbx_, nullptr));
  EXPECT_DIF_BADARG(dif_mbx_process_request(&mbx_, &request));
}

class ProcessResponseTests : public MbxTestInitialized {};

TEST_F(ProcessResponseTests, Success) {
  dif_mbx_transaction_t response;
  std::array<uint32_t, 4> data = {0x123456, 0x456789, 0xDEADBEEF, 0xCAFEDEAD};
  response.nr_dwords = data.size();
  response.data_dwords = data.data();

  EXPECT_READ32(MBX_OUTBOUND_READ_PTR_REG_OFFSET, 0x1000);
  EXPECT_ABS_WRITE32(0x1000, data[0]);
  EXPECT_ABS_WRITE32(0x1004, data[1]);
  EXPECT_ABS_WRITE32(0x1008, data[2]);
  EXPECT_ABS_WRITE32(0x100C, data[3]);
  EXPECT_WRITE32(MBX_OUTBOUND_OBJECT_SIZE_REG_OFFSET, response.nr_dwords);

  EXPECT_DIF_OK(dif_mbx_generate_response(&mbx_, response));
}

TEST_F(ProcessResponseTests, BadArg) {
  dif_mbx_transaction_t response1;
  response1.nr_dwords = DOE_MAILBOX_MAX_OBJECT_SIZE + 1;

  dif_mbx_transaction_t response2;
  response2.data_dwords = nullptr;
  response2.nr_dwords = 1;

  EXPECT_DIF_BADARG(dif_mbx_generate_response(nullptr, response1));
  EXPECT_DIF_BADARG(dif_mbx_generate_response(&mbx_, response1));
  EXPECT_DIF_BADARG(dif_mbx_generate_response(&mbx_, response2));
}

}  // namespace dif_mbx_test
