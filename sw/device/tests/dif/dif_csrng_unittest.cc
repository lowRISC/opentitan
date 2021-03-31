// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "csrng_regs.h"  // Generated

namespace dif_entropy_unittest {
namespace {

class DifCsrngTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  const dif_csrng_params_t params_ = {.base_addr = dev().region()};
  const dif_csrng_t csrng_ = {
      .params = {.base_addr = dev().region()},
  };
};

class InitTest : public DifCsrngTest {};

TEST_F(InitTest, BadArgs) {
  EXPECT_EQ(dif_csrng_init(params_, nullptr), kDifCsrngBadArg);
}

TEST_F(InitTest, InitOk) {
  dif_csrng_t csrng;
  EXPECT_EQ(dif_csrng_init(params_, &csrng), kDifCsrngOk);
}

class ConfigTest : public DifCsrngTest {
 protected:
  /**
   * Sets CTRL write register expectations.
   */
  void ExpectCtrlWrite(bool bypass_aes_cipher) {
    EXPECT_WRITE32(CSRNG_CTRL_REG_OFFSET,
                   {
                       {CSRNG_CTRL_ENABLE_BIT, true},
                       {CSRNG_CTRL_AES_CIPHER_DISABLE_BIT, bypass_aes_cipher},
                       {CSRNG_CTRL_FIFO_DEPTH_STS_SEL_OFFSET, 0},
                   });
  }

  dif_csrng_config_t config_ = {
      .debug_config = {.bypass_aes_cipher = false},
  };
};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_csrng_configure(nullptr, {}), kDifCsrngBadArg);
}

TEST_F(ConfigTest, ConfigOk) {
  config_.debug_config.bypass_aes_cipher = false;
  ExpectCtrlWrite(config_.debug_config.bypass_aes_cipher);
  EXPECT_EQ(dif_csrng_configure(&csrng_, config_), kDifCsrngOk);
}

TEST_F(ConfigTest, ConfigAesBypassOk) {
  config_.debug_config.bypass_aes_cipher = true;
  ExpectCtrlWrite(config_.debug_config.bypass_aes_cipher);
  EXPECT_EQ(dif_csrng_configure(&csrng_, config_), kDifCsrngOk);
}

class GetCmdInterfaceStatusTest : public DifCsrngTest {};

TEST_F(GetCmdInterfaceStatusTest, NullArgs) {
  dif_csrng_cmd_status_t status;
  EXPECT_EQ(dif_csrng_get_cmd_interface_status(nullptr, &status),
            kDifCsrngBadArg);

  EXPECT_EQ(dif_csrng_get_cmd_interface_status(&csrng_, nullptr),
            kDifCsrngBadArg);
}

struct GetCmdInterfaceStatusParams {
  bool cmd_ready;
  bool cmd_status;
  dif_csrng_cmd_status_t expected_status;
};

class GetCmdInterfaceStatusTestAllParams
    : public GetCmdInterfaceStatusTest,
      public testing::WithParamInterface<GetCmdInterfaceStatusParams> {};

TEST_P(GetCmdInterfaceStatusTestAllParams, ValidConfigurationMode) {
  const GetCmdInterfaceStatusParams &test_param = GetParam();
  dif_csrng_cmd_status_t status;
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {
                    {CSRNG_SW_CMD_STS_CMD_RDY_BIT, test_param.cmd_ready},
                    {CSRNG_SW_CMD_STS_CMD_STS_BIT, test_param.cmd_status},
                });
  EXPECT_EQ(dif_csrng_get_cmd_interface_status(&csrng_, &status), kDifCsrngOk);
  EXPECT_EQ(status, test_param.expected_status);
}

INSTANTIATE_TEST_SUITE_P(
    GetCmdInterfaceStatusTestAllParams, GetCmdInterfaceStatusTestAllParams,
    testing::Values(
        GetCmdInterfaceStatusParams{true, false, kDifCsrngCmdStatusReady},
        GetCmdInterfaceStatusParams{true, true, kDifCsrngCmdStatusError},
        GetCmdInterfaceStatusParams{false, true, kDifCsrngCmdStatusError},
        GetCmdInterfaceStatusParams{false, false, kDifCsrngCmdStatusBusy}));

class GetOutputStatusTest : public DifCsrngTest {};

TEST_F(GetOutputStatusTest, NullArgs) {
  dif_csrng_output_status_t status;
  EXPECT_EQ(dif_csrng_get_output_status(nullptr, &status), kDifCsrngBadArg);

  EXPECT_EQ(dif_csrng_get_output_status(&csrng_, nullptr), kDifCsrngBadArg);
}

TEST_F(GetOutputStatusTest, ValidStatus) {
  // Each option is initialized to a boolean complement of the other so
  // that we can test both fields toggling in one pass.
  dif_csrng_output_status_t status = {.valid_data = false, .fips_mode = true};
  EXPECT_READ32(CSRNG_GENBITS_VLD_REG_OFFSET,
                {
                    {CSRNG_GENBITS_VLD_GENBITS_VLD_BIT, true},
                    {CSRNG_GENBITS_VLD_GENBITS_FIPS_BIT, false},
                });

  EXPECT_EQ(dif_csrng_get_output_status(&csrng_, &status), kDifCsrngOk);
  EXPECT_EQ(status.valid_data, true);
  EXPECT_EQ(status.fips_mode, false);
}

}  // namespace
}  // namespace dif_entropy_unittest
