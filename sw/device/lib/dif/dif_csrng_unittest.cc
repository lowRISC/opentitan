// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng.h"

#include <array>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

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

/**
 * DRBG commands are tested using this test group as the underlying
 * command interface is shared across API functions.
 */
class CommandTest : public DifCsrngTest {
 protected:
  dif_csrng_seed_material_t seed_material_ = {
      .seed_material_len = 0,
      .seed_material = {0},
  };
};

TEST_F(CommandTest, InstantiateOk) {
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000101);
  EXPECT_EQ(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleDisable,
                                  &seed_material_),
            kDifCsrngOk);

  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000001);
  EXPECT_EQ(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleEnable,
                                  &seed_material_),
            kDifCsrngOk);

  seed_material_.seed_material[0] = 0x5a5a5a5a;
  seed_material_.seed_material_len = 1;
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000011);
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_EQ(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleEnable,
                                  &seed_material_),
            kDifCsrngOk);
}

TEST_F(CommandTest, InstantiateBadArgs) {
  EXPECT_EQ(dif_csrng_instantiate(nullptr, kDifCsrngEntropySrcToggleDisable,
                                  &seed_material_),
            kDifCsrngBadArg);

  // Failed overflow check.
  seed_material_.seed_material_len = 16;
  EXPECT_EQ(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleDisable,
                                  &seed_material_),
            kDifCsrngBadArg);
}

TEST_F(CommandTest, ReseedOk) {
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000002);
  EXPECT_EQ(dif_csrng_reseed(&csrng_, &seed_material_), kDifCsrngOk);

  seed_material_.seed_material[0] = 0x5a5a5a5a;
  seed_material_.seed_material_len = 1;
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000012);
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_EQ(dif_csrng_reseed(&csrng_, &seed_material_), kDifCsrngOk);
}

TEST_F(CommandTest, ReseedBadArgs) {
  EXPECT_EQ(dif_csrng_reseed(nullptr, &seed_material_), kDifCsrngBadArg);

  // Failed overflow check.
  seed_material_.seed_material_len = 16;
  EXPECT_EQ(dif_csrng_reseed(&csrng_, &seed_material_), kDifCsrngBadArg);
}

TEST_F(CommandTest, UpdateOk) {
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000004);
  EXPECT_EQ(dif_csrng_update(&csrng_, &seed_material_), kDifCsrngOk);

  seed_material_.seed_material[0] = 0x5a5a5a5a;
  seed_material_.seed_material_len = 1;
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000014);
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_EQ(dif_csrng_update(&csrng_, &seed_material_), kDifCsrngOk);
}

TEST_F(CommandTest, UpdateBadArgs) {
  EXPECT_EQ(dif_csrng_update(nullptr, &seed_material_), kDifCsrngBadArg);
}

TEST_F(CommandTest, GenerateOk) {
  // 512bits = 16 x 32bit = 4 x 128bit blocks
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00004003);
  EXPECT_EQ(dif_csrng_generate_start(&csrng_, /*len=*/16), kDifCsrngOk);

  // 576bits = 18 x 32bit = 5 x 128bit blocks (rounded up)
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00005003);
  EXPECT_EQ(dif_csrng_generate_start(&csrng_, /*len=*/18), kDifCsrngOk);
}

TEST_F(CommandTest, GenerateBadArgs) {
  EXPECT_EQ(dif_csrng_generate_start(nullptr, /*len=*/1), kDifCsrngBadArg);
  EXPECT_EQ(dif_csrng_generate_start(&csrng_, /*len=*/0), kDifCsrngBadArg);
}

TEST_F(CommandTest, UninstantiateOk) {
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000005);
  EXPECT_EQ(dif_csrng_uninstantiate(&csrng_), kDifCsrngOk);
}

class GenerateEndTest : public DifCsrngTest {};

TEST_F(GenerateEndTest, ReadOk) {
  constexpr std::array<uint32_t, 4> kExpected = {
      0x00000000,
      0x11111111,
      0x22222222,
      0x33333333,
  };

  EXPECT_READ32(CSRNG_GENBITS_VLD_REG_OFFSET,
                {
                    {CSRNG_GENBITS_VLD_GENBITS_VLD_BIT, true},
                });
  for (const uint32_t val : kExpected) {
    EXPECT_READ32(CSRNG_GENBITS_REG_OFFSET, val);
  }

  std::vector<uint32_t> got(kExpected.size());
  EXPECT_EQ(dif_csrng_generate_end(&csrng_, got.data(), got.size()),
            kDifCsrngOk);
  EXPECT_THAT(got, testing::ElementsAreArray(kExpected));
}

TEST_F(GenerateEndTest, ReadBadArgs) {
  EXPECT_EQ(dif_csrng_generate_end(&csrng_, nullptr, /*len=*/0),
            kDifCsrngBadArg);

  uint32_t data;
  EXPECT_EQ(dif_csrng_generate_end(nullptr, &data, /*len=*/1), kDifCsrngBadArg);
}

}  // namespace
}  // namespace dif_entropy_unittest
