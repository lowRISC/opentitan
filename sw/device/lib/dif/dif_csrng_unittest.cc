// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng.h"

#include <array>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "csrng_regs.h"  // Generated

namespace dif_csrng_unittest {
namespace {

using ::testing::ElementsAreArray;

class DifCsrngTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  const dif_csrng_t csrng_ = {.base_addr = dev().region()};
};

class ConfigTest : public DifCsrngTest {};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_csrng_configure(nullptr), kDifBadArg);
}

TEST_F(ConfigTest, ConfigOk) {
  EXPECT_WRITE32(CSRNG_CTRL_REG_OFFSET, 0xaaa);
  EXPECT_DIF_OK(dif_csrng_configure(&csrng_));
}

class GetCmdInterfaceStatusTest : public DifCsrngTest {};

TEST_F(GetCmdInterfaceStatusTest, NullArgs) {
  dif_csrng_cmd_status_t status;
  EXPECT_EQ(dif_csrng_get_cmd_interface_status(nullptr, &status), kDifBadArg);

  EXPECT_EQ(dif_csrng_get_cmd_interface_status(&csrng_, nullptr), kDifBadArg);
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
  EXPECT_DIF_OK(dif_csrng_get_cmd_interface_status(&csrng_, &status));
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
  EXPECT_EQ(dif_csrng_get_output_status(nullptr, &status), kDifBadArg);

  EXPECT_EQ(dif_csrng_get_output_status(&csrng_, nullptr), kDifBadArg);
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

  EXPECT_DIF_OK(dif_csrng_get_output_status(&csrng_, &status));
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
  EXPECT_DIF_OK(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleDisable,
                                      &seed_material_));

  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000001);
  EXPECT_DIF_OK(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleEnable,
                                      &seed_material_));

  seed_material_.seed_material[0] = 0x5a5a5a5a;
  seed_material_.seed_material_len = 1;
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000011);
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_DIF_OK(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleEnable,
                                      &seed_material_));
}

TEST_F(CommandTest, InstantiateBadArgs) {
  EXPECT_EQ(dif_csrng_instantiate(nullptr, kDifCsrngEntropySrcToggleDisable,
                                  &seed_material_),
            kDifBadArg);

  // Failed overflow check.
  seed_material_.seed_material_len = 16;
  EXPECT_EQ(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleDisable,
                                  &seed_material_),
            kDifBadArg);
}

TEST_F(CommandTest, ReseedOk) {
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000002);
  EXPECT_DIF_OK(dif_csrng_reseed(&csrng_, &seed_material_));

  seed_material_.seed_material[0] = 0x5a5a5a5a;
  seed_material_.seed_material_len = 1;
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000012);
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_DIF_OK(dif_csrng_reseed(&csrng_, &seed_material_));
}

TEST_F(CommandTest, ReseedBadArgs) {
  EXPECT_EQ(dif_csrng_reseed(nullptr, &seed_material_), kDifBadArg);

  // Failed overflow check.
  seed_material_.seed_material_len = 16;
  EXPECT_EQ(dif_csrng_reseed(&csrng_, &seed_material_), kDifBadArg);
}

TEST_F(CommandTest, UpdateOk) {
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000004);
  EXPECT_DIF_OK(dif_csrng_update(&csrng_, &seed_material_));

  seed_material_.seed_material[0] = 0x5a5a5a5a;
  seed_material_.seed_material_len = 1;
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000014);
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_DIF_OK(dif_csrng_update(&csrng_, &seed_material_));
}

TEST_F(CommandTest, UpdateBadArgs) {
  EXPECT_EQ(dif_csrng_update(nullptr, &seed_material_), kDifBadArg);
}

TEST_F(CommandTest, GenerateOk) {
  // 512bits = 16 x 32bit = 4 x 128bit blocks
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00004003);
  EXPECT_DIF_OK(dif_csrng_generate_start(&csrng_, /*len=*/16));

  // 576bits = 18 x 32bit = 5 x 128bit blocks (rounded up)
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00005003);
  EXPECT_DIF_OK(dif_csrng_generate_start(&csrng_, /*len=*/18));
}

TEST_F(CommandTest, GenerateBadArgs) {
  EXPECT_EQ(dif_csrng_generate_start(nullptr, /*len=*/1), kDifBadArg);
  EXPECT_EQ(dif_csrng_generate_start(&csrng_, /*len=*/0), kDifBadArg);
}

TEST_F(CommandTest, UninstantiateOk) {
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x00000005);
  EXPECT_DIF_OK(dif_csrng_uninstantiate(&csrng_));
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
  EXPECT_DIF_OK(dif_csrng_generate_end(&csrng_, got.data(), got.size()));
  EXPECT_THAT(got, testing::ElementsAreArray(kExpected));
}

TEST_F(GenerateEndTest, ReadBadArgs) {
  EXPECT_EQ(dif_csrng_generate_end(&csrng_, nullptr, /*len=*/0), kDifBadArg);

  uint32_t data;
  EXPECT_EQ(dif_csrng_generate_end(nullptr, &data, /*len=*/1), kDifBadArg);
}

class GetInternalStateTest : public DifCsrngTest {};

TEST_F(GetInternalStateTest, GetInternalStateOk) {
  dif_csrng_internal_state_id_t instance_id = kCsrngInternalStateIdSw;

  EXPECT_WRITE32(CSRNG_INT_STATE_NUM_REG_OFFSET,
                 {
                     {CSRNG_INT_STATE_NUM_INT_STATE_NUM_OFFSET,
                      static_cast<uint32_t>(instance_id)},
                 });

  dif_csrng_internal_state_t expected = {
      .reseed_counter = 1,
      .v = {1, 2, 3, 4},
      .key = {1, 2, 3, 4, 5, 6, 7, 8},
      .instantiated = true,
      .fips_compliance = true,
  };
  EXPECT_READ32(CSRNG_INT_STATE_VAL_REG_OFFSET, expected.reseed_counter);
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_READ32(CSRNG_INT_STATE_VAL_REG_OFFSET, expected.v[i]);
  }
  for (size_t i = 0; i < 8; ++i) {
    EXPECT_READ32(CSRNG_INT_STATE_VAL_REG_OFFSET, expected.key[i]);
  }
  EXPECT_READ32(CSRNG_INT_STATE_VAL_REG_OFFSET, 3);

  dif_csrng_internal_state_t got;
  EXPECT_DIF_OK(dif_csrng_get_internal_state(&csrng_, instance_id, &got));

  EXPECT_EQ(got.reseed_counter, expected.reseed_counter);
  EXPECT_THAT(got.key, ElementsAreArray(expected.key));
  EXPECT_THAT(got.v, ElementsAreArray(expected.v));
  EXPECT_EQ(got.instantiated, expected.instantiated);
  EXPECT_EQ(got.fips_compliance, expected.fips_compliance);
}

TEST_F(GetInternalStateTest, GetInternalStateBadArgs) {
  EXPECT_EQ(
      dif_csrng_get_internal_state(&csrng_, kCsrngInternalStateIdSw, nullptr),
      kDifBadArg);

  dif_csrng_internal_state unused;
  EXPECT_EQ(
      dif_csrng_get_internal_state(nullptr, kCsrngInternalStateIdSw, &unused),
      kDifBadArg);
}

}  // namespace
}  // namespace dif_csrng_unittest
