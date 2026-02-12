// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_csrng.h"

#include <array>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "hw/top/csrng_regs.h"  // Generated

namespace dif_csrng_unittest {
namespace {

using ::testing::ElementsAreArray;

class DifCsrngTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  const dif_csrng_t csrng_ = {.base_addr = dev().region()};
};

class ConfigTest : public DifCsrngTest {};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_csrng_configure(nullptr));
}

TEST_F(ConfigTest, ConfigOk) {
  constexpr uint32_t exp = kMultiBitBool4True | kMultiBitBool4True << 4 |
                           kMultiBitBool4True << 8 | kMultiBitBool4False << 12;
  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(CSRNG_CTRL_REG_OFFSET, exp);
  EXPECT_DIF_OK(dif_csrng_configure(&csrng_));
}

TEST_F(ConfigTest, Locked) {
  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_csrng_configure(&csrng_), kDifLocked);
}

class GetCmdInterfaceStatusTest : public DifCsrngTest {};

TEST_F(GetCmdInterfaceStatusTest, NullArgs) {
  dif_csrng_cmd_status_t status;
  EXPECT_DIF_BADARG(dif_csrng_get_cmd_interface_status(nullptr, &status));

  EXPECT_DIF_BADARG(dif_csrng_get_cmd_interface_status(&csrng_, nullptr));
}

struct StatusTestCase {
  bool cmd_ready;
  bool cmd_ack;
  uint32_t cmd_status;
  dif_csrng_cmd_status_t expected_status;
};

class GetCmdInterfaceStatusTestAllParams
    : public GetCmdInterfaceStatusTest,
      public testing::WithParamInterface<StatusTestCase> {};

TEST_P(GetCmdInterfaceStatusTestAllParams, ValidConfigurationMode) {
  const auto &test_param = GetParam();
  dif_csrng_cmd_status_t status{};
  uint32_t ctrl_reg = 0;
  ctrl_reg = bitfield_bit32_write(ctrl_reg, CSRNG_SW_CMD_STS_CMD_RDY_BIT,
                                  test_param.cmd_ready);
  ctrl_reg = bitfield_bit32_write(ctrl_reg, CSRNG_SW_CMD_STS_CMD_ACK_BIT,
                                  test_param.cmd_ack);
  ctrl_reg = bitfield_field32_write(ctrl_reg, CSRNG_SW_CMD_STS_CMD_STS_FIELD,
                                    test_param.cmd_status);
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET, ctrl_reg);
  EXPECT_DIF_OK(dif_csrng_get_cmd_interface_status(&csrng_, &status));
  EXPECT_EQ(status.kind, test_param.expected_status.kind);
  EXPECT_EQ(status.cmd_sts, test_param.expected_status.cmd_sts);
}

INSTANTIATE_TEST_SUITE_P(
    GetCmdInterfaceStatusTestAllParams, GetCmdInterfaceStatusTestAllParams,
    testing::Values(StatusTestCase{true, 0, 0x0, {kDifCsrngCmdStatusReady}},
                    StatusTestCase{false, 0, 0x0, {kDifCsrngCmdStatusBusy}},
                    StatusTestCase{true, 1, 0x0, {kDifCsrngCmdStatusReady}},
                    StatusTestCase{
                        false,
                        1,
                        kDifCsrngCmdStsInvalidAcmd,
                        {
                            .kind = kDifCsrngCmdStatusError,
                            .cmd_sts = kDifCsrngCmdStsInvalidAcmd,
                        },
                    }));

class ForceErrorTest : public DifCsrngTest {};

TEST_F(ForceErrorTest, BadArgs) {
  EXPECT_DIF_BADARG(dif_csrng_get_cmd_force_unhealthy_fifo(
      &csrng_, static_cast<dif_csrng_fifo_t>(-1)));
  EXPECT_DIF_BADARG(
      dif_csrng_get_cmd_force_unhealthy_fifo(nullptr, kDifCsrngFifoGenBits));
  EXPECT_DIF_BADARG(dif_csrng_get_cmd_force_error(
      &csrng_, static_cast<dif_csrng_error_t>(-1)));
  EXPECT_DIF_BADARG(
      dif_csrng_get_cmd_force_error(nullptr, kDifCsrngErrorAesSm));
}

TEST_F(ForceErrorTest, ForceFifo) {
  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(CSRNG_ERR_CODE_TEST_REG_OFFSET,
                 CSRNG_ERR_CODE_SFIFO_GENBITS_ERR_BIT);
  EXPECT_DIF_OK(
      dif_csrng_get_cmd_force_unhealthy_fifo(&csrng_, kDifCsrngFifoGenBits));
}

TEST_F(ForceErrorTest, ForceError) {
  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(CSRNG_ERR_CODE_TEST_REG_OFFSET,
                 CSRNG_ERR_CODE_AES_CIPHER_SM_ERR_BIT);
  EXPECT_DIF_OK(dif_csrng_get_cmd_force_error(&csrng_, kDifCsrngErrorAesSm));
}

TEST_F(ForceErrorTest, Locked) {
  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 0);
  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(
      dif_csrng_get_cmd_force_unhealthy_fifo(&csrng_, kDifCsrngFifoGenBits),
      kDifLocked);
  EXPECT_EQ(dif_csrng_get_cmd_force_error(&csrng_, kDifCsrngErrorAesSm),
            kDifLocked);
}

class MiscStatusTest : public DifCsrngTest {};

TEST_F(MiscStatusTest, BadArgs) {
  uint32_t out;
  EXPECT_DIF_BADARG(dif_csrng_get_main_state_machine(nullptr, &out));
  EXPECT_DIF_BADARG(dif_csrng_get_main_state_machine(&csrng_, nullptr));
  EXPECT_DIF_BADARG(dif_csrng_get_hw_csrng_exceptions(nullptr, &out));
  EXPECT_DIF_BADARG(dif_csrng_get_hw_csrng_exceptions(&csrng_, nullptr));
  EXPECT_DIF_BADARG(dif_csrng_clear_hw_csrng_exceptions(nullptr));
}

TEST_F(MiscStatusTest, GetMainSm) {
  EXPECT_READ32(CSRNG_MAIN_SM_STATE_REG_OFFSET, 42);

  uint32_t out;
  EXPECT_DIF_OK(dif_csrng_get_main_state_machine(&csrng_, &out));
  EXPECT_EQ(out, 42);
}

TEST_F(MiscStatusTest, GetExceptions) {
  EXPECT_READ32(CSRNG_HW_EXC_STS_REG_OFFSET, 42);

  uint32_t out;
  EXPECT_DIF_OK(dif_csrng_get_hw_csrng_exceptions(&csrng_, &out));
  EXPECT_EQ(out, 42);
}

TEST_F(MiscStatusTest, ClearExceptions) {
  EXPECT_WRITE32(CSRNG_HW_EXC_STS_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_clear_hw_csrng_exceptions(&csrng_));
}

class GetOutputStatusTest : public DifCsrngTest {};

TEST_F(GetOutputStatusTest, NullArgs) {
  dif_csrng_output_status_t status;
  EXPECT_DIF_BADARG(dif_csrng_get_output_status(nullptr, &status));

  EXPECT_DIF_BADARG(dif_csrng_get_output_status(&csrng_, nullptr));
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
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00000001 | kMultiBitBool4True << 8);
  EXPECT_DIF_OK(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleDisable,
                                      &seed_material_));

  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00000001 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleEnable,
                                      &seed_material_));

  seed_material_.seed_material[0] = 0x5a5a5a5a;
  seed_material_.seed_material_len = 1;
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00000011 | kMultiBitBool4False << 8);
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_DIF_OK(dif_csrng_instantiate(&csrng_, kDifCsrngEntropySrcToggleEnable,
                                      &seed_material_));
}

TEST_F(CommandTest, InstantiateBadArgs) {
  EXPECT_DIF_BADARG(dif_csrng_instantiate(
      nullptr, kDifCsrngEntropySrcToggleDisable, &seed_material_));

  // Failed overflow check.
  seed_material_.seed_material_len = 16;
  EXPECT_DIF_BADARG(dif_csrng_instantiate(
      &csrng_, kDifCsrngEntropySrcToggleDisable, &seed_material_));
}

TEST_F(CommandTest, ReseedOk) {
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00000002 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_csrng_reseed(&csrng_, &seed_material_));

  seed_material_.seed_material[0] = 0x5a5a5a5a;
  seed_material_.seed_material_len = 1;
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00000012 | kMultiBitBool4False << 8);
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_DIF_OK(dif_csrng_reseed(&csrng_, &seed_material_));
}

TEST_F(CommandTest, ReseedBadArgs) {
  EXPECT_DIF_BADARG(dif_csrng_reseed(nullptr, &seed_material_));

  // Failed overflow check.
  seed_material_.seed_material_len = 16;
  EXPECT_DIF_BADARG(dif_csrng_reseed(&csrng_, &seed_material_));
}

TEST_F(CommandTest, UpdateOk) {
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00000004 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_csrng_update(&csrng_, &seed_material_));

  seed_material_.seed_material[0] = 0x5a5a5a5a;
  seed_material_.seed_material_len = 1;
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00000014 | kMultiBitBool4False << 8);
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_DIF_OK(dif_csrng_update(&csrng_, &seed_material_));
}

TEST_F(CommandTest, UpdateBadArgs) {
  EXPECT_DIF_BADARG(dif_csrng_update(nullptr, &seed_material_));
}

TEST_F(CommandTest, GenerateOk) {
  // 512bits = 16 x 32bit = 4 x 128bit blocks
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00004003 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_csrng_generate_start(&csrng_, nullptr, /*len=*/16));

  // 576bits = 18 x 32bit = 5 x 128bit blocks (rounded up)
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00005003 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_csrng_generate_start(&csrng_, nullptr, /*len=*/18));
}

TEST_F(CommandTest, GenerateBadArgs) {
  EXPECT_DIF_BADARG(dif_csrng_generate_start(nullptr, nullptr, /*len=*/1));
  EXPECT_DIF_BADARG(dif_csrng_generate_start(&csrng_, nullptr, /*len=*/0));
}

TEST_F(CommandTest, GenerateOutOfRange) {
  enum {
    // The maximum allowed is 0x800 128-bit blocks. Multiply by 4 to get the
    // number of uint32 words and add one to trigger the error.
    kGenerateLenOutOfRange = 0x800 * 4 + 1,
  };
  EXPECT_DIF_OUTOFRANGE(
      dif_csrng_generate_start(&csrng_, nullptr, kGenerateLenOutOfRange));
}

TEST_F(CommandTest, UninstantiateOk) {
  EXPECT_READ32(CSRNG_SW_CMD_STS_REG_OFFSET,
                {{CSRNG_SW_CMD_STS_CMD_RDY_BIT, true}});
  EXPECT_WRITE32(CSRNG_CMD_REQ_REG_OFFSET,
                 0x00000005 | kMultiBitBool4False << 8);
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
  EXPECT_DIF_OK(dif_csrng_generate_read(&csrng_, got.data(), got.size()));
  EXPECT_THAT(got, testing::ElementsAreArray(kExpected));
}

TEST_F(GenerateEndTest, ReadBadArgs) {
  EXPECT_DIF_BADARG(dif_csrng_generate_read(&csrng_, nullptr, /*len=*/0));

  uint32_t data;
  EXPECT_DIF_BADARG(dif_csrng_generate_read(nullptr, &data, /*len=*/1));
}

class GetInternalStateTest : public DifCsrngTest {};

TEST_F(GetInternalStateTest, GetInternalStateOk) {
  dif_csrng_internal_state_id_t instance_id = kCsrngInternalStateIdSw;

  EXPECT_WRITE32(CSRNG_INT_STATE_NUM_REG_OFFSET,
                 {
                     {CSRNG_INT_STATE_NUM_INT_STATE_NUM_OFFSET,
                      static_cast<uint32_t>(instance_id)},
                 });
  EXPECT_READ32(CSRNG_INT_STATE_NUM_REG_OFFSET,
                {
                    {CSRNG_INT_STATE_NUM_INT_STATE_NUM_OFFSET,
                     static_cast<uint32_t>(instance_id)},
                });

  dif_csrng_internal_state_t expected = {
      .reseed_counter = 0,
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

TEST_F(GetInternalStateTest, BadIntStateNumWrite) {
  EXPECT_WRITE32(CSRNG_INT_STATE_NUM_REG_OFFSET,
                 {
                     {CSRNG_INT_STATE_NUM_INT_STATE_NUM_OFFSET,
                      static_cast<uint32_t>(kCsrngInternalStateIdSw)},
                 });
  EXPECT_READ32(CSRNG_INT_STATE_NUM_REG_OFFSET,
                {
                    {CSRNG_INT_STATE_NUM_INT_STATE_NUM_OFFSET, 0},
                });

  dif_csrng_internal_state_t got;
  EXPECT_EQ(
      dif_csrng_get_internal_state(&csrng_, kCsrngInternalStateIdSw, &got),
      kDifError);
}

TEST_F(GetInternalStateTest, GetInternalStateBadArgs) {
  EXPECT_DIF_BADARG(
      dif_csrng_get_internal_state(&csrng_, kCsrngInternalStateIdSw, nullptr));

  dif_csrng_internal_state unused;
  EXPECT_DIF_BADARG(
      dif_csrng_get_internal_state(nullptr, kCsrngInternalStateIdSw, &unused));
}

class GetReseedCounterTest : public DifCsrngTest {};

TEST_F(GetReseedCounterTest, GetReseedCounterOk) {
  dif_csrng_internal_state_id_t instance_id = kCsrngInternalStateIdSw;
  uint32_t reseed_counter;

  EXPECT_READ32(
      (CSRNG_RESEED_COUNTER_0_REG_OFFSET + ((uint32_t)(instance_id) << 2)), 0);
  EXPECT_DIF_OK(
      dif_csrng_get_reseed_counter(&csrng_, instance_id, &reseed_counter));
}

TEST_F(GetReseedCounterTest, GetReseedCounterBadArgs) {
  EXPECT_DIF_BADARG(
      dif_csrng_get_reseed_counter(&csrng_, kCsrngInternalStateIdSw, nullptr));

  uint32_t unused;
  EXPECT_DIF_BADARG(
      dif_csrng_get_reseed_counter(nullptr, kCsrngInternalStateIdSw, &unused));

  EXPECT_DIF_BADARG(dif_csrng_get_reseed_counter(
      &csrng_, static_cast<dif_csrng_internal_state_id_t>(-1), &unused));
}

class LockTest : public DifCsrngTest {};

TEST_F(LockTest, BadArgs) {
  bool flag;
  EXPECT_DIF_BADARG(dif_csrng_lock(nullptr));
  EXPECT_DIF_BADARG(dif_csrng_is_locked(nullptr, &flag));
  EXPECT_DIF_BADARG(dif_csrng_is_locked(&csrng_, nullptr));
}

TEST_F(LockTest, Lock) {
  EXPECT_WRITE32(CSRNG_REGWEN_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_lock(&csrng_));
}

TEST_F(LockTest, IsLocked) {
  bool flag;

  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 1);
  EXPECT_DIF_OK(dif_csrng_is_locked(&csrng_, &flag));
  EXPECT_FALSE(flag);

  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_is_locked(&csrng_, &flag));
  EXPECT_TRUE(flag);
}

class StopTest : public DifCsrngTest {};

TEST_F(StopTest, BadArgs) { EXPECT_DIF_BADARG(dif_csrng_stop(nullptr)); }

TEST_F(StopTest, Stop) {
  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(CSRNG_CTRL_REG_OFFSET, CSRNG_CTRL_REG_RESVAL);
  EXPECT_DIF_OK(dif_csrng_stop(&csrng_));
}

TEST_F(StopTest, Locked) {
  EXPECT_READ32(CSRNG_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_csrng_stop(&csrng_), kDifLocked);
}

class AlertTest : public DifCsrngTest {};

TEST_F(AlertTest, BadArgs) {
  uint32_t out;
  EXPECT_DIF_BADARG(dif_csrng_get_recoverable_alerts(nullptr, &out));
  EXPECT_DIF_BADARG(dif_csrng_get_recoverable_alerts(&csrng_, nullptr));
  EXPECT_DIF_BADARG(dif_csrng_clear_recoverable_alerts(nullptr));
}

TEST_F(AlertTest, Get) {
  uint32_t out;
  EXPECT_READ32(CSRNG_RECOV_ALERT_STS_REG_OFFSET,
                {
                    {CSRNG_RECOV_ALERT_STS_ENABLE_FIELD_ALERT_BIT, true},
                    {CSRNG_RECOV_ALERT_STS_CS_BUS_CMP_ALERT_BIT, true},
                });
  EXPECT_DIF_OK(dif_csrng_get_recoverable_alerts(&csrng_, &out));
  EXPECT_EQ(out, kDifCsrngRecoverableAlertBadEnable |
                     kDifCsrngRecoverableAlertRepeatedGenBits);
}

TEST_F(AlertTest, Clear) {
  EXPECT_WRITE32(CSRNG_RECOV_ALERT_STS_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_csrng_clear_recoverable_alerts(&csrng_));
}

}  // namespace
}  // namespace dif_csrng_unittest
