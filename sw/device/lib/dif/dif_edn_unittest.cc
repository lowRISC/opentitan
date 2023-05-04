// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_edn.h"

#include <array>
#include <vector>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "edn_regs.h"  // Generated

namespace dif_edn_unittest {
namespace {

using ::testing::ElementsAreArray;

class DifEdnTest : public testing::Test, public mock_mmio::MmioTest {
 protected:
  const dif_edn_t edn_ = {.base_addr = dev().region()};
};

class ConfigTest : public DifEdnTest {};

TEST_F(ConfigTest, BadArgs) { EXPECT_DIF_BADARG(dif_edn_configure(nullptr)); }

TEST_F(ConfigTest, ConfigOk) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 1);
  EXPECT_MASK32(EDN_CTRL_REG_OFFSET,
                {
                    {EDN_CTRL_EDN_ENABLE_OFFSET, 0xf, kMultiBitBool4True},
                });
  EXPECT_DIF_OK(dif_edn_configure(&edn_));
}

TEST_F(ConfigTest, Locked) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_edn_configure(&edn_), kDifLocked);
}

class LockTest : public DifEdnTest {};

TEST_F(LockTest, BadArgs) {
  bool flag;
  EXPECT_DIF_BADARG(dif_edn_lock(nullptr));
  EXPECT_DIF_BADARG(dif_edn_is_locked(nullptr, &flag));
  EXPECT_DIF_BADARG(dif_edn_is_locked(&edn_, nullptr));
}

TEST_F(LockTest, Lock) {
  EXPECT_WRITE32(EDN_REGWEN_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_edn_lock(&edn_));
}

TEST_F(LockTest, IsLocked) {
  bool flag;

  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 1);
  EXPECT_DIF_OK(dif_edn_is_locked(&edn_, &flag));
  EXPECT_FALSE(flag);

  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_edn_is_locked(&edn_, &flag));
  EXPECT_TRUE(flag);
}

class SetModeTest : public DifEdnTest {};

TEST_F(SetModeTest, BadArgs) {
  EXPECT_DIF_BADARG(dif_edn_set_boot_mode(nullptr));
  EXPECT_DIF_BADARG(dif_edn_set_auto_mode(nullptr, {}));
}

TEST_F(SetModeTest, Boot) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 1);
  EXPECT_MASK32(EDN_CTRL_REG_OFFSET,
                {
                    {EDN_CTRL_BOOT_REQ_MODE_OFFSET, 0xf, kMultiBitBool4True},
                });
  EXPECT_DIF_OK(dif_edn_set_boot_mode(&edn_));
}

TEST_F(SetModeTest, Auto) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 1);

  EXPECT_READ32(EDN_CTRL_REG_OFFSET, EDN_CTRL_REG_RESVAL);
  EXPECT_WRITE32(EDN_CTRL_REG_OFFSET,
                 {
                     {EDN_CTRL_EDN_ENABLE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_BOOT_REQ_MODE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_AUTO_REQ_MODE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_CMD_FIFO_RST_OFFSET, kMultiBitBool4False},
                 });
  EXPECT_WRITE32(EDN_CTRL_REG_OFFSET,
                 {
                     {EDN_CTRL_EDN_ENABLE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_BOOT_REQ_MODE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_AUTO_REQ_MODE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_CMD_FIFO_RST_OFFSET, kMultiBitBool4True},
                 });
  EXPECT_WRITE32(EDN_CTRL_REG_OFFSET,
                 {
                     {EDN_CTRL_EDN_ENABLE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_BOOT_REQ_MODE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_AUTO_REQ_MODE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_CMD_FIFO_RST_OFFSET, kMultiBitBool4False},
                 });

  dif_edn_auto_params_t params = {
      .instantiate_cmd = {.cmd = 1 | kMultiBitBool4False << 8,
                          .seed_material =
                              {
                                  .len = 3,
                                  .data = {1, 2, 3},
                              }},
      .reseed_cmd = {.cmd = 11,
                     .seed_material =
                         {
                             .len = 4,
                             .data = {4, 5, 6, 7},
                         }},
      .generate_cmd = {.cmd = 12,
                       .seed_material =
                           {
                               .len = 5,
                               .data = {8, 9, 10, 11, 12},
                           }},
      .reseed_interval = 42,
  };

  EXPECT_WRITE32(EDN_RESEED_CMD_REG_OFFSET, params.reseed_cmd.cmd);
  for (size_t i = 0; i < params.reseed_cmd.seed_material.len; ++i) {
    EXPECT_WRITE32(EDN_RESEED_CMD_REG_OFFSET,
                   params.reseed_cmd.seed_material.data[i]);
  }
  EXPECT_WRITE32(EDN_GENERATE_CMD_REG_OFFSET, params.generate_cmd.cmd);
  for (size_t i = 0; i < params.generate_cmd.seed_material.len; ++i) {
    EXPECT_WRITE32(EDN_GENERATE_CMD_REG_OFFSET,
                   params.generate_cmd.seed_material.data[i]);
  }
  EXPECT_WRITE32(EDN_MAX_NUM_REQS_BETWEEN_RESEEDS_REG_OFFSET,
                 params.reseed_interval);

  EXPECT_WRITE32(EDN_CTRL_REG_OFFSET,
                 {
                     {EDN_CTRL_EDN_ENABLE_OFFSET, kMultiBitBool4True},
                     {EDN_CTRL_BOOT_REQ_MODE_OFFSET, kMultiBitBool4False},
                     {EDN_CTRL_AUTO_REQ_MODE_OFFSET, kMultiBitBool4True},
                     {EDN_CTRL_CMD_FIFO_RST_OFFSET, kMultiBitBool4False},
                 });

  EXPECT_READ32(EDN_SW_CMD_STS_REG_OFFSET, 1);

  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 1 | params.instantiate_cmd.seed_material.len << 4 |
                     kMultiBitBool4False << 8);
  for (size_t i = 0; i < params.instantiate_cmd.seed_material.len; ++i) {
    EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                   params.instantiate_cmd.seed_material.data[i]);
  }

  EXPECT_READ32(EDN_SW_CMD_STS_REG_OFFSET, 1);

  EXPECT_READ32(EDN_SW_CMD_STS_REG_OFFSET, 1);

  EXPECT_DIF_OK(dif_edn_set_auto_mode(&edn_, params));
}

TEST_F(SetModeTest, Locked) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 0);
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_edn_set_boot_mode(&edn_), kDifLocked);
  EXPECT_EQ(dif_edn_set_auto_mode(&edn_, {}), kDifLocked);
}

class GetStatusTest : public DifEdnTest {};

TEST_F(GetStatusTest, BadArgs) {
  bool flag;
  EXPECT_DIF_BADARG(dif_edn_get_status(nullptr, kDifEdnStatusReady, &flag));
  EXPECT_DIF_BADARG(
      dif_edn_get_status(&edn_, static_cast<dif_edn_status_t>(-1), &flag));
  EXPECT_DIF_BADARG(dif_edn_get_status(&edn_, kDifEdnStatusReady, nullptr));
}

TEST_F(GetStatusTest, Ok) {
  bool flag;

  EXPECT_READ32(EDN_SW_CMD_STS_REG_OFFSET,
                {
                    {EDN_SW_CMD_STS_CMD_RDY_BIT, true},
                    {EDN_SW_CMD_STS_CMD_STS_BIT, false},
                });
  EXPECT_DIF_OK(dif_edn_get_status(&edn_, kDifEdnStatusReady, &flag));
  EXPECT_TRUE(flag);

  EXPECT_READ32(EDN_SW_CMD_STS_REG_OFFSET,
                {
                    {EDN_SW_CMD_STS_CMD_RDY_BIT, true},
                    {EDN_SW_CMD_STS_CMD_STS_BIT, false},
                });
  EXPECT_DIF_OK(dif_edn_get_status(&edn_, kDifEdnStatusCsrngAck, &flag));
  EXPECT_FALSE(flag);
}

class ErrorTest : public DifEdnTest {};

TEST_F(ErrorTest, BadArgs) {
  uint32_t set;
  EXPECT_DIF_BADARG(dif_edn_get_errors(nullptr, &set, &set));
  EXPECT_DIF_BADARG(dif_edn_get_errors(&edn_, nullptr, &set));
  EXPECT_DIF_BADARG(dif_edn_get_errors(&edn_, &set, nullptr));
  EXPECT_DIF_BADARG(dif_edn_get_cmd_unhealthy_fifo_force(
      &edn_, static_cast<dif_edn_fifo_t>(-1)));
  EXPECT_DIF_BADARG(
      dif_edn_get_cmd_unhealthy_fifo_force(nullptr, kDifEdnFifoReseedCmd));
  EXPECT_DIF_BADARG(
      dif_edn_get_cmd_error_force(&edn_, static_cast<dif_edn_error_t>(-1)));
  EXPECT_DIF_BADARG(dif_edn_get_cmd_error_force(nullptr, kDifEdnErrorMainSm));
}

TEST_F(ErrorTest, Ok) {
  EXPECT_READ32(EDN_ERR_CODE_REG_OFFSET,
                {
                    {EDN_ERR_CODE_SFIFO_RESCMD_ERR_BIT, true},
                    {EDN_ERR_CODE_EDN_MAIN_SM_ERR_BIT, true},
                    {EDN_ERR_CODE_FIFO_STATE_ERR_BIT, true},
                });

  uint32_t fifos, errors;
  EXPECT_DIF_OK(dif_edn_get_errors(&edn_, &fifos, &errors));
  EXPECT_EQ(fifos, 1 << kDifEdnFifoReseedCmd);
  EXPECT_EQ(errors,
            1 << kDifEdnErrorMainSm | 1 << kDifEdnErrorFifoFullAndEmpty);
}

TEST_F(ErrorTest, ForceFifo) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(EDN_ERR_CODE_TEST_REG_OFFSET,
                 EDN_ERR_CODE_SFIFO_RESCMD_ERR_BIT);
  EXPECT_DIF_OK(
      dif_edn_get_cmd_unhealthy_fifo_force(&edn_, kDifEdnFifoReseedCmd));
}

TEST_F(ErrorTest, ForceError) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 1);
  EXPECT_WRITE32(EDN_ERR_CODE_TEST_REG_OFFSET,
                 EDN_ERR_CODE_EDN_MAIN_SM_ERR_BIT);
  EXPECT_DIF_OK(dif_edn_get_cmd_error_force(&edn_, kDifEdnErrorMainSm));
}

TEST_F(ErrorTest, Locked) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 0);
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_edn_get_cmd_unhealthy_fifo_force(&edn_, kDifEdnFifoReseedCmd),
            kDifLocked);
  EXPECT_EQ(dif_edn_get_cmd_error_force(&edn_, kDifEdnErrorMainSm), kDifLocked);
}

class MiscStatusTest : public DifEdnTest {};

TEST_F(MiscStatusTest, BadArgs) {
  uint32_t out;
  EXPECT_DIF_BADARG(dif_edn_get_main_state_machine(nullptr, &out));
  EXPECT_DIF_BADARG(dif_edn_get_main_state_machine(&edn_, nullptr));
}

TEST_F(MiscStatusTest, GetMainSm) {
  EXPECT_READ32(EDN_MAIN_SM_STATE_REG_OFFSET, 42);

  uint32_t out;
  EXPECT_DIF_OK(dif_edn_get_main_state_machine(&edn_, &out));
  EXPECT_EQ(out, 42);
}

/**
 * DRBG commands are tested using this test group as the underlying
 * command interface is shared across API functions.
 */
class CommandTest : public DifEdnTest {
 protected:
  dif_edn_seed_material_t seed_material_{};
};

TEST_F(CommandTest, InstantiateOk) {
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00000001 | kMultiBitBool4True << 8);
  EXPECT_DIF_OK(dif_edn_instantiate(&edn_, kDifEdnEntropySrcToggleDisable,
                                    &seed_material_));

  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00000001 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_edn_instantiate(&edn_, kDifEdnEntropySrcToggleEnable,
                                    &seed_material_));

  seed_material_.data[0] = 0x5a5a5a5a;
  seed_material_.len = 1;
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00000011 | kMultiBitBool4False << 8);
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_DIF_OK(dif_edn_instantiate(&edn_, kDifEdnEntropySrcToggleEnable,
                                    &seed_material_));
}

TEST_F(CommandTest, InstantiateBadArgs) {
  EXPECT_DIF_BADARG(dif_edn_instantiate(nullptr, kDifEdnEntropySrcToggleDisable,
                                        &seed_material_));

  // Unaligned `seed_material` pointer.
  dif_edn_seed_material_t *corrupt_seed_material_ptr =
      reinterpret_cast<dif_edn_seed_material_t *>(
          reinterpret_cast<uintptr_t>(&seed_material_) + 3);
  EXPECT_DIF_BADARG(dif_edn_instantiate(&edn_, kDifEdnEntropySrcToggleDisable,
                                        corrupt_seed_material_ptr));

  // Failed overflow check.
  seed_material_.len = 16;
  EXPECT_DIF_BADARG(dif_edn_instantiate(&edn_, kDifEdnEntropySrcToggleDisable,
                                        &seed_material_));
}

TEST_F(CommandTest, ReseedOk) {
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00000002 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_edn_reseed(&edn_, &seed_material_));

  seed_material_.data[0] = 0x5a5a5a5a;
  seed_material_.len = 1;
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00000012 | kMultiBitBool4False << 8);
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_DIF_OK(dif_edn_reseed(&edn_, &seed_material_));
}

TEST_F(CommandTest, ReseedBadArgs) {
  EXPECT_DIF_BADARG(dif_edn_reseed(nullptr, &seed_material_));

  // Failed overflow check.
  seed_material_.len = 16;
  EXPECT_DIF_BADARG(dif_edn_reseed(&edn_, &seed_material_));
}

TEST_F(CommandTest, UpdateOk) {
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00000004 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_edn_update(&edn_, &seed_material_));
  seed_material_.data[0] = 0x5a5a5a5a;
  seed_material_.len = 1;
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00000014 | kMultiBitBool4False << 8);
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET, 0x5a5a5a5a);
  EXPECT_DIF_OK(dif_edn_update(&edn_, &seed_material_));
}

TEST_F(CommandTest, UpdateBadArgs) {
  EXPECT_DIF_BADARG(dif_edn_update(nullptr, &seed_material_));
}

TEST_F(CommandTest, GenerateOk) {
  // 512bits = 16 x 32bit = 4 x 128bit blocks
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00004003 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_edn_generate_start(&edn_, /*len=*/16));

  // 576bits = 18 x 32bit = 5 x 128bit blocks (rounded up)
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00005003 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_edn_generate_start(&edn_, /*len=*/18));
}

TEST_F(CommandTest, GenerateBadArgs) {
  EXPECT_DIF_BADARG(dif_edn_generate_start(nullptr, /*len=*/1));
  EXPECT_DIF_BADARG(dif_edn_generate_start(&edn_, /*len=*/0));
}

TEST_F(CommandTest, GenerateOutOfRange) {
  enum {
    // The maximum allowed is 0x800 128-bit blocks. Multiply by 4 to get the
    // number of uint32 words and add one to trigger the error.
    kGenerateLenOutOfRange = 0x800 * 4 + 1,
  };
  EXPECT_DIF_OUTOFRANGE(dif_edn_generate_start(&edn_, kGenerateLenOutOfRange));
}

TEST_F(CommandTest, UninstantiateOk) {
  EXPECT_WRITE32(EDN_SW_CMD_REQ_REG_OFFSET,
                 0x00000005 | kMultiBitBool4False << 8);
  EXPECT_DIF_OK(dif_edn_uninstantiate(&edn_));
}

class StopTest : public DifEdnTest {};

TEST_F(StopTest, BadArgs) { EXPECT_DIF_BADARG(dif_edn_stop(nullptr)); }

TEST_F(StopTest, Stop) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 1);
  EXPECT_READ32(EDN_CTRL_REG_OFFSET, 0x3);
  uint32_t ctrl_reg = bitfield_field32_write(0x3, EDN_CTRL_CMD_FIFO_RST_FIELD,
                                             kMultiBitBool4True);
  EXPECT_WRITE32(EDN_CTRL_REG_OFFSET, ctrl_reg);
  EXPECT_WRITE32(EDN_CTRL_REG_OFFSET, EDN_CTRL_REG_RESVAL);
  EXPECT_DIF_OK(dif_edn_stop(&edn_));
}

TEST_F(StopTest, Locked) {
  EXPECT_READ32(EDN_REGWEN_REG_OFFSET, 0);
  EXPECT_EQ(dif_edn_stop(&edn_), kDifLocked);
}

class AlertTest : public DifEdnTest {};

TEST_F(AlertTest, BadArgs) {
  uint32_t out;
  EXPECT_DIF_BADARG(dif_edn_get_recoverable_alerts(nullptr, &out));
  EXPECT_DIF_BADARG(dif_edn_get_recoverable_alerts(&edn_, nullptr));
  EXPECT_DIF_BADARG(dif_edn_clear_recoverable_alerts(nullptr));
}

TEST_F(AlertTest, Get) {
  uint32_t out;
  EXPECT_READ32(EDN_RECOV_ALERT_STS_REG_OFFSET,
                {
                    {EDN_RECOV_ALERT_STS_BOOT_REQ_MODE_FIELD_ALERT_BIT, true},
                    {EDN_RECOV_ALERT_STS_EDN_BUS_CMP_ALERT_BIT, true},
                });
  EXPECT_DIF_OK(dif_edn_get_recoverable_alerts(&edn_, &out));
  EXPECT_EQ(out, 1 << kDifEdnRecoverableAlertBadBootReqMode |
                     1 << kDifEdnRecoverableAlertRepeatedGenBits);
}

TEST_F(AlertTest, Clear) {
  EXPECT_WRITE32(EDN_RECOV_ALERT_STS_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_edn_clear_recoverable_alerts(&edn_));
}

}  // namespace
}  // namespace dif_edn_unittest
