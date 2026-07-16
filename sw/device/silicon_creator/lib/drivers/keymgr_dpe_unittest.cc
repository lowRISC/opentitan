// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top/dt/keymgr_dpe.h"

#include <array>
#include <limits>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mock_abs_mmio.h"
#include "sw/device/silicon_creator/lib/base/mock_sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr_dpe.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top/keymgr_dpe_regs.h"  // Generated.

namespace keymgr_dpe_unittest {
namespace {

// TODO(#30609): extend this unittest

class KeymgrDpeTest : public rom_test::RomTest {
 protected:
  /**
   * Expects a read of the OP_STATUS register followed by the write that
   * clears the status by writing back the read value.
   */
  void ExpectOpStatusReadClear(uint32_t op_status) {
    EXPECT_ABS_READ32(base_ + KEYMGR_DPE_OP_STATUS_REG_OFFSET, op_status);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_OP_STATUS_REG_OFFSET, op_status);
  }

  /**
   * Expects a read-and-clear of the ERR_CODE register.
   */
  void ExpectErrCodeReadClear(uint32_t err_code) {
    EXPECT_ABS_READ32(base_ + KEYMGR_DPE_ERR_CODE_REG_OFFSET, err_code);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_ERR_CODE_REG_OFFSET, err_code);
  }

  /**
   * Expects a full `expected_state_check()` sequence with a single,
   * non-polling OP_STATUS read.
   */
  void ExpectStatusCheck(uint32_t op_status, uint32_t km_state,
                         uint32_t err_code) {
    ExpectOpStatusReadClear(op_status);
    ExpectErrCodeReadClear(err_code);
    EXPECT_ABS_READ32(base_ + KEYMGR_DPE_WORKING_STATE_REG_OFFSET, km_state);
  }

  /**
   * Expects a single OP_STATUS read as performed by `keymgr_dpe_is_idle()`.
   */
  void ExpectIdleCheck(uint32_t op_status) {
    EXPECT_ABS_READ32(base_ + KEYMGR_DPE_OP_STATUS_REG_OFFSET, op_status);
  }

  /**
   * Expects a write to the CONTROL_SHADOWED register.
   */
  void ExpectControlRegSet(bool sw_binding_only, uint32_t ops, uint32_t dest,
                           uint32_t src_slot, uint32_t dst_slot) {
    EXPECT_ABS_WRITE32_SHADOWED(
        base_ + KEYMGR_DPE_CONTROL_SHADOWED_REG_OFFSET,
        {
            {KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_OFFSET, ops},
            {KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_OFFSET, dest},
            {KEYMGR_DPE_CONTROL_SHADOWED_SLOT_SRC_SEL_OFFSET, src_slot},
            {KEYMGR_DPE_CONTROL_SHADOWED_SLOT_DST_SEL_OFFSET, dst_slot},
            {KEYMGR_DPE_CONTROL_SHADOWED_SW_BINDING_ONLY_BIT, sw_binding_only},
        });
  }

  /**
   * Expects a write to the START register.
   */
  void ExpectStartOperation(void) {
    EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_START_REG_OFFSET,
                       {
                           {KEYMGR_DPE_START_EN_BIT, true},
                       });
  }

  /**
   * Expects a `sc_keymgr_dpe_wait_until_done()` polling sequence that reads
   * `busy_cycles` WIP statuses before the final `end_status`.
   */
  void ExpectWaitUntilDone(size_t busy_cycles, uint32_t end_status) {
    for (size_t i = 0; i < busy_cycles; i++) {
      ExpectOpStatusReadClear(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_WIP);
    }
    ExpectOpStatusReadClear(end_status);
  }

  /**
   * Expects a `sc_keymgr_dpe_max_ver_set()` sequence.
   */
  void ExpectMaxVerSet(uint32_t max_key_ver) {
    EXPECT_SEC_WRITE32_SHADOWED(
        base_ + KEYMGR_DPE_MAX_KEY_VER_SHADOWED_REG_OFFSET, max_key_ver);
    EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_MAX_KEY_VER_REGWEN_REG_OFFSET, 0);
  }

  /**
   * Expects a `sc_keymgr_dpe_sw_binding_set()` sequence.
   */
  void ExpectSwBindingSet(const keymgr_dpe_binding_value_t *binding_value) {
    for (size_t i = 0; i < ARRAYSIZE(binding_value->data); ++i) {
      EXPECT_SEC_WRITE32(
          base_ + KEYMGR_DPE_SW_BINDING_0_REG_OFFSET + i * sizeof(uint32_t),
          binding_value->data[i]);
    }
    EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_SW_BINDING_REGWEN_REG_OFFSET, 0);
  }

  /**
   * Expects a `sc_keymgr_dpe_policy_set()` sequence.
   */
  void ExpectPolicySet(sc_keymgr_dpe_policies_t policy) {
    EXPECT_SEC_WRITE32(
        base_ + KEYMGR_DPE_SLOT_POLICY_REG_OFFSET,
        {
            {KEYMGR_DPE_SLOT_POLICY_ALLOW_CHILD_BIT, policy.child},
            {KEYMGR_DPE_SLOT_POLICY_EXPORTABLE_BIT, policy.expo},
            {KEYMGR_DPE_SLOT_POLICY_RETAIN_PARENT_BIT, policy.parent},
        });
    EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_SLOT_POLICY_REGWEN_REG_OFFSET, 0);
  }

  /**
   * Expects a full `sc_keymgr_dpe_advance_wrapper()` sequence up to and
   * including the start of the operation.
   */
  void ExpectAdvanceWrapper(bool sw_binding_only,
                            const sc_keymgr_dpe_advance_data_t &adv_data) {
    ExpectMaxVerSet(adv_data.version);
    ExpectSwBindingSet(adv_data.binding_value);
    ExpectPolicySet(adv_data.policy);
    ExpectControlRegSet(sw_binding_only,
                        KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE,
                        KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE,
                        adv_data.sel_src_slot, adv_data.sel_dst_slot);
    ExpectStartOperation();
  }

  /**
   * Expects a `sc_keymgr_dpe_load_uds()` sequence.
   */
  void ExpectLoadUds(uint32_t dst_slot) {
    ExpectControlRegSet(
        /*sw_binding_only=*/false,
        KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_LOAD_ROOT_KEY,
        KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE, /*src_slot=*/0,
        dst_slot);
    ExpectStartOperation();
    ExpectWaitUntilDone(/*busy_cycles=*/1,
                        KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  }

  uint32_t base_ =
      dt_keymgr_dpe_reg_block(kDtKeymgrDpe, kDtKeymgrDpeRegBlockCore);
  keymgr_dpe_binding_value_t binding_value_sealing_ = {
      {0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07}};
  keymgr_dpe_binding_value_t binding_value_attestation_ = {
      {0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f}};
  sc_keymgr_dpe_policies_t policy_erase_parent_ = {
      .parent = kScKeymgrDPESlotPolEraseParent,
      .child = kScKeymgrDPESlotPolAllowChild,
      .expo = kScKeymgrDPESlotPolNoExport,
  };
  sc_keymgr_dpe_diversification_t diversification_ = {
      .salt = {0xf0f1f2f3, 0xf4f5f6f7, 0xf8f9fafb, 0xfcfdfeff, 0xd0d1d2d3,
               0xd4d5d6d7, 0xd8d9dadb, 0xdcdddedf},
      .sel_src_slot = 2,
      .version = 0xA5A5A5A4,
  };
  rom_test::MockAbsMmio mmio_;
  rom_test::MockSecMmio sec_mmio_;
};

TEST_F(KeymgrDpeTest, EntropyReseedIntervalSet) {
  EXPECT_SEC_WRITE32_SHADOWED(
      base_ + KEYMGR_DPE_RESEED_INTERVAL_SHADOWED_REG_OFFSET, 0x1234u);
  sc_keymgr_dpe_entropy_reseed_interval_set(0x1234u);
}

TEST_F(KeymgrDpeTest, SwBindingValueSet) {
  ExpectSwBindingSet(&binding_value_sealing_);
  sc_keymgr_dpe_sw_binding_set(&binding_value_sealing_);
}

TEST_F(KeymgrDpeTest, SwBindingUnlockWait) {
  // The function polls until the REGWEN register reads non-zero and then
  // reads it once more through sec_mmio to update the expectations table.
  EXPECT_ABS_READ32(base_ + KEYMGR_DPE_SW_BINDING_REGWEN_REG_OFFSET, 0);
  EXPECT_ABS_READ32(base_ + KEYMGR_DPE_SW_BINDING_REGWEN_REG_OFFSET, 1);
  EXPECT_SEC_READ32(base_ + KEYMGR_DPE_SW_BINDING_REGWEN_REG_OFFSET, 1);
  sc_keymgr_dpe_sw_binding_unlock_wait();
}

TEST_F(KeymgrDpeTest, MaxVerSet) {
  ExpectMaxVerSet(0xA5A5A5A5);
  sc_keymgr_dpe_max_ver_set(0xA5A5A5A5);
}

TEST_F(KeymgrDpeTest, KeyVerSet) {
  EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_KEY_VERSION_REG_OFFSET, 0x5A5A5A5A);
  sc_keymgr_dpe_key_ver_set(0x5A5A5A5A);
}

TEST_F(KeymgrDpeTest, PolicySet) {
  sc_keymgr_dpe_policies_t policy = {
      .parent = kScKeymgrDPESlotPolRetainParent,
      .child = kScKeymgrDPESlotPolAllowChild,
      .expo = kScKeymgrDPESlotPolNoExport,
  };
  ExpectPolicySet(policy);
  sc_keymgr_dpe_policy_set(policy);
}

TEST_F(KeymgrDpeTest, ControlRegSet_1) {
  ExpectControlRegSet(/*sw_binding_only=*/true,
                      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE,
                      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_OTBN,
                      /*src_slot=*/1, /*dst_slot=*/2);
  sc_keymgr_dpe_control_reg_set(
      kScKeymgrDPEUseExclusiveSwBinding,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE, kScKeymgrDPEDestOtbn,
      /*sel_src_slot=*/1, /*sel_dst_slot=*/2);
}

TEST_F(KeymgrDpeTest, ControlRegSet_2) {
  ExpectControlRegSet(/*sw_binding_only=*/false,
                      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE,
                      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE,
                      /*src_slot=*/0, /*dst_slot=*/3);
  sc_keymgr_dpe_control_reg_set(
      kScKeymgrDPEUseAdditionalHwBinding,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE, kScKeymgrDPEDestNone,
      /*sel_src_slot=*/0, /*sel_dst_slot=*/3);
}

TEST_F(KeymgrDpeTest, StartOperation) {
  ExpectStartOperation();
  sc_keymgr_dpe_start_operation();
}

TEST_F(KeymgrDpeTest, WaitUntilDoneSuccess) {
  ExpectWaitUntilDone(/*busy_cycles=*/2,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  EXPECT_EQ(sc_keymgr_dpe_wait_until_done(), kErrorOk);
}

TEST_F(KeymgrDpeTest, WaitUntilDoneError) {
  ExpectWaitUntilDone(/*busy_cycles=*/1,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_ERROR);
  // On error the ERR_CODE register is read and cleared.
  ExpectErrCodeReadClear(1 << KEYMGR_DPE_ERR_CODE_INVALID_OP_BIT);
  EXPECT_EQ(sc_keymgr_dpe_wait_until_done(), kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, CheckState) {
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  EXPECT_EQ(sc_keymgr_dpe_state_check(kScKeymgrDPEStateAvailable), kErrorOk);
}

TEST_F(KeymgrDpeTest, CheckStatePolling) {
  // The status check polls while the OP_STATUS register reads either WIP or
  // DONE_SUCCESS.
  ExpectOpStatusReadClear(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_WIP);
  ExpectOpStatusReadClear(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  EXPECT_EQ(sc_keymgr_dpe_state_check(kScKeymgrDPEStateAvailable), kErrorOk);
}

TEST_F(KeymgrDpeTest, CheckStateInvalidResponse) {
  // A state mismatch is expected to fail.
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_INVALID,
                    /*err_code=*/0u);
  EXPECT_EQ(sc_keymgr_dpe_state_check(kScKeymgrDPEStateAvailable),
            kErrorKeymgrInternal);

  // Any non-idle status is expected to fail.
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_ERROR,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  EXPECT_EQ(sc_keymgr_dpe_state_check(kScKeymgrDPEStateAvailable),
            kErrorKeymgrInternal);

  // Any non-zero error code is expected to fail.
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/1u);
  EXPECT_EQ(sc_keymgr_dpe_state_check(kScKeymgrDPEStateAvailable),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, GenerateKeySwOutput) {
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_KEY_VERSION_REG_OFFSET,
                     diversification_.version);
  for (size_t i = 0; i < kScKeymgrDPESaltNumWords; ++i) {
    EXPECT_ABS_WRITE32(
        base_ + KEYMGR_DPE_SALT_0_REG_OFFSET + i * sizeof(uint32_t),
        diversification_.salt[i]);
  }
  ExpectControlRegSet(
      /*sw_binding_only=*/false,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_SW_OUTPUT,
      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE,
      diversification_.sel_src_slot, /*dst_slot=*/0);
  ExpectStartOperation();
  ExpectWaitUntilDone(/*busy_cycles=*/2,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);

  EXPECT_EQ(sc_keymgr_dpe_generate_key(kScKeymgrDPEDestNone, diversification_),
            kErrorOk);
}

TEST_F(KeymgrDpeTest, GenerateKeyOtbn) {
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_KEY_VERSION_REG_OFFSET,
                     diversification_.version);
  for (size_t i = 0; i < kScKeymgrDPESaltNumWords; ++i) {
    EXPECT_ABS_WRITE32(
        base_ + KEYMGR_DPE_SALT_0_REG_OFFSET + i * sizeof(uint32_t),
        diversification_.salt[i]);
  }
  ExpectControlRegSet(
      /*sw_binding_only=*/false,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_GENERATE_HW_OUTPUT,
      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_OTBN,
      diversification_.sel_src_slot, /*dst_slot=*/0);
  ExpectStartOperation();
  ExpectWaitUntilDone(/*busy_cycles=*/2,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);

  EXPECT_EQ(sc_keymgr_dpe_generate_key_otbn(diversification_), kErrorOk);
}

TEST_F(KeymgrDpeTest, GenerateKeyBadState) {
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_RESET,
                    /*err_code=*/0u);
  EXPECT_EQ(sc_keymgr_dpe_generate_key(kScKeymgrDPEDestOtbn, diversification_),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, ReadKeyNotIdle) {
  std::array<uint32_t, kScKeymgrDPEKeyNumWords> share0;
  std::array<uint32_t, kScKeymgrDPEKeyNumWords> share1;

  ExpectIdleCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_WIP);
  EXPECT_EQ(sc_keymgr_dpe_read_key(share0.data(), share1.data()),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, ClearKeyOtbn) {
  ExpectIdleCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE);
  EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET,
                     {
                         {KEYMGR_DPE_SIDELOAD_CLEAR_VAL_OFFSET,
                          KEYMGR_DPE_SIDELOAD_CLEAR_VAL_VALUE_OTBN},
                     });
  EXPECT_ABS_READ32(base_ + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET,
                    {
                        {KEYMGR_DPE_SIDELOAD_CLEAR_VAL_OFFSET,
                         KEYMGR_DPE_SIDELOAD_CLEAR_VAL_VALUE_OTBN},
                    });
  EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET,
                     {
                         {KEYMGR_DPE_SIDELOAD_CLEAR_VAL_OFFSET,
                          KEYMGR_DPE_SIDELOAD_CLEAR_VAL_VALUE_NONE},
                     });

  EXPECT_EQ(sc_keymgr_dpe_clear_sideload_key_otbn(), kErrorOk);
}

TEST_F(KeymgrDpeTest, ClearKeyNotIdle) {
  ExpectIdleCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_WIP);
  EXPECT_EQ(sc_keymgr_dpe_clear_key(kScKeymgrDPEDestOtbn),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, ClearKeyReadbackMismatch) {
  ExpectIdleCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE);
  EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET,
                     {
                         {KEYMGR_DPE_SIDELOAD_CLEAR_VAL_OFFSET,
                          KEYMGR_DPE_SIDELOAD_CLEAR_VAL_VALUE_OTBN},
                     });

  // Readback does not match the value written.
  EXPECT_ABS_READ32(base_ + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET,
                    {
                        {KEYMGR_DPE_SIDELOAD_CLEAR_VAL_OFFSET,
                         KEYMGR_DPE_SIDELOAD_CLEAR_VAL_VALUE_AES},
                    });

  EXPECT_EQ(sc_keymgr_dpe_clear_key(kScKeymgrDPEDestOtbn),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, AdvanceDpeContext) {
  sc_keymgr_dpe_advance_data_t adv_data = {
      .binding_value = &binding_value_sealing_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 1,
      .sel_dst_slot = 2,
      .version = 0xA5A5A5A5,
  };

  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  // Advancing a generic DPE context uses the sw binding exclusively.
  ExpectAdvanceWrapper(/*sw_binding_only=*/true, adv_data);
  EXPECT_EQ(sc_keymgr_dpe_advance_dpe_context(adv_data), kErrorOk);
}

TEST_F(KeymgrDpeTest, LockUds) {
  EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_LOAD_KEY_LOCK_REG_OFFSET,
                     {
                         {KEYMGR_DPE_LOAD_KEY_LOCK_LOCK_BIT, true},
                     });
  EXPECT_EQ(sc_keymgr_dpe_lock_uds(), kErrorOk);
}

TEST_F(KeymgrDpeTest, LoadUds) {
  ExpectLoadUds(/*dst_slot=*/1);
  EXPECT_EQ(sc_keymgr_dpe_load_uds(/*sel_dst_slot=*/1), kErrorOk);
}

TEST_F(KeymgrDpeTest, LoadUdsError) {
  ExpectControlRegSet(
      /*sw_binding_only=*/false,
      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_LOAD_ROOT_KEY,
      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE, /*src_slot=*/0,
      /*dst_slot=*/1);
  ExpectStartOperation();
  // Loading the UDS into an occupied slot or while locked reports an error.
  ExpectWaitUntilDone(/*busy_cycles=*/1,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_ERROR);
  ExpectErrCodeReadClear(1 << KEYMGR_DPE_ERR_CODE_INVALID_OP_BIT);
  EXPECT_EQ(sc_keymgr_dpe_load_uds(/*sel_dst_slot=*/1), kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, AdvanceInitial) {
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_RESET,
                    /*err_code=*/0u);
  ExpectControlRegSet(/*sw_binding_only=*/false,
                      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ADVANCE,
                      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE,
                      /*src_slot=*/0, /*dst_slot=*/1);
  ExpectStartOperation();
  ExpectWaitUntilDone(/*busy_cycles=*/2,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);

  EXPECT_EQ(sc_keymgr_dpe_advance_initial(/*sel_dst_slot_uds=*/1), kErrorOk);
}

TEST_F(KeymgrDpeTest, AdvanceInitialBadState) {
  // The initial advance call requires the keymgr_dpe to be in reset state.
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  EXPECT_EQ(sc_keymgr_dpe_advance_initial(/*sel_dst_slot_uds=*/1),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, AdvanceCreator) {
  sc_keymgr_dpe_advance_data_t adv_data_sealing = {
      .binding_value = &binding_value_sealing_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 0,
      .sel_dst_slot = 1,
      .version = 0xA5A5A5A5,
  };
  sc_keymgr_dpe_advance_data_t adv_data_attestation = {
      .binding_value = &binding_value_attestation_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 2,
      .sel_dst_slot = 3,
      .version = 0xA5A5A5A5,
  };

  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  // Advance the sealing key chain from the preloaded UDS.
  ExpectAdvanceWrapper(/*sw_binding_only=*/false, adv_data_sealing);
  ExpectWaitUntilDone(/*busy_cycles=*/1,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  // Reload the UDS into the attestation source slot.
  ExpectLoadUds(adv_data_attestation.sel_src_slot);
  // Advance the attestation key chain.
  ExpectAdvanceWrapper(/*sw_binding_only=*/false, adv_data_attestation);
  ExpectWaitUntilDone(/*busy_cycles=*/1,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);

  EXPECT_EQ(
      sc_keymgr_dpe_advance_creator(adv_data_sealing, adv_data_attestation),
      kErrorOk);
}

TEST_F(KeymgrDpeTest, AdvanceCreatorBadPolicy) {
  sc_keymgr_dpe_advance_data_t adv_data = {
      .binding_value = &binding_value_sealing_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 0,
      .sel_dst_slot = 1,
      .version = 0xA5A5A5A5,
  };
  // The creator keys must not outlive their boot stage; a retain parent
  // policy is rejected before any register access.
  sc_keymgr_dpe_advance_data_t adv_data_bad_policy = adv_data;
  adv_data_bad_policy.policy.parent = kScKeymgrDPESlotPolRetainParent;

  EXPECT_EQ(sc_keymgr_dpe_advance_creator(adv_data_bad_policy, adv_data),
            kErrorKeymgrInternal);
  EXPECT_EQ(sc_keymgr_dpe_advance_creator(adv_data, adv_data_bad_policy),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, AdvanceOwnerInt) {
  sc_keymgr_dpe_advance_data_t adv_data_sealing = {
      .binding_value = &binding_value_sealing_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 1,
      .sel_dst_slot = 1,
      .version = 0xA5A5A5A5,
  };
  sc_keymgr_dpe_advance_data_t adv_data_attestation = {
      .binding_value = &binding_value_attestation_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 3,
      .sel_dst_slot = 3,
      .version = 0xA5A5A5A5,
  };

  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  ExpectAdvanceWrapper(/*sw_binding_only=*/false, adv_data_sealing);
  ExpectWaitUntilDone(/*busy_cycles=*/1,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  ExpectAdvanceWrapper(/*sw_binding_only=*/false, adv_data_attestation);
  ExpectWaitUntilDone(/*busy_cycles=*/1,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);

  EXPECT_EQ(
      sc_keymgr_dpe_advance_owner_int(adv_data_sealing, adv_data_attestation),
      kErrorOk);
}

TEST_F(KeymgrDpeTest, AdvanceOwnerIntBadArguments) {
  sc_keymgr_dpe_advance_data_t adv_data = {
      .binding_value = &binding_value_sealing_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 1,
      .sel_dst_slot = 1,
      .version = 0xA5A5A5A5,
  };

  // The source and destination slots have to be equal.
  sc_keymgr_dpe_advance_data_t adv_data_bad_slot = adv_data;
  adv_data_bad_slot.sel_dst_slot = 2;
  EXPECT_EQ(sc_keymgr_dpe_advance_owner_int(adv_data_bad_slot, adv_data),
            kErrorKeymgrInternal);
  EXPECT_EQ(sc_keymgr_dpe_advance_owner_int(adv_data, adv_data_bad_slot),
            kErrorKeymgrInternal);

  // The retain parent policy is rejected.
  sc_keymgr_dpe_advance_data_t adv_data_bad_policy = adv_data;
  adv_data_bad_policy.policy.parent = kScKeymgrDPESlotPolRetainParent;
  EXPECT_EQ(sc_keymgr_dpe_advance_owner_int(adv_data_bad_policy, adv_data),
            kErrorKeymgrInternal);
  EXPECT_EQ(sc_keymgr_dpe_advance_owner_int(adv_data, adv_data_bad_policy),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, AdvanceOwner) {
  sc_keymgr_dpe_advance_data_t adv_data_sealing = {
      .binding_value = &binding_value_sealing_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 1,
      .sel_dst_slot = 1,
      .version = 0xA5A5A5A5,
  };
  sc_keymgr_dpe_advance_data_t adv_data_attestation = {
      .binding_value = &binding_value_attestation_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 3,
      .sel_dst_slot = 3,
      .version = 0xA5A5A5A5,
  };

  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  ExpectAdvanceWrapper(/*sw_binding_only=*/false, adv_data_sealing);
  ExpectWaitUntilDone(/*busy_cycles=*/1,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  ExpectAdvanceWrapper(/*sw_binding_only=*/false, adv_data_attestation);
  ExpectWaitUntilDone(/*busy_cycles=*/1,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);

  EXPECT_EQ(sc_keymgr_dpe_advance_owner(adv_data_sealing, adv_data_attestation),
            kErrorOk);
}

TEST_F(KeymgrDpeTest, AdvanceOwnerBadSlots) {
  sc_keymgr_dpe_advance_data_t adv_data = {
      .binding_value = &binding_value_sealing_,
      .policy = policy_erase_parent_,
      .sel_src_slot = 1,
      .sel_dst_slot = 1,
      .version = 0xA5A5A5A5,
  };

  // The source and destination slots have to be equal.
  sc_keymgr_dpe_advance_data_t adv_data_bad_slot = adv_data;
  adv_data_bad_slot.sel_dst_slot = 2;
  EXPECT_EQ(sc_keymgr_dpe_advance_owner(adv_data_bad_slot, adv_data),
            kErrorKeymgrInternal);
  EXPECT_EQ(sc_keymgr_dpe_advance_owner(adv_data, adv_data_bad_slot),
            kErrorKeymgrInternal);
}

TEST_F(KeymgrDpeTest, EraseSlot) {
  ExpectControlRegSet(/*sw_binding_only=*/false,
                      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_ERASE_SLOT,
                      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE,
                      /*src_slot=*/0, /*dst_slot=*/2);
  ExpectStartOperation();
  ExpectWaitUntilDone(/*busy_cycles=*/1,
                      KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);

  EXPECT_EQ(sc_keymgr_dpe_erase_slot(/*sel_dst_slot=*/2), kErrorOk);
}

TEST_F(KeymgrDpeTest, Disable) {
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_AVAILABLE,
                    /*err_code=*/0u);
  ExpectControlRegSet(/*sw_binding_only=*/true,
                      KEYMGR_DPE_CONTROL_SHADOWED_OPERATION_VALUE_DISABLE,
                      KEYMGR_DPE_CONTROL_SHADOWED_DEST_SEL_VALUE_NONE,
                      /*src_slot=*/0, /*dst_slot=*/0);
  ExpectStartOperation();
  // The final state check polls through the WIP and DONE_SUCCESS statuses
  // of the disable operation.
  ExpectOpStatusReadClear(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_WIP);
  ExpectOpStatusReadClear(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_DONE_SUCCESS);
  ExpectStatusCheck(KEYMGR_DPE_OP_STATUS_STATUS_VALUE_IDLE,
                    KEYMGR_DPE_WORKING_STATE_STATE_VALUE_DISABLED,
                    /*err_code=*/0u);
  // An invalid destination enables continuous clearing of all destinations.
  EXPECT_ABS_WRITE32(base_ + KEYMGR_DPE_SIDELOAD_CLEAR_REG_OFFSET,
                     std::numeric_limits<uint32_t>::max());

  EXPECT_EQ(sc_keymgr_dpe_disable(), kErrorOk);
}

}  // namespace
}  // namespace keymgr_dpe_unittest
