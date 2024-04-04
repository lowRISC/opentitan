// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/ast.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"

#include "ast_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "sensor_ctrl_regs.h"

#ifndef OT_PLATFORM_RV32
// Provide a definition for off-target unit tests.
const uint32_t kAstCheckPollCpuCycles = 10000;
#endif

enum {
  kBaseSensorCtrl = TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR,
  kBaseAst = TOP_EARLGREY_AST_BASE_ADDR,

  /**
   * AST Calibration Data Size - Bank 0, Page 0
   *
   * Number of AST calibration words that will be stored in flash / OTP.
   *
   * Must match `kFlashInfoAstCalibrationDataSizeIn32BitWords` in
   * //sw/device/silicon_creator/manuf/lib/flash_info_fields.h.
   */
  kAstCalibrationDataSizeIn32BitWords =
      (AST_REGAL_REG_OFFSET + sizeof(uint32_t)) / sizeof(uint32_t),

  /**
   * The starting offset of the AST calibration data within the
   * `kFlashCtrlInfoPageFactoryId` info flash page.
   *
   * Must be compatible to the `kFlashInfoFieldAstCalibrationData` byte offset
   * in //sw/device/silicon_creator/manuf/lib/flash_info_fields.c.
   */
  kAstCalibrationDataInfoFlashByteOffset =
      OTP_CTRL_PARAM_DEVICE_ID_SIZE + OTP_CTRL_PARAM_MANUF_STATE_SIZE,
};

rom_error_t ast_check(lifecycle_state_t lc_state) {
  // In some lifecycle states we want to continue the boot process even if the
  // AST is not initialized. Note that in these states OTP may not have been
  // configured.
  switch (launder32(lc_state)) {
    case kLcStateTest:
      HARDENED_CHECK_EQ(lc_state, kLcStateTest);
      return kErrorOk;
    case kLcStateRma:
      HARDENED_CHECK_EQ(lc_state, kLcStateRma);
      return kErrorOk;
    case kLcStateDev:
      HARDENED_CHECK_EQ(lc_state, kLcStateDev);
      break;
    case kLcStateProd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProd);
      break;
    case kLcStateProdEnd:
      HARDENED_CHECK_EQ(lc_state, kLcStateProdEnd);
      break;
    default:
      HARDENED_TRAP();
  }

  // OTP can be configured to skip AST initialization. In this situation we do
  // not check that AST_INIT_DONE is set.
  uint32_t en = otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_AST_INIT_EN_OFFSET);
  if (launder32(en) == kMultiBitBool4False) {
    HARDENED_CHECK_EQ(en, kMultiBitBool4False);
    return kErrorOk;
  }

  // AST initialization may take up to 100us. It is most likely already complete
  // at this point but for resilience poll for up to 100us.
  uint32_t mcycle;
  rom_error_t res = kErrorAstInitNotDone;
  CSR_WRITE(CSR_REG_MCYCLE, 0);
  do {
    CSR_READ(CSR_REG_MCYCLE, &mcycle);
    hardened_bool_t init_done = ast_init_done();
    if (init_done != kHardenedBoolFalse) {
      static_assert(kErrorOk == (rom_error_t)kHardenedBoolTrue,
                    "kErrorOk must be equal to kHardenedBoolTrue");
      res = (rom_error_t)init_done;
      break;
    }
  } while (mcycle < kAstCheckPollCpuCycles);

  return res;
}

OT_WARN_UNUSED_RESULT
static bool done_bit_get(void) {
  uint32_t reg =
      abs_mmio_read32(kBaseSensorCtrl + SENSOR_CTRL_STATUS_REG_OFFSET);
  return bitfield_bit32_read(reg, SENSOR_CTRL_STATUS_AST_INIT_DONE_BIT);
}

hardened_bool_t ast_init_done(void) {
  static_assert(kHardenedBoolTrue == 0x739,
                "This function expects kHardenedBoolTrue to be 0x739");

  // The code below reads the AST_INIT_DONE bit twice and modifies `res` with
  // the result of each attempt. `res` should be `kHardenedBoolTrue` if all
  // attempts return true.
  hardened_bool_t res = 0x631;
  res |= (hardened_bool_t)done_bit_get() << 3;
  res |= (hardened_bool_t)done_bit_get() << 8;

  if (res != kHardenedBoolTrue) {
    return kHardenedBoolFalse;
  }
  return res;
}

/**
 * Loads AST patch from kFlashCtrlInfoPageFactoryId page.
 *
 * The `ast_data` offset must be equivalent to the one used in
 * //sw/device/silicon_creator/manuf/lib/ast_program.c.
 *
 * The info flash configuration must also be the same used to program the page,
 * otherwise the data read will be garbled.
 *
 * @param[out] ast_data Pointer to the buffer used to store the data read.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t load_ast_config_from_flash(uint32_t *ast_data) {
  flash_ctrl_info_perms_set(&kFlashCtrlInfoPageFactoryId,
                            (flash_ctrl_perms_t){
                                .read = kMultiBitBool4True,
                                .write = kMultiBitBool4False,
                                .erase = kMultiBitBool4False,
                            });
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageFactoryId,
                          (flash_ctrl_cfg_t){
                              .scrambling = kMultiBitBool4False,
                              .ecc = kMultiBitBool4True,
                              .he = kMultiBitBool4False,
                          });
  return flash_ctrl_info_read(&kFlashCtrlInfoPageFactoryId,
                              kAstCalibrationDataInfoFlashByteOffset,
                              kAstCalibrationDataSizeIn32BitWords, ast_data);
}

rom_error_t ast_patch(lifecycle_state_t lc_state) {
  uint32_t ast_data[kAstCalibrationDataSizeIn32BitWords];
  HARDENED_RETURN_IF_ERROR(load_ast_config_from_flash(ast_data));

  // Skip patching logic if either of the first two words don't seem to be
  // configured.
  if (ast_data[0] == 0 || ast_data[0] == UINT32_MAX) {
    return ast_check(lc_state);
  }

  if (ast_data[1] == 0 || ast_data[1] == UINT32_MAX) {
    return ast_check(lc_state);
  }

  for (size_t i = 0; i < kAstCalibrationDataSizeIn32BitWords; ++i) {
    abs_mmio_write32(kBaseAst + i * sizeof(uint32_t), ast_data[i]);
  }

  return ast_check(lc_state);
}
