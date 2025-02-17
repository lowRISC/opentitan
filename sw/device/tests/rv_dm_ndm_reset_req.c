// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dt/dt_otp_ctrl.h"  // Generated
#include "dt/dt_pinmux.h"    // Generated
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "otp_ctrl_regs.h"
#include "pinmux_regs.h"

#if defined(OPENTITAN_IS_EARLGREY)
#include "dt/dt_adc_ctrl.h"     // Generated
#include "dt/dt_flash_ctrl.h"   // Generated
#include "dt/dt_keymgr.h"       // Generated
#include "dt/dt_sysrst_ctrl.h"  // Generated

#include "adc_ctrl_regs.h"
#include "flash_ctrl_regs.h"
#include "keymgr_regs.h"
#include "sysrst_ctrl_regs.h"
#elif defined(OPENTITAN_IS_DARJEELING)
#include "dt/dt_keymgr_dpe.h"  // Generated

#include "keymgr_dpe_regs.h"
#else
#error Unsupported top
#endif

/*
   RV_DM NDM RESET REQUEST TEST

   In top_earlgrey and top_darjeeling, the CSRs can be divided into 3 groups as
   below.
     1. Group1 : Device under por_reset
        - pwrmgr, rstmgr
     2. Group2 : Device under lc_reset
        - otp_ctrl, pinmux, rv_dm and aontimer

       * clkmgr stay between category 1 and 2.
     3. Group3 : None of the above

   Upon power up, test programs following registers from Group 2 and 3.
     Group2:
                                          RESET    PRGM (ARBITRARY VALUE)
       OTP_CTRL.DIRECT_ACCESS_WDATA0      0x0      0x0609_2022
       PINMUX.WKUP_DETECTOR_CNT_TH_1      0X0      0X44 --> move to LC
       SRAM RET ADDRESS(8)                ?        0xDDAA_55BB
    Group3 (earlgrey):
                                          RESET    PRGM (ARBITRARY VALUE)
       ADC_CTRL.ADC_SAMPLE_CTL            0x9B     0x37
       SYSRST_CTRL.EC_RST_CTL             0x7D0    0x567
       KEYMGR.MAX_OWNER_KEY_VER_SHADOWED  0x0      0x1600_ABBA
       FLASH_CTRL.SCRATCH                 0x0      0x3927
    Group3 (darjeeling):
                                          RESET    PRGM (ARBITRARY VALUE)
       KEYMGR_DPE.MAX_KEY_VER_SHADOWED    0x0      0x1600_ABBA

   After programming csrs, the test assert NDM reset from RV_DM and de-assert.
   Read programmed csr to check all Group2 keep programmed value while group 3
   csrs have reset values.

 */
OTTF_DEFINE_TEST_CONFIG();
/**
 * Test csr struct
 */
typedef struct test_register {
  /**
   * Name of the device.
   */
  const char *name;
  /**
   * Base address of the test block
   */
  uintptr_t base;
  /**
   * Offset of CSR / MEM of the test block
   */
  ptrdiff_t offset;
  /**
   * Arbitrary write value to check register reset.
   * If the register got reset, then this value will get wiped out.
   */
  uint32_t write_val;
  /**
   * Expected read value.
   * For Group 2 registers, it is programmed value - arbitrary, hard coded.
   * For Group 3 registers, it is reset value.
   * in the beginning of the test.
   */
  uint32_t exp_read_val;

} test_register_t;

static dif_rstmgr_t rstmgr;

static void write_test_reg(test_register_t *regs, size_t reg_count) {
  for (size_t i = 0; i < reg_count; ++i) {
    mmio_region_write32(mmio_region_from_addr(regs[i].base), regs[i].offset,
                        regs[i].write_val);
  }
}

static void check_test_reg(test_register_t *regs, size_t reg_count) {
  for (size_t i = 0; i < reg_count; ++i) {
    uint32_t val =
        mmio_region_read32(mmio_region_from_addr(regs[i].base), regs[i].offset);
    CHECK(val == regs[i].exp_read_val, "reg[%d]: obs:0x%x  exp:0x%x", i, val,
          regs[i].exp_read_val);
  }
}

bool test_main(void) {
  test_register_t regs[] = {
    {
        .name = "OTP_CTRL",
        .base = dt_otp_ctrl_primary_reg_block(kDtOtpCtrl),
        .offset = OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET,
        .write_val = 0x06092022,
        .exp_read_val = OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_RESVAL,
    },
    {
        .name = "PINMUX",
        .base = dt_pinmux_primary_reg_block(kDtPinmuxAon),
        .offset = PINMUX_WKUP_DETECTOR_CNT_TH_1_REG_OFFSET,
        .write_val = 0x44,
        .exp_read_val = PINMUX_WKUP_DETECTOR_CNT_TH_1_REG_RESVAL,

    },
#if defined(OPENTITAN_IS_EARLGREY)
    {
        .name = "ADC_CTRL",
        .base = dt_adc_ctrl_primary_reg_block(kDtAdcCtrlAon),
        .offset = ADC_CTRL_ADC_SAMPLE_CTL_REG_OFFSET,
        .write_val = 0x37,
        .exp_read_val = ADC_CTRL_ADC_SAMPLE_CTL_REG_RESVAL,

    },
    {
        .name = "SYSRST_CTRL",
        .base = dt_sysrst_ctrl_primary_reg_block(kDtSysrstCtrlAon),
        .offset = SYSRST_CTRL_EC_RST_CTL_REG_OFFSET,
        .write_val = 0x567,
        .exp_read_val = SYSRST_CTRL_EC_RST_CTL_REG_RESVAL,

    },
    {
        .name = "KEYMGR",
        .base = dt_keymgr_primary_reg_block(kDtKeymgr),
        .offset = KEYMGR_MAX_OWNER_KEY_VER_SHADOWED_REG_OFFSET,
        .write_val = 0x1600ABBA,
        .exp_read_val = KEYMGR_MAX_OWNER_KEY_VER_SHADOWED_REG_RESVAL,

    },
    {
        .name = "FLASH_CTRL",
        .base = dt_flash_ctrl_primary_reg_block(kDtFlashCtrl),
        .offset = FLASH_CTRL_SCRATCH_REG_OFFSET,
        .write_val = 0x3927,
        .exp_read_val = FLASH_CTRL_SCRATCH_REG_RESVAL,
    },
#elif defined(OPENTITAN_IS_DARJEELING)
    {
        .name = "KEYMGR_DPE",
        .base = dt_keymgr_dpe_primary_reg_block(kDtKeymgrDpe),
        .offset = KEYMGR_DPE_MAX_KEY_VER_SHADOWED_REG_OFFSET,
        .write_val = 0x1600ABBA,
        .exp_read_val = KEYMGR_DPE_MAX_KEY_VER_SHADOWED_REG_RESVAL,
    },
#else
#error Unsupported top
#endif
  };

  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kDtRstmgrAon, &rstmgr));

  if (UNWRAP(rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor))) {
    rstmgr_testutils_reason_clear();

    // Write arbitrary value to each test register.
    write_test_reg(regs, ARRAYSIZE(regs));

    LOG_INFO("wait for ndm reset");
    wait_for_interrupt();
  } else {
    // NDM reset is de-asserted.
    // Check reset info to be kDifRstmgrResetInfoNdm.
    LOG_INFO("check reset info");
    CHECK(UNWRAP(
        rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoNdm)));

    // Register value check after reset.
    LOG_INFO("Check registers");
    check_test_reg(regs, ARRAYSIZE(regs));
    return true;
  }
  return false;
}
