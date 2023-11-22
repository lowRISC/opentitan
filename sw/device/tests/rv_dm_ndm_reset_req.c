// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "adc_ctrl_regs.h"
#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "keymgr_regs.h"
#include "otp_ctrl_regs.h"
#include "pinmux_regs.h"
#include "sysrst_ctrl_regs.h"
/*
   RV_DM NDM RESET REQUEST TEST
   In top_earlgrey, the CSRs can be divided into 3 groups as below.
     1. Group1 : Devce under por_reset
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
    Group3:
                                          RESET    PRGM (ARBITRARY VALUE)
       ADC_CTRL.ADC_SAMPLE_CTL            0x9B     0x37
       SYSRST_CTRL.EC_RST_CTL             0x7D0    0x567
       KEYMGR.MAX_OWNER_KEY_VER_SHADOWED  0x0      0x1600_ABBA
       FLASH_CTRL.SCRATCH                 0x0      0x3927

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
  const uintptr_t base;
  /**
   * Offset of CSR / MEM of the test block
   */
  const ptrdiff_t offset;
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
static dif_otp_ctrl_t otp_ctrl;
static dif_flash_ctrl_t flash_ctrl;
static dif_adc_ctrl_t adc_ctrl;
static dif_sysrst_ctrl_t sysrst_ctrl;
static dif_pinmux_t pinmux;
static dif_keymgr_t keymgr;

enum {
  OTP_CTRL,
  PINMUX,
  ADC_CTRL,
  SYSRST_CTRL,
  KEYMGR,
  FLASH_CTRL,
};

static test_register_t kReg[] = {
    [OTP_CTRL] =
        {
            .name = "OTP_CTRL",
            .base = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR,
            .offset = OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_OFFSET,
            .write_val = 0x06092022,
            .exp_read_val = OTP_CTRL_DIRECT_ACCESS_WDATA_0_REG_RESVAL,
        },
    [PINMUX] =
        {
            .name = "PINMUX",
            .base = TOP_EARLGREY_PINMUX_AON_BASE_ADDR,
            .offset = PINMUX_WKUP_DETECTOR_CNT_TH_1_REG_OFFSET,
            .write_val = 0x44,
            .exp_read_val = PINMUX_WKUP_DETECTOR_CNT_TH_1_REG_RESVAL,

        },
    [ADC_CTRL] =
        {
            .name = "ADC_CTRL",
            .base = TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR,
            .offset = ADC_CTRL_ADC_SAMPLE_CTL_REG_OFFSET,
            .write_val = 0x37,
            .exp_read_val = ADC_CTRL_ADC_SAMPLE_CTL_REG_RESVAL,

        },
    [SYSRST_CTRL] =
        {
            .name = "SYSRST_CTRL",
            .base = TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR,
            .offset = SYSRST_CTRL_EC_RST_CTL_REG_OFFSET,
            .write_val = 0x567,
            .exp_read_val = SYSRST_CTRL_EC_RST_CTL_REG_RESVAL,

        },
    [KEYMGR] =
        {
            .name = "KEYMGR",
            .base = TOP_EARLGREY_KEYMGR_BASE_ADDR,
            .offset = KEYMGR_MAX_OWNER_KEY_VER_SHADOWED_REG_OFFSET,
            .write_val = 0x1600ABBA,
            .exp_read_val = KEYMGR_MAX_OWNER_KEY_VER_SHADOWED_REG_RESVAL,

        },
    [FLASH_CTRL] =
        {
            .name = "FLASH_CTRL",
            .base = TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR,
            .offset = FLASH_CTRL_SCRATCH_REG_OFFSET,
            .write_val = 0x3927,
            .exp_read_val = FLASH_CTRL_SCRATCH_REG_RESVAL,
        },
};

static void write_test_reg(void) {
  for (size_t i = 0; i < ARRAYSIZE(kReg); ++i) {
    mmio_region_write32(mmio_region_from_addr(kReg[i].base), kReg[i].offset,
                        kReg[i].write_val);
  }
}

static void check_test_reg(void) {
  for (size_t i = 0; i < ARRAYSIZE(kReg); ++i) {
    uint32_t val =
        mmio_region_read32(mmio_region_from_addr(kReg[i].base), kReg[i].offset);
    CHECK(val == kReg[i].exp_read_val, "reg[%d]: obs:0x%x  exp:0x%x", i, val,
          kReg[i].exp_read_val);
  }
}

static void init_peripherals(void) {
  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_rstmgr_init(addr, &rstmgr));

  addr = mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(addr, &otp_ctrl));

  addr = mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_flash_ctrl_init(addr, &flash_ctrl));

  addr = mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_adc_ctrl_init(addr, &adc_ctrl));

  addr = mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_sysrst_ctrl_init(addr, &sysrst_ctrl));

  addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pinmux_init(addr, &pinmux));

  addr = mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR);
  CHECK_DIF_OK(dif_keymgr_init(addr, &keymgr));
}

bool test_main(void) {
  init_peripherals();

  if (UNWRAP(rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor))) {
    rstmgr_testutils_reason_clear();

    // Write arbitrary value to each test register.
    write_test_reg();

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
    check_test_reg();
    return true;
  }
  return false;
}
