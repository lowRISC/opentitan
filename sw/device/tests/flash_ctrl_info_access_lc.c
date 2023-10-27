// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_lc_ctrl.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/lc_ctrl_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "lc_ctrl_regs.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

static dif_lc_ctrl_t lc_ctrl;
static dif_rv_plic_t plic0;
static dif_flash_ctrl_state_t flash_state;
static dif_flash_ctrl_t flash_ctrl;

static plic_isr_ctx_t plic_ctx = {
    .rv_plic = &plic0,
    .hart_id = kTopEarlgreyPlicTargetIbex0,
};

static flash_ctrl_isr_ctx_t flash_ctx = {
    .flash_ctrl = &flash_ctrl,
    .plic_flash_ctrl_start_irq_id = kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty,
    .is_only_irq = false,
};

enum {
  kFlashInfoBank = 0,
  kPartitionId = 0,
  kFlashInfoPageIdCreatorSecret = 1,
  kFlashInfoPageIdOwnerSecret = 2,
  kFlashInfoPageIdIsoPart = 3,
  kInfoSize = 16,
  kNumIRQs = 5,
};

static const uint32_t kRandomData1[kInfoSize] = {
    0xb295d21b, 0xecdfbdcd, 0x67e7ab2d, 0x6f660b08, 0x273bf65c, 0xe80f1695,
    0x586b80db, 0xc3dba27e, 0xdc124c5d, 0xb01ccd52, 0x815713e1, 0x31a141b2,
    0x2124be3b, 0x299a6f2a, 0x1f2a4741, 0x1a073cc0,
};

static const uint32_t kRandomData2[kInfoSize] = {
    0x69e705a0, 0x65c2ec6b, 0x04b0b634, 0x59313526, 0x1858aee1, 0xd49f3ba9,
    0x230bcd38, 0xc1eb6b3e, 0x68c15e3b, 0x024d02a9, 0x0b062ae4, 0x334dd155,
    0x53fdbf8a, 0x3792f1e2, 0xee317161, 0x33b19bf3,
};

static const uint32_t kRandomData3[kInfoSize] = {
    0x2b78dbf5, 0x3e6e5a00, 0xbf82c6d5, 0x68d8e33f, 0x9c524bbc, 0xac5beeef,
    0x1287ca5a, 0x12b61419, 0x872e709f, 0xf91b7c0c, 0x18312a1f, 0x325cef9a,
    0x19fefa95, 0x4ceb421b, 0xa57d74c4, 0xaf1d723d,
};

static volatile bool expected_irqs[kNumIRQs];
static volatile bool fired_irqs[kNumIRQs];

/**
 * Provides external IRQ handling for this test.
 *
 * This function overrides the default OTTF external ISR.
 */
void ottf_external_isr(void) {
  top_earlgrey_plic_peripheral_t peripheral_serviced;
  dif_flash_ctrl_irq_t irq_serviced;
  isr_testutils_flash_ctrl_isr(plic_ctx, flash_ctx, &peripheral_serviced,
                               &irq_serviced);
  CHECK(peripheral_serviced == kTopEarlgreyPlicPeripheralFlashCtrl,
        "Interurpt from unexpected peripheral: %d", peripheral_serviced);
  fired_irqs[irq_serviced] = true;
}

/**
 * Clear the volatile IRQ variables.
 */
static void clear_irq_variables(void) {
  for (int i = 0; i < kNumIRQs; ++i) {
    expected_irqs[i] = false;
    fired_irqs[i] = false;
  }
}

/**
 * Initializes FLASH_CTRL and enables the relevant interrupts.
 */
static void flash_ctrl_init_with_irqs(mmio_region_t base_addr,
                                      dif_flash_ctrl_state_t *flash_state,
                                      dif_flash_ctrl_t *flash_ctrl) {
  CHECK_DIF_OK(dif_flash_ctrl_init(base_addr, flash_ctrl));
  CHECK_DIF_OK(dif_flash_ctrl_init_state(flash_state, base_addr));

  for (dif_flash_ctrl_irq_t i = 0; i < kNumIRQs; ++i) {
    CHECK_DIF_OK(dif_flash_ctrl_irq_set_enabled(
        flash_ctrl, kDifFlashCtrlIrqProgEmpty + i, kDifToggleEnabled));
  }
  clear_irq_variables();
}

/**
 * Compares the expected and fired IRQs and clears both.
 */
static void compare_and_clear_irq_variables(void) {
  for (int i = 0; i < kNumIRQs; ++i) {
    CHECK(expected_irqs[i] == fired_irqs[i], "expected IRQ mismatch = %d", i);
  }
  clear_irq_variables();
}

/**
 * Access infomation partition.
 * If write or read is not allowed, device will generate recoverable alert
 * (mp_err) and task status of write or read will fail.
 */
static void test_info_part(uint32_t partition_number, const uint32_t *test_data,
                           bool write_allowed, bool read_allowed) {
  uint32_t address = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup(
      &flash_state, partition_number, kFlashInfoBank, kPartitionId, &address));

  CHECK_DIF_OK(dif_flash_ctrl_set_prog_fifo_watermark(&flash_state, 0));
  CHECK_DIF_OK(dif_flash_ctrl_set_read_fifo_watermark(&flash_state, 8));
  clear_irq_variables();

  // Write task:
  // Erase before program the page with test_data.
  if (write_allowed) {
    expected_irqs[kDifFlashCtrlIrqOpDone] = true;
    CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
        &flash_state, address, kPartitionId, kDifFlashCtrlPartitionTypeInfo));
    compare_and_clear_irq_variables();

    LOG_INFO("partition:%1d erase done", partition_number);
    expected_irqs[kDifFlashCtrlIrqOpDone] = true;
    expected_irqs[kDifFlashCtrlIrqProgEmpty] = true;
    expected_irqs[kDifFlashCtrlIrqProgLvl] = true;
    CHECK_STATUS_OK(flash_ctrl_testutils_write(
        &flash_state, address, kPartitionId, test_data,
        kDifFlashCtrlPartitionTypeInfo, kInfoSize));
    compare_and_clear_irq_variables();
    LOG_INFO("partition:%1d write done", partition_number);
  } else {
    CHECK_STATUS_NOT_OK(flash_ctrl_testutils_write(
        &flash_state, address, kPartitionId, test_data,
        kDifFlashCtrlPartitionTypeInfo, kInfoSize));
    LOG_INFO("partition:%1d write not allowed", partition_number);
  }

  // Read task:
  // Read page and compared with test_data.
  uint32_t readback_data[kInfoSize];
  if (read_allowed) {
    expected_irqs[kDifFlashCtrlIrqOpDone] = true;
    expected_irqs[kDifFlashCtrlIrqRdLvl] = true;
    expected_irqs[kDifFlashCtrlIrqRdFull] = true;
    CHECK_STATUS_OK(flash_ctrl_testutils_read(
        &flash_state, address, kPartitionId, readback_data,
        kDifFlashCtrlPartitionTypeInfo, kInfoSize, 1));
    compare_and_clear_irq_variables();
    CHECK_ARRAYS_EQ(readback_data, test_data, kInfoSize);
    LOG_INFO("partition:%1d read done", partition_number);
  } else {
    CHECK_STATUS_NOT_OK(flash_ctrl_testutils_read(
        &flash_state, address, kPartitionId, readback_data,
        kDifFlashCtrlPartitionTypeInfo, kInfoSize, 1));
    LOG_INFO("partition:%1d read not allowed", partition_number);
  }
}

bool test_main(void) {
  CHECK_DIF_OK(dif_lc_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_LC_CTRL_BASE_ADDR), &lc_ctrl));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic0));

  flash_ctrl_init_with_irqs(
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR),
      &flash_state, &flash_ctrl);
  rv_plic_testutils_irq_range_enable(&plic0, plic_ctx.hart_id,
                                     kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty,
                                     kTopEarlgreyPlicIrqIdFlashCtrlOpDone);

  // Enable the external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  dif_lc_ctrl_id_state_t lc_id_state;
  dif_lc_ctrl_state_t lc_state;
  bool personalized = false;
  // Check if device is personalized.
  uint32_t reg =
      mmio_region_read32(lc_ctrl.base_addr, LC_CTRL_LC_ID_STATE_REG_OFFSET);
  LOG_INFO("id_state: %x", reg);

  CHECK_DIF_OK(dif_lc_ctrl_get_id_state(&lc_ctrl, &lc_id_state));
  personalized = (lc_id_state == kDifLcCtrlIdStatePersonalized);
  LOG_INFO("test: personalized : %d", personalized);

  // Read lc state and execute info part access test.
  // Life cycle controlled info partition access is summarized in
  // (https://opentitan.org/book/hw/ip/lc_ctrl/doc/theory_of_operation.html#
  // life-cycle-access-control-signals)
  CHECK_DIF_OK(dif_lc_ctrl_get_state(&lc_ctrl, &lc_state));
  CHECK_STATUS_OK(lc_ctrl_testutils_lc_state_log(&lc_state));

  switch (lc_state) {
    case kDifLcCtrlStateTestUnlocked0:
      test_info_part(kFlashInfoPageIdCreatorSecret, kRandomData1,
                     /*write_allowed=*/0, /*read_allowed=*/0);
      test_info_part(kFlashInfoPageIdOwnerSecret, kRandomData2,
                     /*write_allowed=*/0, /*read_allowed=*/0);
      test_info_part(kFlashInfoPageIdIsoPart, kRandomData3, /*write_allowed=*/1,
                     /*read_allowed=*/0);
      break;
    case kDifLcCtrlStateDev:
      test_info_part(kFlashInfoPageIdCreatorSecret, kRandomData1,
                     /*write_allowed=*/!personalized,
                     /*read_allowed=*/!personalized);
      test_info_part(kFlashInfoPageIdOwnerSecret, kRandomData2,
                     /*write_allowed=*/1, /*read_allowed=*/1);
      test_info_part(kFlashInfoPageIdIsoPart, kRandomData3, /*write_allowed=*/1,
                     /*read_allowed=*/0);
      break;
    case kDifLcCtrlStateProd:
    case kDifLcCtrlStateProdEnd:
      test_info_part(kFlashInfoPageIdCreatorSecret, kRandomData1,
                     /*write_allowed=*/!personalized,
                     /*read_allowed=*/!personalized);
      test_info_part(kFlashInfoPageIdOwnerSecret, kRandomData2,
                     /*write_allowed=*/1, /*read_allowed=*/1);
      test_info_part(kFlashInfoPageIdIsoPart, kRandomData3, /*write_allowed=*/1,
                     /*read_allowed=*/1);
      break;
    case kDifLcCtrlStateRma:
      test_info_part(kFlashInfoPageIdCreatorSecret, kRandomData1,
                     /*write_allowed=*/1, /*read_allowed=*/1);
      test_info_part(kFlashInfoPageIdOwnerSecret, kRandomData2,
                     /*write_allowed=*/1, /*read_allowed=*/1);
      test_info_part(kFlashInfoPageIdIsoPart, kRandomData3, /*write_allowed=*/1,
                     /*read_allowed=*/1);
      break;
    default:
      LOG_ERROR("Unexpected lc state 0x%x", lc_state);
  }
  return true;
}
