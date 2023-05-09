// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

#define FLASH_CTRL_NUM_IRQS 5

OTTF_DEFINE_TEST_CONFIG();

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
  kFlashInfoPageIdCreatorSecret = 1,
  kFlashInfoPageIdOwnerSecret = 2,
  kFlashInfoPageIdIsoPart = 3,
  kFlashInfoBank = 0,
  kRegionBaseBank0Page0Index = 0,
  kRegionBaseBank1Page0Index = 256,
  kRegionBaseBank1Page255Index = 511,
  kFlashBank0DataRegion = 0,
  kFlashBank1DataRegion = 1,
  kPartitionId = 0,
  kRegionSize = 1,
  kInfoSize = 16,
  kDataSize = 32,
  kPageSize = 2048,
};

const uint32_t kRandomData1[kInfoSize] = {
    0xb295d21b, 0xecdfbdcd, 0x67e7ab2d, 0x6f660b08, 0x273bf65c, 0xe80f1695,
    0x586b80db, 0xc3dba27e, 0xdc124c5d, 0xb01ccd52, 0x815713e1, 0x31a141b2,
    0x2124be3b, 0x299a6f2a, 0x1f2a4741, 0x1a073cc0,
};

const uint32_t kRandomData2[kInfoSize] = {
    0x69e705a0, 0x65c2ec6b, 0x04b0b634, 0x59313526, 0x1858aee1, 0xd49f3ba9,
    0x230bcd38, 0xc1eb6b3e, 0x68c15e3b, 0x024d02a9, 0x0b062ae4, 0x334dd155,
    0x53fdbf8a, 0x3792f1e2, 0xee317161, 0x33b19bf3,
};

const uint32_t kRandomData3[kInfoSize] = {
    0x2b78dbf5, 0x3e6e5a00, 0xbf82c6d5, 0x68d8e33f, 0x9c524bbc, 0xac5beeef,
    0x1287ca5a, 0x12b61419, 0x872e709f, 0xf91b7c0c, 0x18312a1f, 0x325cef9a,
    0x19fefa95, 0x4ceb421b, 0xa57d74c4, 0xaf1d723d,
};

const uint32_t kRandomData4[kDataSize] = {
    0x0f5b84a3, 0xfa0330c3, 0xe125d174, 0x959d9779, 0xe10da3ba, 0x739e804d,
    0xf8f8c317, 0xf236e75f, 0xa2118c37, 0x2d12fa9d, 0xa6fd72cd, 0x4b21d3dc,
    0x6d36ca93, 0xbac514a6, 0x5f5695f8, 0xe7fdbe07, 0xde77eac9, 0x5ee7432f,
    0xc7d26081, 0xae1d7262, 0x47d46715, 0x9da2de97, 0xa41e639d, 0x34470ce0,
    0x8ac69175, 0x1dbcd910, 0x8193d43e, 0xe1538689, 0x166599e1, 0x0d5cc465,
    0x86298854, 0x93121b13,
};

const uint32_t kRandomData5[kDataSize] = {
    0xe5214227, 0x8473a570, 0xc6fc9728, 0x6110fbbe, 0xa2b4cdc8, 0x0156836a,
    0xa0c90954, 0x23e66c9b, 0x607c9e7c, 0x40f993b6, 0x253dfc7d, 0xe0c70727,
    0xa7b974ea, 0x0e8561c8, 0xfe8858a9, 0x36bf06bc, 0x2a734e91, 0xf0aca1e6,
    0x6e22f4c5, 0x469cb0a2, 0x0f6bbc43, 0xc719f5cd, 0x0a129d7d, 0x9a6c171e,
    0x1b39ff3a, 0x9644ab82, 0x5209d14c, 0x46a7e380, 0x575b1e0b, 0x4af5e8c3,
    0xfcbbfa64, 0xe3afddf2,
};

static volatile bool expected_irqs[FLASH_CTRL_NUM_IRQS];
static volatile bool fired_irqs[FLASH_CTRL_NUM_IRQS];

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
  for (int i = 0; i < FLASH_CTRL_NUM_IRQS; ++i) {
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

  for (dif_flash_ctrl_irq_t i = 0; i < FLASH_CTRL_NUM_IRQS; ++i) {
    CHECK_DIF_OK(dif_flash_ctrl_irq_set_enabled(
        flash_ctrl, kDifFlashCtrlIrqProgEmpty + i, kDifToggleEnabled));
  }
  clear_irq_variables();
}

/**
 * Compares the expected and fired IRQs and clears both.
 */
static void compare_and_clear_irq_variables(void) {
  for (int i = 0; i < FLASH_CTRL_NUM_IRQS; ++i) {
    CHECK(expected_irqs[i] == fired_irqs[i], "expected IRQ mismatch = %d", i);
  }
  clear_irq_variables();
}

/**
 * Check data read from host interface against known data.
 */
static void read_and_check_host_if(uint32_t addr, const uint32_t *check_data) {
  mmio_region_t flash_addr =
      mmio_region_from_addr(TOP_EARLGREY_EFLASH_BASE_ADDR + addr);
  uint32_t host_data[kDataSize];
  for (int i = 0; i < kDataSize; ++i) {
    host_data[i] =
        mmio_region_read32(flash_addr, i * (ptrdiff_t)sizeof(uint32_t));
  }
  CHECK_ARRAYS_EQ(host_data, check_data, kDataSize);
}

/**
 * Tests the interrupts for erase, write and
 * read of the specified information partition.
 * Confirms that the written data is read back correctly.
 */
static void do_info_partition_test(uint32_t partition_number,
                                   const uint32_t *test_data) {
  uint32_t address = 0;
  CHECK_STATUS_OK(flash_ctrl_testutils_info_region_setup(
      &flash_state, partition_number, kFlashInfoBank, kPartitionId, &address));

  CHECK_DIF_OK(dif_flash_ctrl_set_prog_fifo_watermark(&flash_state, 0));
  CHECK_DIF_OK(dif_flash_ctrl_set_read_fifo_watermark(&flash_state, 8));

  clear_irq_variables();

  expected_irqs[kDifFlashCtrlIrqOpDone] = true;
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
      &flash_state, address, kPartitionId, kDifFlashCtrlPartitionTypeInfo));
  compare_and_clear_irq_variables();

  expected_irqs[kDifFlashCtrlIrqOpDone] = true;
  expected_irqs[kDifFlashCtrlIrqProgEmpty] = true;
  expected_irqs[kDifFlashCtrlIrqProgLvl] = true;
  CHECK_STATUS_OK(
      flash_ctrl_testutils_write(&flash_state, address, kPartitionId, test_data,
                                 kDifFlashCtrlPartitionTypeInfo, kInfoSize));

  compare_and_clear_irq_variables();

  uint32_t readback_data[kInfoSize];
  expected_irqs[kDifFlashCtrlIrqOpDone] = true;
  expected_irqs[kDifFlashCtrlIrqRdLvl] = true;
  expected_irqs[kDifFlashCtrlIrqRdFull] = true;
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash_state, address, kPartitionId, readback_data,
      kDifFlashCtrlPartitionTypeInfo, kInfoSize, 1));

  compare_and_clear_irq_variables();

  CHECK_ARRAYS_EQ(readback_data, test_data, kInfoSize);
}

/**
 * Tests the interrupts for read of bank0 data partition.
 * Only read is tested as this partition contains the program
 * code so should not be erased or written.
 * The data read via the flash_ctrl interface is checked against the
 * data read via the host interface.
 */
static void do_bank0_data_partition_test(void) {
  uint32_t address;
  CHECK_STATUS_OK(flash_ctrl_testutils_data_region_setup(
      &flash_state, kRegionBaseBank0Page0Index, kFlashBank0DataRegion,
      kRegionSize, &address));

  CHECK_DIF_OK(dif_flash_ctrl_set_read_fifo_watermark(&flash_state, 8));

  clear_irq_variables();
  expected_irqs[kDifFlashCtrlIrqOpDone] = true;
  expected_irqs[kDifFlashCtrlIrqRdLvl] = true;
  expected_irqs[kDifFlashCtrlIrqRdFull] = true;

  uint32_t readback_data[kDataSize];
  CHECK_STATUS_OK(flash_ctrl_testutils_read(
      &flash_state, address, kPartitionId, readback_data,
      kDifFlashCtrlPartitionTypeData, kDataSize, 1));

  compare_and_clear_irq_variables();
  read_and_check_host_if(0, readback_data);
}

/**
 * Tests the interrupts for erase, write and read of
 * the lowest and highest page of bank 1 data partition.
 * Confirms that the written data is read back correctly.
 * The whole bank is then erased and the interrupt is checked
 * followed by confirmation that the previously written data
 * has been wiped.
 */
static void do_bank1_data_partition_test(void) {
  uint32_t address = 0;
  CHECK_DIF_OK(dif_flash_ctrl_set_prog_fifo_watermark(&flash_state, 0));
  CHECK_DIF_OK(dif_flash_ctrl_set_read_fifo_watermark(&flash_state, 8));

  // Loop for low and high page erase, write and read.
  for (int i = 0; i < 2; ++i) {
    uint32_t page_index =
        (i == 0) ? kRegionBaseBank1Page0Index : kRegionBaseBank1Page255Index;
    const uint32_t *test_data = (i == 0) ? kRandomData4 : kRandomData5;

    CHECK_STATUS_OK(flash_ctrl_testutils_data_region_setup(
        &flash_state, page_index, kFlashBank1DataRegion, kRegionSize,
        &address));

    clear_irq_variables();

    expected_irqs[kDifFlashCtrlIrqOpDone] = true;
    CHECK_STATUS_OK(flash_ctrl_testutils_erase_page(
        &flash_state, address, kPartitionId, kDifFlashCtrlPartitionTypeData));

    compare_and_clear_irq_variables();

    expected_irqs[kDifFlashCtrlIrqOpDone] = true;
    expected_irqs[kDifFlashCtrlIrqProgEmpty] = true;
    expected_irqs[kDifFlashCtrlIrqProgLvl] = true;
    CHECK_STATUS_OK(flash_ctrl_testutils_write(
        &flash_state, address, kPartitionId, test_data,
        kDifFlashCtrlPartitionTypeData, kDataSize));

    compare_and_clear_irq_variables();

    uint32_t readback_data[kDataSize];
    expected_irqs[kDifFlashCtrlIrqOpDone] = true;
    expected_irqs[kDifFlashCtrlIrqRdLvl] = true;
    expected_irqs[kDifFlashCtrlIrqRdFull] = true;
    CHECK_STATUS_OK(flash_ctrl_testutils_read(
        &flash_state, address, kPartitionId, readback_data,
        kDifFlashCtrlPartitionTypeData, kDataSize, 1));

    compare_and_clear_irq_variables();

    read_and_check_host_if(kPageSize * page_index, test_data);
    CHECK_ARRAYS_EQ(readback_data, test_data, kDataSize);
  }

  // Erasing the whole of bank 1.
  CHECK_DIF_OK(dif_flash_ctrl_set_bank_erase_enablement(&flash_state, 1,
                                                        kDifToggleEnabled));
  expected_irqs[kDifFlashCtrlIrqOpDone] = true;

  CHECK_STATUS_OK(flash_ctrl_testutils_data_region_setup(
      &flash_state, kRegionBaseBank1Page0Index, kFlashBank1DataRegion,
      kRegionSize, &address));
  dif_flash_ctrl_transaction_t transaction = {
      .byte_address = address,
      .op = kDifFlashCtrlOpBankErase,
      .partition_type = kDifFlashCtrlPartitionTypeData,
      .partition_id = 0x0,
      .word_count = 0x0};
  CHECK_DIF_OK(dif_flash_ctrl_start(&flash_state, transaction));
  CHECK_STATUS_OK(flash_ctrl_testutils_wait_transaction_end(&flash_state));

  compare_and_clear_irq_variables();

  // Loop for low and high page read back after bank erase.
  for (int i = 0; i < 2; ++i) {
    uint32_t page_index =
        (i == 0) ? kRegionBaseBank1Page0Index : kRegionBaseBank1Page255Index;

    CHECK_STATUS_OK(flash_ctrl_testutils_data_region_setup(
        &flash_state, page_index, kFlashBank1DataRegion, kRegionSize,
        &address));

    uint32_t readback_data[kDataSize];
    expected_irqs[kDifFlashCtrlIrqOpDone] = true;
    expected_irqs[kDifFlashCtrlIrqRdLvl] = true;
    expected_irqs[kDifFlashCtrlIrqRdFull] = true;
    CHECK_STATUS_OK(flash_ctrl_testutils_read(
        &flash_state, address, kPartitionId, readback_data,
        kDifFlashCtrlPartitionTypeData, kDataSize, 1));

    compare_and_clear_irq_variables();

    uint32_t expected_data[kDataSize];
    memset(expected_data, 0xff, sizeof(expected_data));

    read_and_check_host_if(kPageSize * page_index, expected_data);
    CHECK_ARRAYS_EQ(readback_data, expected_data, kDataSize);
  }
}

bool test_main(void) {
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

  do_info_partition_test(kFlashInfoPageIdCreatorSecret, kRandomData1);
  do_info_partition_test(kFlashInfoPageIdOwnerSecret, kRandomData2);
  do_info_partition_test(kFlashInfoPageIdIsoPart, kRandomData3);
  do_bank0_data_partition_test();
  do_bank1_data_partition_test();

  return true;
}
