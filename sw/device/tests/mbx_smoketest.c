// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// (DV Counterpart -> chip_sw_mbx_smoke_vseq.sv)
//
// - vseq(UVM) drives the test as the requester, sw responds
//   - vseq sends a request to a single mailbox at a time
//   - vseq does not send a new request until the previous txn (req+rsp) has
//   completed
//   - SW identifies the mbx via the req irq, and responds via the same mbx
// - Before any mbx txns, vseq sends nTxns via sw_symbol_backdoor_overwrite()
//   - After this many transactions, sw will end the test with success.
//   - Between txns, sw uses WFI to await the next req message

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/mbx/dif/dif_mbx.h"
#include "sw/ip/rv_core_ibex/test/utils/rv_core_ibex_testutils.h"
#include "sw/ip/rv_plic/dif/dif_rv_plic.h"
#include "sw/ip/sram_ctrl/dif/dif_sram_ctrl.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/irq.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "mbx_regs.h"  // Generated
#include "sw/top_darjeeling/sw/test/utils/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kHart = kTopDarjeelingPlicTargetIbex0,
  kIrqVoid = UINT32_MAX,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_sram_ctrl_t sram_ctrl_mbox;
static dif_rv_plic_t rv_plic;

// TODO. get this #define from a chip-specific header
#define NUM_MBXS 10
static dif_mbx_t gMbx[NUM_MBXS];
static dif_mbx_transaction_t gTxn[NUM_MBXS];

// Define some test-state that allow multiple mailboxes transactions to
// handled at the same time. We need to hold some global state to ensure
// that the different routines can be reentrant.
typedef enum mbx_txn_state {
  kStateIdle = 0,
  kStateWaitingForRequest = 1,
  kStateReceivedRequest = 2,
  kStateGeneratingResponse = 3,
  kStateWaitingForResponseDrained = 4,
  kStateCleaningUp = 5,
} mbx_txn_state_t;
typedef struct mbx_test_handler_state {
  dif_mbx_t *mbx;
  dif_mbx_irq_state_snapshot_t irq_state;
  dif_mbx_transaction_t *txn;
  mbx_txn_state_t txn_state;
  dif_mbx_irq_t mbx_irq_serviced;
  dif_rv_plic_irq_id_t plic_irq_serviced;
} mbx_test_handler_state_t;
static volatile mbx_test_handler_state_t gHandlerState[NUM_MBXS];
static volatile bool is_finished;

// CONSTANTS
static const dif_mbx_irq_t mbx_irq_ids[] = {
    kDifMbxIrqMbxReady, kDifMbxIrqMbxAbort, kDifMbxIrqMbxError};

dif_rv_plic_irq_id_t irq_ids_rv_plic[] = {
    kTopDarjeelingPlicIrqIdMbx0MbxReady,     /**< mbx0_mbx_ready */
    kTopDarjeelingPlicIrqIdMbx0MbxAbort,     /**< mbx0_mbx_abort */
    kTopDarjeelingPlicIrqIdMbx0MbxError,     /**< mbx0_mbx_error */
    kTopDarjeelingPlicIrqIdMbx1MbxReady,     /**< mbx1_mbx_ready */
    kTopDarjeelingPlicIrqIdMbx1MbxAbort,     /**< mbx1_mbx_abort */
    kTopDarjeelingPlicIrqIdMbx1MbxError,     /**< mbx1_mbx_error */
    kTopDarjeelingPlicIrqIdMbx2MbxReady,     /**< mbx2_mbx_ready */
    kTopDarjeelingPlicIrqIdMbx2MbxAbort,     /**< mbx2_mbx_abort */
    kTopDarjeelingPlicIrqIdMbx2MbxError,     /**< mbx2_mbx_error */
    kTopDarjeelingPlicIrqIdMbx3MbxReady,     /**< mbx3_mbx_ready */
    kTopDarjeelingPlicIrqIdMbx3MbxAbort,     /**< mbx3_mbx_abort */
    kTopDarjeelingPlicIrqIdMbx3MbxError,     /**< mbx3_mbx_error */
    kTopDarjeelingPlicIrqIdMbx4MbxReady,     /**< mbx4_mbx_ready */
    kTopDarjeelingPlicIrqIdMbx4MbxAbort,     /**< mbx4_mbx_abort */
    kTopDarjeelingPlicIrqIdMbx4MbxError,     /**< mbx4_mbx_error */
    kTopDarjeelingPlicIrqIdMbx5MbxReady,     /**< mbx5_mbx_ready */
    kTopDarjeelingPlicIrqIdMbx5MbxAbort,     /**< mbx5_mbx_abort */
    kTopDarjeelingPlicIrqIdMbx5MbxError,     /**< mbx5_mbx_error */
    kTopDarjeelingPlicIrqIdMbx6MbxReady,     /**< mbx6_mbx_ready */
    kTopDarjeelingPlicIrqIdMbx6MbxAbort,     /**< mbx6_mbx_abort */
    kTopDarjeelingPlicIrqIdMbx6MbxError,     /**< mbx6_mbx_error */
    kTopDarjeelingPlicIrqIdMbxJtagMbxReady,  /**< mbx_jtag_mbx_ready */
    kTopDarjeelingPlicIrqIdMbxJtagMbxAbort,  /**< mbx_jtag_mbx_abort */
    kTopDarjeelingPlicIrqIdMbxJtagMbxError,  /**< mbx_jtag_mbx_error */
    kTopDarjeelingPlicIrqIdMbxPcie0MbxReady, /**< mbx_pcie0_mbx_ready */
    kTopDarjeelingPlicIrqIdMbxPcie0MbxAbort, /**< mbx_pcie0_mbx_abort */
    kTopDarjeelingPlicIrqIdMbxPcie0MbxError, /**< mbx_pcie0_mbx_error */
    kTopDarjeelingPlicIrqIdMbxPcie1MbxReady, /**< mbx_pcie1_mbx_ready */
    kTopDarjeelingPlicIrqIdMbxPcie1MbxAbort, /**< mbx_pcie1_mbx_abort */
    kTopDarjeelingPlicIrqIdMbxPcie1MbxError, /**< mbx_pcie1_mbx_error */
};

enum {
  kSoftwareBarrierTimeoutUsec = 100,
};
/* This value is updated by the testbench to synchronize. */
static volatile const uint8_t kSoftwareBarrier = 0;
static volatile const uint8_t kNumTxns = 0;

//////////////////////
// HELPER FUNCTIONS //
//////////////////////

static void increment_array_uint32(uint32_t *arr, uint32_t size) {
  for (size_t i = 0; i < size; ++i) {
    arr[i]++;
  }
}

/**
 * Get the mbx object from the plic_peripheral index.
 *
 * This can be used to get back to the corresponding dif_mbx_t object from a
 * plic_irq. e.g. dif_mbx_t *mbx =
 * get_mbx_handler(top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id]);
 */
volatile mbx_test_handler_state_t *get_mbx_handler(
    top_darjeeling_plic_peripheral_t peripheral) {
  switch (peripheral) {
    case kTopDarjeelingPlicPeripheralMbx0: {
      return &gHandlerState[0];
    }
    case kTopDarjeelingPlicPeripheralMbx1: {
      return &gHandlerState[1];
    }
    case kTopDarjeelingPlicPeripheralMbx2: {
      return &gHandlerState[2];
    }
    case kTopDarjeelingPlicPeripheralMbx3: {
      return &gHandlerState[3];
    }
    case kTopDarjeelingPlicPeripheralMbx4: {
      return &gHandlerState[4];
    }
    case kTopDarjeelingPlicPeripheralMbx5: {
      return &gHandlerState[5];
    }
    case kTopDarjeelingPlicPeripheralMbx6: {
      return &gHandlerState[6];
    }
    case kTopDarjeelingPlicPeripheralMbxJtag: {
      return &gHandlerState[7];
    }
    case kTopDarjeelingPlicPeripheralMbxPcie0: {
      return &gHandlerState[8];
    }
    case kTopDarjeelingPlicPeripheralMbxPcie1: {
      return &gHandlerState[9];
    }
    default: {
      CHECK(false,
            "get_mbx_handler() called for a plic_peripheral that is not a "
            "mailbox!");
      return 0;
    }
  }  // switch(peripheral)
}

/**
 * Get the dif_mbx_irq_t index for a given plic_irq index.
 * We do this by creating a lookup from peripherals to their lowest irq's in the
 * plic.
 *
 * This is used to identify irq's in the scope of the peripheral, which we
 * find by counting the difference between the irq and the lowest irq of the
 * peripheral instance.
 */
dif_rv_plic_irq_id_t get_lowest_irq(dif_rv_plic_irq_id_t plic_irq_id) {
  // Get the peripheral this plic_irq_id belongs to.
  top_darjeeling_plic_peripheral_t peripheral =
      (top_darjeeling_plic_peripheral_t)
          top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  // Get the lowest irq of this peripheral.
  dif_rv_plic_irq_id_t plic_periph_base_irq_id;
  switch (peripheral) {
    case kTopDarjeelingPlicPeripheralMbx0: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbx0MbxReady;
      break;
    }
    case kTopDarjeelingPlicPeripheralMbx1: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbx1MbxReady;
      break;
    }
    case kTopDarjeelingPlicPeripheralMbx2: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbx2MbxReady;
      break;
    }
    case kTopDarjeelingPlicPeripheralMbx3: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbx3MbxReady;
      break;
    }
    case kTopDarjeelingPlicPeripheralMbx4: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbx4MbxReady;
      break;
    }
    case kTopDarjeelingPlicPeripheralMbx5: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbx5MbxReady;
      break;
    }
    case kTopDarjeelingPlicPeripheralMbx6: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbx6MbxReady;
      break;
    }
    case kTopDarjeelingPlicPeripheralMbxJtag: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbxJtagMbxReady;
      break;
    }
    case kTopDarjeelingPlicPeripheralMbxPcie0: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbxPcie0MbxReady;
      break;
    }
    case kTopDarjeelingPlicPeripheralMbxPcie1: {
      plic_periph_base_irq_id = kTopDarjeelingPlicIrqIdMbxPcie1MbxReady;
      break;
    }
    default: {
      CHECK(false,
            "get_lowest_irq() called for a plic_irq_id that is not a mailbox!");
      return 0;
    }
  }  // switch(peripheral)

  return plic_periph_base_irq_id;
}

////////////////////////
// CONFIGURE MEMORIES //
////////////////////////

enum {
  kSramStart = TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_BASE_ADDR,
  kSramEnd = TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_BASE_ADDR +
             TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_SIZE_BYTES,
  kMbxSizeDWORDS = 8,  // The size we are allocating to each mbx for this test
                       // (imbx + ombx == kMbxSizeDWORDS * 2)
};

static_assert(
    NUM_MBXS * (kMbxSizeDWORDS * 2) <=
        (kSramEnd - kSramStart) / sizeof(uint32_t),
    "As specified, the mailbox memories cannot fit in the backing SRAM!");

// Backing storage for objects used by the mailbox handler(s)
// (dif_mbx_transaction_t)
static uint32_t gDataDWORDS[NUM_MBXS][kMbxSizeDWORDS];

/**
 * Setup the mailbox CSRs
 *
 * - Setup imbx/ombx base+limit addresses to match SoC memory
 * - Other misc init tasks (addr_range_valid, etc)
 */
void configure_mbx_peripherals(void) {
  uint32_t mbx_size_bytes = kMbxSizeDWORDS * sizeof(uint32_t);

  for (size_t i = 0; i < NUM_MBXS; ++i) {
    uint32_t mbx_region_base = kSramStart + (mbx_size_bytes * 2 * i);
    // Set the memory ranges
    dif_mbx_range_config_t config = {
        .imbx_base_addr = mbx_region_base,
        .imbx_limit_addr =  // limit_addr is _inclusive_, hence (sizeW - 1)
        mbx_region_base + mbx_size_bytes - sizeof(uint32_t),
        .ombx_base_addr = mbx_region_base + mbx_size_bytes,
        .ombx_limit_addr =
            mbx_region_base + (mbx_size_bytes * 2) - sizeof(uint32_t),
    };
    // This DIF also writes the bit indicating the range configuration is valid.
    CHECK_DIF_OK(dif_mbx_range_set(&gMbx[i], config));

    // Readback the range configuration registers, check they have been set as
    // expected.
    dif_mbx_range_config_t config_readback;
    CHECK_DIF_OK(dif_mbx_range_get(&gMbx[i], &config_readback));
    CHECK((config.imbx_base_addr == config_readback.imbx_base_addr) &&
          (config.imbx_limit_addr == config_readback.imbx_limit_addr) &&
          (config.ombx_base_addr == config_readback.ombx_base_addr) &&
          (config.ombx_limit_addr == config_readback.ombx_limit_addr));

    // Clear the control register.
    mmio_region_write32(gMbx[i].base_addr, MBX_CONTROL_REG_OFFSET, 0);
  }
}

/**
 * Initialize the global state that synchronizes the main_thread/ISR
 */
static void init_global_state(void) {
  for (size_t i = 0; i < NUM_MBXS; ++i) {
    // Initialize storage for mbx transaction objects
    gTxn[i].data_dwords = gDataDWORDS[i];
    // Create an initial snapshop of the pending interrupts
    dif_mbx_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_mbx_irq_get_state(&gMbx[i], &snapshot));
    CHECK(snapshot == 0,
          "No interrupts should be pending yet! (mbx[%0d].snapshot = 0x%0x)", i,
          snapshot);
    // Setup the state objects
    gHandlerState[i] =
        (struct mbx_test_handler_state){.mbx = &gMbx[i],
                                        .irq_state = snapshot,
                                        .txn = &gTxn[i],
                                        .txn_state = kStateIdle,
                                        .mbx_irq_serviced = kIrqVoid,
                                        .plic_irq_serviced = kIrqVoid};
  }
}

//////////////////////////
// CONFIGURE INTERRUPTS //
//////////////////////////

/**
 * Initialize the peripherals used in this test.
 *
 * - dif_*_init() for all peripherals
 */
static void init_peripherals(void) {
  mmio_region_t base_addr;

  base_addr = mmio_region_from_addr(TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(base_addr, &rv_core_ibex));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &rv_plic));
  base_addr =
      mmio_region_from_addr(TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_BASE_ADDR);
  CHECK_DIF_OK(dif_sram_ctrl_init(base_addr, &sram_ctrl_mbox));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX0_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[0]));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX1_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[1]));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX2_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[2]));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX3_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[3]));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX4_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[4]));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX5_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[5]));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX6_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[6]));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX_JTAG_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[7]));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX_PCIE0_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[8]));
  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX_PCIE1_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &gMbx[9]));

  // ADDITIONAL INITIALIZATION
  CHECK_DIF_OK(dif_sram_ctrl_scramble(
      &sram_ctrl_mbox));  // Scramble to initialize the memory with valid ECC
}

/**
 * Enable the interrupts required by this test.
 */
static void init_interrupts(void) {
  irq_global_ctrl(false);
  irq_external_ctrl(false);

  // Set Ibex IRQ priority threshold level to lowest (0)
  // - All IRQs with prio > 0 will not be masked
  CHECK_DIF_OK(
      dif_rv_plic_target_set_threshold(&rv_plic, kHart, kDifRvPlicMinPriority));

  // Enable IRQs at rv_plic
  // - enable
  // - set prio > 0
  for (size_t i = 0; i < ARRAYSIZE(irq_ids_rv_plic); ++i) {
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&rv_plic, irq_ids_rv_plic[i],
                                             kHart, kDifToggleEnabled));
    CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&rv_plic, irq_ids_rv_plic[i],
                                              kDifRvPlicMaxPriority));
  }
  // Enable IRQs at the periph
  for (size_t i = 0; i < NUM_MBXS; ++i) {
    for (size_t j = 0; j < ARRAYSIZE(mbx_irq_ids); ++j) {
      CHECK_DIF_OK(
          dif_mbx_irq_set_enabled(&gMbx[i], mbx_irq_ids[j], kDifToggleEnabled));
    }
  }

  irq_external_ctrl(true);
  irq_global_ctrl(true);
}

/**
 *  core.status.intr_status bit requires clearing separately to the standard
 *  'dif_*_acknowledge()' routines.
 *  This bit is 'W1C'.
 */
void clear_mbx_irq_pending(const dif_mbx_t *mbx) {
  uint32_t reg = mmio_region_read32(mbx->base_addr, MBX_STATUS_REG_OFFSET);
  reg = bitfield_bit32_write(reg, MBX_STATUS_SYS_INTR_STATE_BIT, 1u);
  mmio_region_write32(mbx->base_addr, MBX_STATUS_REG_OFFSET, reg);
}

/**
 * External ISR handler for this test.
 * (Our overridden ottf_external_isr() calls this function only.)
 *
 * - Claim the interrupt
 * - Check this irq_id is valid for this test
 * - Setup state in the global mbx_test_handler_state_t object
 *   - This allows the main thread (e.g. responder_mbx_transaction()) to
 * continue
 */
static status_t external_isr(void) {
  volatile mbx_test_handler_state_t *mbxths;
  dif_mbx_irq_t mbx_irq_id;
  dif_rv_plic_irq_id_t plic_irq_id;

  // (1) First, find which interrupt fired at PLIC by claiming it.
  TRY(dif_rv_plic_irq_claim(&rv_plic, kHart, &plic_irq_id));

  // Check the plic_irq is actually from a mailbox peripheral
  // This test currently cannot handle any other interrupts, as the logic/ISRs
  // are not sufficiently robust.
  CHECK(plic_irq_id >= kTopDarjeelingPlicIrqIdMbx0MbxReady &&
            plic_irq_id <= kTopDarjeelingPlicIrqIdMbxPcie1MbxError,
        "got an irq from a plic_peripheral that is not a mailbox!");

  // - Use lookup-tables (get_mbx_handler(), get_lowest_irq()) to find the
  // handles for
  //   objects relevant to the claimed irq.
  // - We don't use the isr_testutils ISR for this test
  //   - The 'mbx_ctx' argument requires a handle to a mbx object, but we don't
  //     know which handle to pass until claiming the irq, and calculating the
  //     peripheral it came from.
  //   - The autogenerated ISR would then claim the irq again, which may return
  //     a different plic_irq_id.
  mbx_irq_id = (dif_mbx_irq_t)(plic_irq_id - get_lowest_irq(plic_irq_id));
  top_darjeeling_plic_peripheral_t peripheral =
      (top_darjeeling_plic_peripheral_t)
          top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  mbxths = get_mbx_handler(peripheral);
  mbxths->mbx_irq_serviced = mbx_irq_id;
  mbxths->plic_irq_serviced = plic_irq_id;

  // Use the ctx_t types the autogenerated ISR takes as arguments, even
  // though we don't use that routine right now. Might be helpful later.
  plic_isr_ctx_t plic_ctx = {.rv_plic = &rv_plic, .hart_id = kHart};
  /* mbx_isr_ctx_t mbx_ctx = { */
  /*   .mbx = mbxths->mbx, */
  /*   .plic_mbx_start_irq_id = get_lowest_irq(plic_irq_id), */
  /*   .expected_irq = 0, */
  /*   .is_only_irq = false */
  /* }; */

  // (2) Handle the peripheral
  switch (mbx_irq_id) {
    case kDifMbxIrqMbxReady: {
      // First, mask the interrupt
      // - The interrupt will not be de-asserted by the peripheral until the
      // requester
      //   drains the response from the ombx. Until then, it cannot be cleared.
      // - The main thread will subsequently poll for the de-assertion of the
      // status.busy to determine when this occurs.
      CHECK_DIF_OK(dif_mbx_irq_set_enabled(
          mbxths->mbx, mbxths->mbx_irq_serviced, kDifToggleDisabled));
      CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
          plic_ctx.rv_plic, mbxths->plic_irq_serviced, plic_ctx.hart_id,
          kDifToggleDisabled));

      // Read message from imbx memory region
      CHECK_DIF_OK(dif_mbx_process_request(mbxths->mbx, mbxths->txn));
      mbxths->txn_state = kStateReceivedRequest;

      break;
    }
    case kDifMbxIrqMbxAbort: {
      CHECK(false, "Saw kDifMbxIrqMbxAbort, should not occur in this test!");
      break;
    }
    case kDifMbxIrqMbxError: {
      CHECK(false, "Saw kDifMbxIrqMbxError, should not occur in this test!");
      break;
    }
    default: {
      CHECK(false, "Invalid mbx_irq_id: %d", mbx_irq_id);
      break;
    }
  }

  // (3) Clear the IRQ at the peripheral and at the PLIC.
  // - This section is lifted from the end of the isr_testutils autgenerated
  // handler
  // - Only the plic_irq_complete() routine matters, since we cannot-yet clear
  // the
  //   INTR_STATE reg at the mbx as the event input is still asserted.

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  dif_irq_type_t type;
  CHECK_DIF_OK(
      dif_mbx_irq_get_type(mbxths->mbx, mbxths->mbx_irq_serviced, &type));
  if (type == kDifIrqTypeEvent) {
    CHECK_DIF_OK(
        dif_mbx_irq_acknowledge(mbxths->mbx, mbxths->mbx_irq_serviced));
  }
  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(plic_ctx.rv_plic, plic_ctx.hart_id,
                                        mbxths->plic_irq_serviced));

  // Set the boolean which allows wfi_flag() to retun.
  is_finished = true;

  return OK_STATUS();
}

static volatile status_t isr_result;
/* This overrides the weak-symbol for ottf_external_isr() */
void ottf_external_isr(void) {
  status_t tmp = external_isr();
  if (status_ok(isr_result)) {
    isr_result = tmp;
  }
}

/**
 * This looks a bit odd, but is needed to avoid a race condition where the
 * interrupt comes in after we load the flag but before we run the WFI
 * instruction.
 * The trick is that WFI returns when an interrupt comes in, even if
 * interrupts are globally disabled, which means that the WFI can actually
 * sit __inside__ the critical section.
 */
void wfi_flag(volatile bool *is_finished) {
  while (true) {
    irq_global_ctrl(false);
    if (*is_finished) {
      *is_finished = false;
      break;
    }
    wait_for_interrupt();
    irq_global_ctrl(true);
  }
  irq_global_ctrl(true);
}

//////////
// TEST //
//////////

/**
 * Perform a basic 'responder' role of the mbx transaction.
 * This test simply responds with the same message as the request, but with
 * all DWORDS incremented by 1.
 *
 * Request
 * - SoC-Side writes data into mbx and sets Go.
 * - Wait for interrupt on the core-side
 * - Read message from imbx memory region
 * Response
 * - Write message back into ombx memory region (and set the object-size)
 * - Poll/Wait for interrupt on soc-side
 * - Read each word from the soc.RDATA register (then write to ack-it)
 */
void responder_mbx_transaction(volatile mbx_test_handler_state_t *mbxths) {
  mbxths->txn_state = kStateGeneratingResponse;

  // Send the response to the requester
  // - Create new data for the outbound message
  increment_array_uint32(mbxths->txn->data_dwords, mbxths->txn->nr_dwords);
  CHECK_DIF_OK(dif_mbx_generate_response(mbxths->mbx, *mbxths->txn));

  mbxths->txn_state = kStateWaitingForResponseDrained;

  {  // Poll the mbx until it reports not-busy.
    bool is_busy = true;
    while (is_busy) {
      CHECK_DIF_OK(dif_mbx_is_busy(mbxths->mbx, &is_busy));
    }
  }
  // This indicates the requester has consumed our message from the ombx.
  // - Only at this point is it now possible to clear the 'ready' interrupt.

  mbxths->txn_state = kStateCleaningUp;

  // Clear the pending 'ready' interrupt now that the ombx is empty.
  // Then we can re-enable the interrupt at the plic.
  clear_mbx_irq_pending(
      mbxths->mbx);  // Clears the special status.DOE_interrupt_status bit
  CHECK_DIF_OK(dif_mbx_irq_acknowledge(mbxths->mbx, kDifMbxIrqMbxReady));
  // Un-mask the interrupt.
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&rv_plic, mbxths->plic_irq_serviced,
                                           kHart, kDifToggleEnabled));
  CHECK_DIF_OK(dif_mbx_irq_set_enabled(mbxths->mbx, mbxths->mbx_irq_serviced,
                                       kDifToggleEnabled));

  mbxths->mbx_irq_serviced = kIrqVoid;
  mbxths->plic_irq_serviced = kIrqVoid;
  mbxths->txn_state = kStateIdle;
}

bool test_main(void) {
  init_peripherals();
  configure_mbx_peripherals();
  init_interrupts();
  init_global_state();

  LOG_INFO("init_complete");

  // Wait for the testbench to set the number of transactions
  IBEX_SPIN_FOR(kSoftwareBarrier == 1, kSoftwareBarrierTimeoutUsec);
  size_t numTxns = kNumTxns;
  LOG_INFO("sw will await %0d transactions before ending the test.", numTxns);

  LOG_INFO("received_tb_cfg");

  // Respond to transaction requests from the tb.
  for (size_t i = 0; i < numTxns; ++i) {
    size_t mbxId = UINT32_MAX;
    bool got_mbxId = false;

    // Loop WFI->ISR->WFI->etc. until 'is_finished' is set true
    // Use this to only advance iff our ISR sets it
    wfi_flag(&is_finished);

    // Find which mbx received the request
    for (size_t i = 0; i < NUM_MBXS; ++i) {
      if (gHandlerState[i].txn_state == kStateReceivedRequest) {
        if (got_mbxId) {
          // This test should only have one mailbox transaction (req+rsp) in
          // flight at a time. The test is designed with this limitation in
          // mind, and the sw is not robust to handling multiple in-flight
          // transactions.
          CHECK(false,
                "After ISR set 'is_finished', multiple mbx's had received "
                "requests.");
        } else {
          got_mbxId = true;
          mbxId = i;
        }
      }
    }
    if (!got_mbxId || (mbxId == UINT32_MAX)) {
      // Should not be possible to return from the WFI loop and then fail this
      // check.
      CHECK(false, "Something went wrong. Aborting test.");
    }

    // Complete the txn
    LOG_INFO("Test sw responding to pending request in mbx[%0d]", mbxId);
    responder_mbx_transaction(&gHandlerState[mbxId]);
  }

  LOG_INFO("End of test.");

  return true;
}
