// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_mbx.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "mbx_regs.h"  // Generated

OTTF_DEFINE_TEST_CONFIG();

enum {
  kHart = 0,
  kIrqVoid = UINT32_MAX,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_sram_ctrl_t sram_ctrl_mbox;
static dif_rv_plic_t rv_plic;

static dif_mbx_t gMbx[kDtMbxCount];
static dif_mbx_transaction_t gTxn[kDtMbxCount];

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
static volatile mbx_test_handler_state_t gHandlerState[kDtMbxCount];
static volatile bool is_finished;

// CONSTANTS
static const dif_mbx_irq_t mbx_irq_ids[] = {
    kDtMbxIrqMbxReady, kDtMbxIrqMbxAbort, kDtMbxIrqMbxError};

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
    kDtMbxCount * (kMbxSizeDWORDS * 2) <=
        (kSramEnd - kSramStart) / sizeof(uint32_t),
    "As specified, the mailbox memories cannot fit in the backing SRAM!");

// Backing storage for objects used by the mailbox handler(s)
// (dif_mbx_transaction_t)
static uint32_t gDataDWORDS[kDtMbxCount][kMbxSizeDWORDS];

/**
 * Setup the mailbox CSRs
 *
 * - Setup imbx/ombx base+limit addresses to match SoC memory
 * - Other misc init tasks (addr_range_valid, etc)
 */
void configure_mbx_peripherals(void) {
  uint32_t mbx_size_bytes = kMbxSizeDWORDS * sizeof(uint32_t);

  for (dt_mbx_t mbx = 0; mbx < kDtMbxCount; mbx++) {
    uint32_t mbx_region_base = kSramStart + (mbx_size_bytes * 2 * mbx);
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
    CHECK_DIF_OK(dif_mbx_range_set(&gMbx[mbx], config));

    // Readback the range configuration registers, check they have been set as
    // expected.
    dif_mbx_range_config_t config_readback;
    CHECK_DIF_OK(dif_mbx_range_get(&gMbx[mbx], &config_readback));
    CHECK((config.imbx_base_addr == config_readback.imbx_base_addr) &&
          (config.imbx_limit_addr == config_readback.imbx_limit_addr) &&
          (config.ombx_base_addr == config_readback.ombx_base_addr) &&
          (config.ombx_limit_addr == config_readback.ombx_limit_addr));

    // Clear the control register.
    mmio_region_write32(gMbx[mbx].base_addr, MBX_CONTROL_REG_OFFSET, 0);
  }
}

/**
 * Initialize the global state that synchronizes the main_thread/ISR
 */
static void init_global_state(void) {
  for (dt_mbx_t mbx = 0; mbx < kDtMbxCount; mbx++) {
    // Initialize storage for mbx transaction objects
    gTxn[mbx].data_dwords = gDataDWORDS[mbx];
    // Create an initial snapshop of the pending interrupts
    dif_mbx_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_mbx_irq_get_state(&gMbx[mbx], &snapshot));
    CHECK(snapshot == 0,
          "No interrupts should be pending yet! (mbx[%0d].snapshot = 0x%0x)",
          mbx, snapshot);
    // Setup the state objects
    gHandlerState[mbx] =
        (struct mbx_test_handler_state){.mbx = &gMbx[mbx],
                                        .irq_state = snapshot,
                                        .txn = &gTxn[mbx],
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
 */
static void init_peripherals(void) {
  CHECK_DIF_OK(dif_rv_core_ibex_init_from_dt(kDtRvCoreIbex, &rv_core_ibex));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kDtRvPlic, &rv_plic));
  CHECK_DIF_OK(dif_sram_ctrl_init_from_dt(kDtSramCtrlMbox, &sram_ctrl_mbox));

  for (dt_mbx_t mbx = 0; mbx < kDtMbxCount; mbx++) {
    CHECK_DIF_OK(dif_mbx_init_from_dt(mbx, &gMbx[mbx]));
  }

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

  // Enable each IRQ for each mailbox at the PLIC and the mailbox itself.
  for (dt_mbx_t mbx = 0; mbx < kDtMbxCount; mbx++) {
    for (int i = 0; i < ARRAYSIZE(mbx_irq_ids); i++) {
      dt_plic_irq_id_t plic_id = dt_mbx_irq_to_plic_id(mbx, mbx_irq_ids[i]);

      CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&rv_plic, plic_id, kHart,
                                               kDifToggleEnabled));
      CHECK_DIF_OK(dif_rv_plic_irq_set_priority(&rv_plic, plic_id,
                                                kDifRvPlicMaxPriority));
      CHECK_DIF_OK(dif_mbx_irq_set_enabled(&gMbx[mbx], mbx_irq_ids[i],
                                           kDifToggleEnabled));
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
  dif_rv_plic_irq_id_t plic_irq_id;

  // (1) First, find which interrupt fired at PLIC by claiming it.
  TRY(dif_rv_plic_irq_claim(&rv_plic, kHart, &plic_irq_id));

  // Check the plic_irq is actually from a mailbox peripheral
  // This test currently cannot handle any other interrupts, as the logic/ISRs
  // are not sufficiently robust.
  dt_instance_id_t inst_id = dt_plic_id_to_instance_id(plic_irq_id);
  dt_device_type_t device_type = dt_device_type(inst_id);
  CHECK(device_type == kDtDeviceTypeMbx,
        "got an irq from a plic_peripheral that is not a mailbox!");

  dt_mbx_t mbx = dt_mbx_from_instance_id(inst_id);
  dif_mbx_irq_t mbx_irq_id = dt_mbx_irq_from_plic_id(mbx, plic_irq_id);

  mbxths = &gHandlerState[mbx];
  mbxths->mbx_irq_serviced = mbx_irq_id;
  mbxths->plic_irq_serviced = plic_irq_id;

  // (2) Handle the peripheral
  switch (mbx_irq_id) {
    case kDtMbxIrqMbxReady: {
      // First, mask the interrupt
      // - The interrupt will not be de-asserted by the peripheral until the
      // requester
      //   drains the response from the ombx. Until then, it cannot be cleared.
      // - The main thread will subsequently poll for the de-assertion of the
      // status.busy to determine when this occurs.
      CHECK_DIF_OK(dif_mbx_irq_set_enabled(
          mbxths->mbx, mbxths->mbx_irq_serviced, kDifToggleDisabled));
      CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
          &rv_plic, mbxths->plic_irq_serviced, kHart, kDifToggleDisabled));

      // Read message from imbx memory region
      CHECK_DIF_OK(dif_mbx_process_request(mbxths->mbx, mbxths->txn));
      mbxths->txn_state = kStateReceivedRequest;

      break;
    }
    case kDtMbxIrqMbxAbort: {
      CHECK(false, "Saw kDifMbxIrqMbxAbort, should not occur in this test!");
      break;
    }
    case kDtMbxIrqMbxError: {
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
  CHECK_DIF_OK(
      dif_rv_plic_irq_complete(&rv_plic, kHart, mbxths->plic_irq_serviced));

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
    dt_mbx_t mbx_id;
    bool got_mbx_id = false;

    // Loop WFI->ISR->WFI->etc. until 'is_finished' is set true
    // Use this to only advance iff our ISR sets it
    ATOMIC_WAIT_FOR_INTERRUPT(is_finished);

    // Find which mbx received the request
    for (dt_mbx_t mbx = 0; mbx < kDtMbxCount; mbx++) {
      if (gHandlerState[mbx].txn_state == kStateReceivedRequest) {
        if (got_mbx_id) {
          // This test should only have one mailbox transaction (req+rsp) in
          // flight at a time. The test is designed with this limitation in
          // mind, and the sw is not robust to handling multiple in-flight
          // transactions.
          CHECK(false,
                "After ISR set 'is_finished', multiple mbx's had received "
                "requests.");
        } else {
          got_mbx_id = true;
          mbx_id = mbx;
        }
      }
    }
    if (!got_mbx_id) {
      // Should not be possible to return from the WFI loop and then fail this
      // check.
      CHECK(false, "Something went wrong. Aborting test.");
    }

    // Complete the txn
    LOG_INFO("Test sw responding to pending request in mbx[%0d]", mbx_id);
    responder_mbx_transaction(&gHandlerState[mbx_id]);
  }

  LOG_INFO("End of test.");

  return true;
}
