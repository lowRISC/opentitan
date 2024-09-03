// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * This test consists of multiple parts:
 *   - First, the test controller configures the UDID and the Message command
 *     value (a "register" address of sorts).
 *   - Then, the test controller sets kTestInitDone to indicate that
 *     initialization via the ujson command processor is complete.
 *   - Next, the test controller issues SMBus ARP commands to configure the
 *     DUT's secondary I2C address. Currently, the PEC is neither generated
 *     nor checked, but the DUT stretches on the PEC byte so it looks like it
 *     checks. Plus, it gets time to assign the new address.
 *   - Finally, the test controller issues a write to the Message register, and
 *     the DUT writes the value. Then the test controller issue a read to the
 *     Message register, and the DUT responds with the current value. The test
 *     passes if the host successfully communicates and receives this value.
 */
#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

enum {
  kArpCmdPrepareToArp = 0x01,
  kArpCmdResetDevice = 0x02,
  kArpCmdGetUdid = 0x03,
  kArpCmdAssignAddress = 0x04,
};

static const uint8_t pec_lut[256] = {
    [0x00] = 0x00, [0x01] = 0x07, [0x02] = 0x0e, [0x03] = 0x09, [0x04] = 0x1c,
    [0x05] = 0x1b, [0x06] = 0x12, [0x07] = 0x15, [0x08] = 0x38, [0x09] = 0x3f,
    [0x0a] = 0x36, [0x0b] = 0x31, [0x0c] = 0x24, [0x0d] = 0x23, [0x0e] = 0x2a,
    [0x0f] = 0x2d, [0x10] = 0x70, [0x11] = 0x77, [0x12] = 0x7e, [0x13] = 0x79,
    [0x14] = 0x6c, [0x15] = 0x6b, [0x16] = 0x62, [0x17] = 0x65, [0x18] = 0x48,
    [0x19] = 0x4f, [0x1a] = 0x46, [0x1b] = 0x41, [0x1c] = 0x54, [0x1d] = 0x53,
    [0x1e] = 0x5a, [0x1f] = 0x5d, [0x20] = 0xe0, [0x21] = 0xe7, [0x22] = 0xee,
    [0x23] = 0xe9, [0x24] = 0xfc, [0x25] = 0xfb, [0x26] = 0xf2, [0x27] = 0xf5,
    [0x28] = 0xd8, [0x29] = 0xdf, [0x2a] = 0xd6, [0x2b] = 0xd1, [0x2c] = 0xc4,
    [0x2d] = 0xc3, [0x2e] = 0xca, [0x2f] = 0xcd, [0x30] = 0x90, [0x31] = 0x97,
    [0x32] = 0x9e, [0x33] = 0x99, [0x34] = 0x8c, [0x35] = 0x8b, [0x36] = 0x82,
    [0x37] = 0x85, [0x38] = 0xa8, [0x39] = 0xaf, [0x3a] = 0xa6, [0x3b] = 0xa1,
    [0x3c] = 0xb4, [0x3d] = 0xb3, [0x3e] = 0xba, [0x3f] = 0xbd, [0x40] = 0xc7,
    [0x41] = 0xc0, [0x42] = 0xc9, [0x43] = 0xce, [0x44] = 0xdb, [0x45] = 0xdc,
    [0x46] = 0xd5, [0x47] = 0xd2, [0x48] = 0xff, [0x49] = 0xf8, [0x4a] = 0xf1,
    [0x4b] = 0xf6, [0x4c] = 0xe3, [0x4d] = 0xe4, [0x4e] = 0xed, [0x4f] = 0xea,
    [0x50] = 0xb7, [0x51] = 0xb0, [0x52] = 0xb9, [0x53] = 0xbe, [0x54] = 0xab,
    [0x55] = 0xac, [0x56] = 0xa5, [0x57] = 0xa2, [0x58] = 0x8f, [0x59] = 0x88,
    [0x5a] = 0x81, [0x5b] = 0x86, [0x5c] = 0x93, [0x5d] = 0x94, [0x5e] = 0x9d,
    [0x5f] = 0x9a, [0x60] = 0x27, [0x61] = 0x20, [0x62] = 0x29, [0x63] = 0x2e,
    [0x64] = 0x3b, [0x65] = 0x3c, [0x66] = 0x35, [0x67] = 0x32, [0x68] = 0x1f,
    [0x69] = 0x18, [0x6a] = 0x11, [0x6b] = 0x16, [0x6c] = 0x03, [0x6d] = 0x04,
    [0x6e] = 0x0d, [0x6f] = 0x0a, [0x70] = 0x57, [0x71] = 0x50, [0x72] = 0x59,
    [0x73] = 0x5e, [0x74] = 0x4b, [0x75] = 0x4c, [0x76] = 0x45, [0x77] = 0x42,
    [0x78] = 0x6f, [0x79] = 0x68, [0x7a] = 0x61, [0x7b] = 0x66, [0x7c] = 0x73,
    [0x7d] = 0x74, [0x7e] = 0x7d, [0x7f] = 0x7a, [0x80] = 0x89, [0x81] = 0x8e,
    [0x82] = 0x87, [0x83] = 0x80, [0x84] = 0x95, [0x85] = 0x92, [0x86] = 0x9b,
    [0x87] = 0x9c, [0x88] = 0xb1, [0x89] = 0xb6, [0x8a] = 0xbf, [0x8b] = 0xb8,
    [0x8c] = 0xad, [0x8d] = 0xaa, [0x8e] = 0xa3, [0x8f] = 0xa4, [0x90] = 0xf9,
    [0x91] = 0xfe, [0x92] = 0xf7, [0x93] = 0xf0, [0x94] = 0xe5, [0x95] = 0xe2,
    [0x96] = 0xeb, [0x97] = 0xec, [0x98] = 0xc1, [0x99] = 0xc6, [0x9a] = 0xcf,
    [0x9b] = 0xc8, [0x9c] = 0xdd, [0x9d] = 0xda, [0x9e] = 0xd3, [0x9f] = 0xd4,
    [0xa0] = 0x69, [0xa1] = 0x6e, [0xa2] = 0x67, [0xa3] = 0x60, [0xa4] = 0x75,
    [0xa5] = 0x72, [0xa6] = 0x7b, [0xa7] = 0x7c, [0xa8] = 0x51, [0xa9] = 0x56,
    [0xaa] = 0x5f, [0xab] = 0x58, [0xac] = 0x4d, [0xad] = 0x4a, [0xae] = 0x43,
    [0xaf] = 0x44, [0xb0] = 0x19, [0xb1] = 0x1e, [0xb2] = 0x17, [0xb3] = 0x10,
    [0xb4] = 0x05, [0xb5] = 0x02, [0xb6] = 0x0b, [0xb7] = 0x0c, [0xb8] = 0x21,
    [0xb9] = 0x26, [0xba] = 0x2f, [0xbb] = 0x28, [0xbc] = 0x3d, [0xbd] = 0x3a,
    [0xbe] = 0x33, [0xbf] = 0x34, [0xc0] = 0x4e, [0xc1] = 0x49, [0xc2] = 0x40,
    [0xc3] = 0x47, [0xc4] = 0x52, [0xc5] = 0x55, [0xc6] = 0x5c, [0xc7] = 0x5b,
    [0xc8] = 0x76, [0xc9] = 0x71, [0xca] = 0x78, [0xcb] = 0x7f, [0xcc] = 0x6a,
    [0xcd] = 0x6d, [0xce] = 0x64, [0xcf] = 0x63, [0xd0] = 0x3e, [0xd1] = 0x39,
    [0xd2] = 0x30, [0xd3] = 0x37, [0xd4] = 0x22, [0xd5] = 0x25, [0xd6] = 0x2c,
    [0xd7] = 0x2b, [0xd8] = 0x06, [0xd9] = 0x01, [0xda] = 0x08, [0xdb] = 0x0f,
    [0xdc] = 0x1a, [0xdd] = 0x1d, [0xde] = 0x14, [0xdf] = 0x13, [0xe0] = 0xae,
    [0xe1] = 0xa9, [0xe2] = 0xa0, [0xe3] = 0xa7, [0xe4] = 0xb2, [0xe5] = 0xb5,
    [0xe6] = 0xbc, [0xe7] = 0xbb, [0xe8] = 0x96, [0xe9] = 0x91, [0xea] = 0x98,
    [0xeb] = 0x9f, [0xec] = 0x8a, [0xed] = 0x8d, [0xee] = 0x84, [0xef] = 0x83,
    [0xf0] = 0xde, [0xf1] = 0xd9, [0xf2] = 0xd0, [0xf3] = 0xd7, [0xf4] = 0xc2,
    [0xf5] = 0xc5, [0xf6] = 0xcc, [0xf7] = 0xcb, [0xf8] = 0xe6, [0xf9] = 0xe1,
    [0xfa] = 0xe8, [0xfb] = 0xef, [0xfc] = 0xfa, [0xfd] = 0xfd, [0xfe] = 0xf4,
    [0xff] = 0xf3,
};

static dif_pinmux_t pinmux;
static dif_rv_plic_t plic;
static dif_i2c_t i2c;

/** The UDID for SMBus ARP purposes. Configured by ujson command. */
volatile uint8_t kSmbusUdid[16] = {0};

/**
 * Message command/address value (for the function on the dynamically-configured
 * I2C address). Configured by ujson command.
 *
 * Two commands come from this address:
 *   - Write Message Register:
 *     S - A/Wr - kMessageAddr - data[0] - data[1] - ... - P
 *   - Read Message Register:
 *     S - A/Wr - kMessageAddr - Sr - A/Rd - data[0] - data[1] - ... - P
 */
volatile uint32_t kMessageAddr = 0;

/** Test ready indication. Configured by ujson command. */
volatile uint32_t kTestInitDone = 0;

typedef enum i2c_state {
  kI2cStateIdle = 0,
  /** Waiting to check the PEC for a pending ARP command. */
  kI2cStateArpPec,
  /** Waiting for the Read transfer to begin after decoding Get UDID. */
  kI2cStateArpGetUdidWait,
  /** Waiting to complete transmission of the Get UDID response. */
  kI2cStateArpGetUdidTransmit,
  /** Waiting to check the complete UDID for an Assign Address command. */
  kI2cStateArpCheckUdid,
  /**
   * Waiting for either a block length to write or a repeated start for the
   * Message register commands.
   */
  kI2cStateMessageWait,
  /**
   * Waiting to receive the complete message to be written to the Message
   * register.
   */
  kI2cStateMessageReceive,
  /** Waiting to complete transmission of the Message register contents. */
  kI2cStateMessageTransmit,
  /** Waiting for the Stop after the Message register read. */
  kI2cStateMessageFinish,
  /** Waiting for the PEC and Stop for Assign Address. */
  kI2cStateAssignAddressComplete,
  /** Waiting for the transaction to complete (with NACK). */
  kI2cStateTransactionNack,
} i2c_state_t;

// Current running PEC.
static uint8_t running_pec;

// SMBus ARP flags
static bool arp_av = false;
static bool arp_ar = false;

// Which ARP command is currently being processed. 0 is reserved.
static uint8_t arp_cmd_pending = 0;

// The SMBus ARP address.
static const dif_i2c_id_t kSmbusArpId = {
    .address = 0x61,
    .mask = 0x7f,
};

// The dynamic address. To be assigned by SMBus ARP.
static dif_i2c_id_t i2c_id = {
    .address = 0x7f,
    .mask = 0x7f,
};

// The enables get saved by the ISR, then restored in normal context.
static volatile dif_i2c_irq_enable_snapshot_t i2c_irq_enables;

// This gets set in the ISR and reset in normal context. It's used to indcate
// that the I2C routine needs to do some processing.
static volatile bool i2c_event = false;

// Current state of the I2C processing state machine.
static i2c_state_t state;

/**
 * A message scratch register assigned to the function on the
 * dynamically-configured address.
 */
static uint8_t message[32];

/**
 * Process i2c interrupts. Only a few interrupts should ever occur during this
 * test. All work is deferred to the bottom half.
 */
void i2c_isr(dif_i2c_irq_t irq) {
  switch (irq) {
    case kDifI2cIrqFmtThreshold:
    case kDifI2cIrqRxThreshold:
    case kDifI2cIrqTxThreshold:
    case kDifI2cIrqRxOverflow:
    case kDifI2cIrqControllerHalt:
    case kDifI2cIrqSclInterference:
    case kDifI2cIrqSdaInterference:
    case kDifI2cIrqStretchTimeout:
    case kDifI2cIrqSdaUnstable:
    case kDifI2cIrqUnexpStop:
    case kDifI2cIrqHostTimeout:
      CHECK(false, "Unexpected I2C IRQ %d", irq);
      break;
    case kDifI2cIrqAcqThreshold:
    case kDifI2cIrqCmdComplete:
    case kDifI2cIrqTxStretch:
    case kDifI2cIrqAcqStretch:
      i2c_event = true;
      break;
    default:
      CHECK(false, "invalid interrupt %d", irq);
  }
  dif_i2c_irq_enable_snapshot_t enables;
  CHECK_DIF_OK(dif_i2c_irq_disable_all(&i2c, &enables));
  i2c_irq_enables = enables;
}

/**
 * External interrupt handler.
 */
void ottf_external_isr(uint32_t *exc_info) {
  const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
  dif_rv_plic_irq_id_t plic_irq_id = 0;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kPlicTarget, &plic_irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  switch (peripheral) {
    case kTopEarlgreyPlicPeripheralUart0:
      if (!ottf_console_flow_control_isr(exc_info)) {
        goto unexpected_irq;
      };
      break;
    case kTopEarlgreyPlicPeripheralI2c0: {
      // Check that the ID matches the expected interrupt, then mask it, since
      // it's a status type.
      dif_i2c_irq_t irq =
          (dif_i2c_irq_t)(plic_irq_id - kTopEarlgreyPlicIrqIdI2c0FmtThreshold);
      i2c_isr(irq);
    } break;
    default:
      goto unexpected_irq;
  }

  // Complete the IRQ at PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kPlicTarget, plic_irq_id));
  return;

  // A label to jump to for common error handling.
unexpected_irq:
  CHECK(false, "Unexpected external IRQ %d", plic_irq_id);
}

/** This is only used during test initialization. */
static status_t command_processor(ujson_t *uj) {
  while (!kTestInitDone) {
    test_command_t command;
    TRY(UJSON_WITH_CRC(ujson_deserialize_test_command_t, uj, &command));
    status_t status = ujson_ottf_dispatch(uj, command);
    if (status_err(status) == kUnimplemented) {
      RESP_ERR(uj, status);
    } else if (status_err(status) != kOk) {
      return status;
    }
  }
  return OK_STATUS();
}

static status_t test_init(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  TRY(dif_pinmux_init(base_addr, &pinmux));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  TRY(dif_rv_plic_init(base_addr, &plic));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR);
  TRY(dif_i2c_init(base_addr, &i2c));

  TRY(i2c_testutils_select_pinmux(&pinmux, 0, I2cPinmuxPlatformIdHyper310));
  TRY(i2c_testutils_set_speed(&i2c, kDifI2cSpeedStandard));

  // 25 ms bus timeout. The upper limit of support is ~1 GHz for the IP, so OK
  // to make the frequency a uint32_t.
  uint32_t kBusTimeoutCycles = ((uint32_t)kClockFreqPeripheralHz / (1000 / 25));
  TRY(dif_i2c_enable_clock_timeout(&i2c, kDifI2cSclTimeoutBus,
                                   kBusTimeoutCycles));

  // 50 us bus idle timeout.
  uint32_t kIdleCycles = ((uint32_t)kClockFreqPeripheralHz / (1000000 / 50));
  TRY(dif_i2c_set_host_timeout(&i2c, kIdleCycles));

  // Enable TX stretch controls. Stale TX data should not be left in the FIFO.
  // This test shouldn't actually run into the scenario for which these controls
  // were created, but it still handles the mechanisms that guard against it.
  TRY(dif_i2c_target_tx_stretch_ctrl_set_enabled(&i2c, kDifToggleEnabled));

  // Enable N-byte ACK control.
  TRY(dif_i2c_ack_ctrl_set_enabled(&i2c, kDifToggleEnabled));
  TRY(dif_i2c_reset_tx_fifo(&i2c));
  TRY(dif_i2c_reset_acq_fifo(&i2c));

  TRY(dif_i2c_set_target_watermarks(&i2c, /*tx_level=*/0,
                                    I2C_PARAM_ACQ_FIFO_DEPTH));
  TRY(dif_i2c_set_device_id(&i2c, &kSmbusArpId, NULL));
  TRY(dif_i2c_multi_controller_monitor_set_enabled(&i2c, kDifToggleEnabled));
  TRY(dif_i2c_device_set_enabled(&i2c, kDifToggleEnabled));

  // Enable all I2C interrupts.
  const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
  for (dif_i2c_irq_t irq = kDifI2cIrqFmtThreshold; irq <= kDifI2cIrqHostTimeout;
       ++irq) {
    CHECK_DIF_OK(dif_i2c_irq_set_enabled(&i2c, irq, kDifToggleEnabled));
  }
  rv_plic_testutils_irq_range_enable(&plic, kPlicTarget,
                                     kTopEarlgreyPlicIrqIdI2c0FmtThreshold,
                                     kTopEarlgreyPlicIrqIdI2c0HostTimeout);

  // Initialize the message buffer.
  memset(message, 0, sizeof(message));

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  ujson_t uj = ujson_ottf_console();
  TRY(command_processor(&uj));
  return OK_STATUS();
}

/**
 * Calculate the PEC / CRC-8, given the running and new values.
 */
static uint8_t calc_pec(uint8_t remainder, uint8_t next) {
  return pec_lut[remainder ^ next];
}

/**
 * This is the entry function for all new transactions that match one of our
 * addresses. This is the processing function for the kI2cStateIdle state.
 *
 * When we reach this state, the ACQ FIFO should have a single entry in it, the
 * address + rnw byte with a Start preceding it. In addition, the Target module
 * should be stretching on the first byte of the Write command, since the Auto
 * Ack Counter starts at 0 for every transfer. From here, we observe the pending
 * command byte and dispatch.
 */
static status_t process_new_command(dif_i2c_irq_state_snapshot_t irq_snapshot,
                                    dif_i2c_status_t i2c_status) {
  if (bitfield_bit32_read(irq_snapshot, kDifI2cIrqAcqStretch)) {
    TRY_CHECK(!i2c_status.acq_fifo_empty);

    uint8_t data;
    dif_i2c_signal_t signal;
    TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
    TRY_CHECK(signal == kDifI2cSignalStart);
    running_pec = 0;

    // All transactions to either address should begin with a write.
    TRY_CHECK((data & 0x1) == 0, "Expected a write command, but got read");
    TRY_CHECK(i2c_status.ack_ctrl_stretch);

    if ((data >> 1) == kSmbusArpId.address) {
      // Received an SMBus ARP command. Check what it is.
      uint8_t command;
      TRY(dif_i2c_get_pending_acq_byte(&i2c, &command));
      if (command == kArpCmdPrepareToArp) {
        arp_cmd_pending = command;
        state = kI2cStateArpPec;
        TRY(dif_i2c_set_auto_ack_count(&i2c, 2));
      } else if (command == kArpCmdResetDevice) {
        arp_cmd_pending = command;
        state = kI2cStateArpPec;
        TRY(dif_i2c_set_auto_ack_count(&i2c, 2));
      } else if (command == kArpCmdGetUdid) {
        if (arp_ar) {
          // NACK if AR is 0 for the general Get UDID command.
          state = kI2cStateTransactionNack;
          TRY(dif_i2c_nack_transaction(&i2c));
        } else {
          // Prepare to receive the beginning of the Read transfer.
          arp_cmd_pending = command;
          state = kI2cStateArpGetUdidWait;
          TRY(dif_i2c_set_auto_ack_count(&i2c, 1));
        }
      } else if (command == kArpCmdAssignAddress) {
        // Prepare to receive the Byte Count and UDID for targeting.
        // The spec is a bit unclear about whether we absolutely must stop at
        // every other byte and NACK a mismatch. We wait for the end of the UDID
        // here.
        arp_cmd_pending = command;
        state = kI2cStateArpCheckUdid;
        TRY(dif_i2c_set_auto_ack_count(&i2c, 17));
      } else if (command == ((i2c_id.address < 1) | 0)) {
        // This is the directed Reset device ARP command.
        if (arp_av) {
          arp_cmd_pending = kArpCmdResetDevice;
          state = kI2cStateArpPec;
          TRY(dif_i2c_set_auto_ack_count(&i2c, 2));
        } else {
          // i2c_id is actually not valid, so reject this command.
          state = kI2cStateTransactionNack;
          TRY(dif_i2c_nack_transaction(&i2c));
        }
      } else if (command == ((i2c_id.address < 1) | 1)) {
        // This is the directed Get UDID command.
        if (arp_av) {
          // Prepare to receive the beginning of the Read transfer.
          arp_cmd_pending = kArpCmdGetUdid;
          state = kI2cStateArpGetUdidWait;
          TRY(dif_i2c_set_auto_ack_count(&i2c, 1));
        } else {
          // NACK if AV is 0 for the general Get UDID command.
          state = kI2cStateTransactionNack;
          TRY(dif_i2c_nack_transaction(&i2c));
        }
      } else {
        state = kI2cStateTransactionNack;
        TRY(dif_i2c_nack_transaction(&i2c));
      }
    } else if (arp_av && ((data >> 1) == i2c_id.address)) {
      uint8_t command;
      TRY(dif_i2c_get_pending_acq_byte(&i2c, &command));
      if (command == (kMessageAddr & 0xffu)) {
        // We'll need to wait and see whether this is a write or the beginning
        // of a read.
        state = kI2cStateMessageWait;
        TRY(dif_i2c_set_auto_ack_count(&i2c, 1));
      } else {
        // Got an unsupported command. NACK the transaction.
        state = kI2cStateTransactionNack;
        TRY(dif_i2c_nack_transaction(&i2c));
      }
    } else {
      TRY_CHECK(false, "Unexpected 7-bit addr match: 0x%x", (data >> 1));
    }
  } else {
    TRY_CHECK(false, "Unexpected INTR_STATE=0x%x", irq_snapshot);
  }
  return OK_STATUS();
}

/**
 * This state is the final state for the Prepare to ARP and Reset Device
 * commands. They will have automatically ACK'd the 2 data bytes and the PEC
 * byte, and that means the Stop will have smoothly hit the ACQ FIFO with no
 * interruptions. These commands completely finish, and the FSM goes back to
 * Idle.
 *
 * The Assign Address command also passes through this state, but it's not the
 * final state for it. It did *not* automatically accept the PEC byte, so that
 * byte hasn't hit the ACQ FIFO yet. Instead, it is stopped here to check the
 * PEC byte, so it may decide whether to NACK the whole transaction.
 *
 * Upon entering this state, the Assign Address command will have already
 * validated the UDID when it had the last byte still pending. It would then
 * have set the Auto ACK Counter to ACK that last UDID byte *and* the new
 * address byte, so the ACQ FIFO should only have those two bytes in it. From
 * here, the Assign Address command will go to the AssignAddressComplete stage
 * or it would NACK (on a PEC failure).
 */
static status_t check_arp_pec(dif_i2c_irq_state_snapshot_t irq_snapshot,
                              dif_i2c_status_t i2c_status) {
  switch (arp_cmd_pending) {
    case kArpCmdPrepareToArp:
      TRY_CHECK(bitfield_bit32_read(irq_snapshot, kDifI2cIrqCmdComplete));
      TRY_CHECK(!i2c_status.acq_fifo_empty);

      // Check that the FIFO has the expected number of bytes, the command, the
      // PEC, and a Stop.
      dif_i2c_level_t acq_fifo_level;
      TRY(dif_i2c_get_fifo_levels(&i2c, NULL, NULL, NULL, &acq_fifo_level));
      TRY_CHECK(acq_fifo_level >= 3);

      // Pop the command byte. It should match.
      uint8_t data = 0;
      dif_i2c_signal_t signal;
      TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
      TRY_CHECK(signal == kDifI2cSignalNone);
      TRY_CHECK(data == arp_cmd_pending);
      running_pec = calc_pec(running_pec, data);

      // The next byte is the PEC.
      TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
      TRY_CHECK(signal == kDifI2cSignalNone);
      running_pec = calc_pec(running_pec, data);

      // Finally, there should be a Stop.
      TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
      TRY_CHECK(signal == kDifI2cSignalStop);

      TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));
      arp_cmd_pending = 0;
      state = kI2cStateIdle;
      TRY_CHECK(running_pec == 0, "PEC failure");
      arp_ar = false;
      break;
    case kArpCmdResetDevice: {
      TRY_CHECK(bitfield_bit32_read(irq_snapshot, kDifI2cIrqCmdComplete));
      TRY_CHECK(!i2c_status.acq_fifo_empty);

      // Check that the FIFO has the expected number of bytes, the command, the
      // PEC, and a Stop.
      dif_i2c_level_t acq_fifo_level;
      TRY(dif_i2c_get_fifo_levels(&i2c, NULL, NULL, NULL, &acq_fifo_level));
      TRY_CHECK(acq_fifo_level >= 3);

      // Pop the command byte. It should match.
      uint8_t data = 0;
      dif_i2c_signal_t signal;
      TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
      TRY_CHECK(signal == kDifI2cSignalNone);
      TRY_CHECK(data == arp_cmd_pending);
      running_pec = calc_pec(running_pec, data);

      // The next byte is the PEC.
      TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
      TRY_CHECK(signal == kDifI2cSignalNone);
      running_pec = calc_pec(running_pec, data);

      // Finally, there should be a Stop.
      TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
      TRY_CHECK(signal == kDifI2cSignalStop);

      TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));
      arp_cmd_pending = 0;
      state = kI2cStateIdle;
      TRY_CHECK(running_pec == 0, "PEC failure");
      arp_ar = false;
      arp_av = false;
    } break;
    case kArpCmdAssignAddress: {
      // For AssignAddress, we have validated the UDID, and the last byte of the
      // UDID and the new address should be in the ACQ FIFO. In addition, we
      // should be stopped on the PEC's ACK pending.
      TRY_CHECK(bitfield_bit32_read(irq_snapshot, kDifI2cIrqAcqStretch));
      TRY_CHECK(i2c_status.ack_ctrl_stretch);
      TRY_CHECK(!i2c_status.acq_fifo_empty);

      // Check that the FIFO has the expected number of bytes, the last byte of
      // the UDID and the proposed address. The Target module is waiting for us
      // to decide whether to ACK the PEC, so it's still pending.
      dif_i2c_level_t acq_fifo_level;
      TRY(dif_i2c_get_fifo_levels(&i2c, NULL, NULL, NULL, &acq_fifo_level));
      TRY_CHECK(acq_fifo_level >= 2);

      // Pop the last UDID byte and drop it.
      uint8_t data = 0;
      dif_i2c_signal_t signal;
      TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
      TRY_CHECK(signal == kDifI2cSignalNone);
      TRY_CHECK(data == kSmbusUdid[15]);
      running_pec = calc_pec(running_pec, data);

      // The next byte is the address.
      uint8_t new_address = 0;
      TRY(dif_i2c_acquire_byte(&i2c, &new_address, &signal));
      TRY_CHECK(signal == kDifI2cSignalNone);
      running_pec = calc_pec(running_pec, new_address);

      // Next would be the pending PEC.
      TRY(dif_i2c_get_pending_acq_byte(&i2c, &data));
      TRY_CHECK(running_pec == data, "PEC failure");

      i2c_id.address = new_address >> 1;
      TRY(dif_i2c_set_device_id(&i2c, &kSmbusArpId, &i2c_id));
      arp_ar = true;
      arp_av = true;
      state = kI2cStateAssignAddressComplete;
      TRY(dif_i2c_set_auto_ack_count(&i2c, 1));
      // arp_cmd_pending will be zeroed out in the finish state
    } break;
    default:
      TRY_CHECK(false, "Found unexpected arp_cmd_pending 0x%x",
                arp_cmd_pending);
      break;
  }
  return OK_STATUS();
}

/**
 * This function prepares the UDID response to be transmitted from the Target
 * on a Get UDID command. We will have reached this state after decoding the
 * command in process_command(), and the ACQ FIFO will have that byte inside.
 *
 * However, the CmdComplete interrupt doesn't coincide with the Restart byte
 * hitting the ACQ FIFO, so if we only have the CmdComplete interrupt and are
 * not stretching on the TX FIFO being empty, we only clear that interrupt and
 * remove the last byte of the Write command that completed.
 *
 * Once the Target module is stretching on the TX FIFO, we make sure the next
 * ACQ FIFO entry is a Restart that still targets this function, then proceed
 * to fill the TX FIFO with the data to be returned on the Read.
 *
 * The next state awaits the completion of the Read command, which should be via
 * a Stop.
 */
static status_t prepare_udid_reply(dif_i2c_irq_state_snapshot_t irq_snapshot,
                                   dif_i2c_status_t i2c_status) {
  TRY_CHECK(arp_cmd_pending == kArpCmdGetUdid);

  bool cmd_complete = bitfield_bit32_read(irq_snapshot, kDifI2cIrqCmdComplete);
  bool tx_stretch = bitfield_bit32_read(irq_snapshot, kDifI2cIrqTxStretch);
  if (cmd_complete) {
    // Should see the command byte still there.
    TRY_CHECK(!i2c_status.acq_fifo_empty);

    uint8_t data = 0;
    dif_i2c_signal_t signal;
    TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
    TRY_CHECK(signal == kDifI2cSignalNone);
    TRY_CHECK((data == ((i2c_id.address << 1) | 1)) ||
              (data == kArpCmdGetUdid));
    TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));

    if (!tx_stretch) {
      // Come back when we've reached the stretch. "Command complete" will
      // arrive before the FIFO has prepared the new command for the read.
      return OK_STATUS();
    }
  }
  TRY_CHECK(tx_stretch);
  TRY_CHECK(i2c_status.tx_fifo_empty);

  // Clear the TX pending bit.
  dif_i2c_target_tx_halt_events_t events = {0};
  TRY(dif_i2c_get_target_tx_halt_events(&i2c, &events));
  TRY_CHECK(events.tx_pending);
  TRY_CHECK(!events.bus_timeout);
  TRY(dif_i2c_clear_target_tx_halt_events(&i2c, events));

  // Should see a Restart with the read to the ARP default address here.
  uint8_t data = 0;
  dif_i2c_signal_t signal;
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalRepeat);
  TRY_CHECK(data == ((kSmbusArpId.address << 1) | 1));

  // First is the byte count.
  TRY(dif_i2c_transmit_byte(&i2c, sizeof(kSmbusUdid) + 1));
  uint8_t pec = calc_pec(0, sizeof(kSmbusUdid) + 1);

  // Next, transmit the UDID.
  for (size_t i = 0; i < sizeof(kSmbusUdid); ++i) {
    TRY(dif_i2c_transmit_byte(&i2c, kSmbusUdid[i]));
    pec = calc_pec(pec, kSmbusUdid[i]);
  }

  // Transmit the current address, if any.
  uint8_t current_address = 0xff;
  if (arp_av) {
    current_address = (uint8_t)((i2c_id.address << 1) | 1);
  }
  TRY(dif_i2c_transmit_byte(&i2c, current_address));
  pec = calc_pec(pec, current_address);

  // Then, transmit the PEC.
  TRY(dif_i2c_transmit_byte(&i2c, pec));
  state = kI2cStateArpGetUdidTransmit;
  return OK_STATUS();
}

/**
 * This state completes the Get UDID command. It expects to get the CmdComplete
 * interrupt and an accompanying Stop. Afterwards, the FSM proceeds to Idle.
 */
static status_t complete_get_udid(dif_i2c_irq_state_snapshot_t irq_snapshot,
                                  dif_i2c_status_t i2c_status) {
  TRY_CHECK(arp_cmd_pending == kArpCmdGetUdid);
  TRY_CHECK(bitfield_bit32_read(irq_snapshot, kDifI2cIrqCmdComplete));
  TRY_CHECK(!i2c_status.acq_fifo_empty);

  uint8_t data = 0;
  dif_i2c_signal_t signal;
  // There should only be a Stop next.
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalStop);

  // Make a superfluous check for lost arbitration. If arbitration were lost,
  // the ACQ FIFO would have kDifI2cSignalNackStop instead.
  dif_i2c_target_tx_halt_events_t events = {0};
  TRY(dif_i2c_get_target_tx_halt_events(&i2c, &events));
  TRY_CHECK(!events.tx_pending);
  TRY_CHECK(!events.bus_timeout);
  TRY_CHECK(!events.arbitration_lost);

  // Return to idle.
  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));
  arp_cmd_pending = 0;
  state = kI2cStateIdle;
  return OK_STATUS();
}

/**
 * This state is the next stop for Assign Address after command dispatch. We
 * will have set the Auto ACK Counter to ACK all bytes up to, but not including,
 * the last UDID byte. The Target module will be stretching on the ACK phase,
 * waiting for software to decide whether to ACK or NACK.
 *
 * We check the UDID and only ACK if all data matches the expectation. The last
 * byte of the UDID is in the pending area, not the ACQ FIFO. If everything
 * matches, we proceed to ACK the last UDID byte and the address assignment,
 * and the Target module will stop on the PEC byte. The next state is the PEC
 * check.
 */
static status_t check_received_udid(dif_i2c_irq_state_snapshot_t irq_snapshot,
                                    dif_i2c_status_t i2c_status) {
  TRY_CHECK(arp_cmd_pending == kArpCmdAssignAddress);
  TRY_CHECK(bitfield_bit32_read(irq_snapshot, kDifI2cIrqAcqStretch));
  TRY_CHECK(!i2c_status.acq_fifo_empty);

  // Check that the FIFO has the expected number of bytes, the command, the
  // byte count, and 15 of 16 UDID bytes.
  dif_i2c_level_t acq_fifo_level;
  TRY(dif_i2c_get_fifo_levels(&i2c, NULL, NULL, NULL, &acq_fifo_level));
  TRY_CHECK(acq_fifo_level >= 17);

  uint8_t data = 0;
  dif_i2c_signal_t signal;
  // First is the command.
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalNone);
  TRY_CHECK(data == arp_cmd_pending);
  running_pec = calc_pec(running_pec, data);

  // Next is the byte count.
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalNone);
  TRY_CHECK(data == 17);
  running_pec = calc_pec(running_pec, data);

  // Then 15 bytes of the UDID.
  bool udid_match = true;
  for (size_t i = 0; i < 15; ++i) {
    TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
    TRY_CHECK(signal == kDifI2cSignalNone);
    if (data != kSmbusUdid[i]) {
      udid_match = false;
    }
    running_pec = calc_pec(running_pec, data);
  }

  // Then the last byte of the UDID is currently pending.
  TRY(dif_i2c_get_pending_acq_byte(&i2c, &data));
  if (data != kSmbusUdid[15]) {
    udid_match = false;
  }
  if (udid_match) {
    // Advance to the PEC byte if the UDID matches. ACK both the last UDID byte
    // and the address, then hold at the PEC byte before committing the address.
    state = kI2cStateArpPec;
    TRY(dif_i2c_set_auto_ack_count(&i2c, 2));
  } else {
    // NACK if the UDID doesn't match.
    state = kI2cStateTransactionNack;
    TRY(dif_i2c_nack_transaction(&i2c));
    LOG_INFO("AssignAddress: UDID mismatch");
  }
  return OK_STATUS();
}

/**
 * This is the final state for the Assign Address command.
 *
 * Because we hadn't ACK'd the PEC until the PEC Check state, the ACQ FIFO
 * should have both the PEC data byte and the Stop here. The next state is Idle.
 */
static status_t finish_assign_addr(dif_i2c_irq_state_snapshot_t irq_snapshot,
                                   dif_i2c_status_t i2c_status) {
  TRY_CHECK(bitfield_bit32_read(irq_snapshot, kDifI2cIrqCmdComplete));
  TRY_CHECK(!i2c_status.acq_fifo_empty);

  uint8_t data = 0;
  dif_i2c_signal_t signal;
  // Pull out the PEC first. No need to validate it again.
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalNone);
  // We only expect a Stop next.
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalStop);

  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));
  arp_cmd_pending = 0;
  state = kI2cStateIdle;
  LOG_INFO("New i2c address assigned: 0x%x", i2c_id.address);

  return OK_STATUS();
}

/**
 * This state handles all NACKs and drains the ACQ FIFO until we see the end of
 * the transaction, a NackStop signal. It makes use of the ACQ FIFO watermark to
 * get further interrupts if we don't see the NackStop the first time.
 */
static status_t finish_nack(dif_i2c_irq_state_snapshot_t irq_snapshot,
                            dif_i2c_status_t i2c_status) {
  bool saw_stop = false;
  if (bitfield_bit32_read(irq_snapshot, kDifI2cIrqCmdComplete)) {
    TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));
  }

  if (!i2c_status.acq_fifo_empty) {
    dif_i2c_level_t acq_fifo_level;
    TRY(dif_i2c_get_fifo_levels(&i2c, NULL, NULL, NULL, &acq_fifo_level));

    for (size_t i = 0; i < acq_fifo_level; ++i) {
      uint8_t data = 0;
      dif_i2c_signal_t signal;
      TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
      if (signal == kDifI2cSignalNackStop) {
        saw_stop = true;
        break;
      }
    }
  }
  if (!saw_stop) {
    // Set the threshold interrupt so we return here.
    TRY(dif_i2c_set_target_watermarks(&i2c, /*tx_level=*/0, /*acq_level=*/0));
  } else {
    // Set the threshold interrupt back to inert.
    TRY(dif_i2c_set_target_watermarks(&i2c, /*tx_level=*/0,
                                      I2C_PARAM_ACQ_FIFO_DEPTH));

    // Done with the command.
    arp_cmd_pending = 0;
    state = kI2cStateIdle;
  }

  return OK_STATUS();
}

/**
 * This function handles dispatch between the Write Message and Read Message
 * commands. For Write Message, we'll see another data byte and stretching on
 * the ACQ FIFO. For Read Message, we'll see the CmdComplete interrupt, but we
 * won't necessarily see the possibly late-arriving address byte in the ACQ
 * FIFO.
 *
 * A Write Message cause a state transition to MessageReceive, and the Auto ACK
 * Counter will be set to receive all data bytes.
 *
 * A Read Message causes a state transition to MessageTransmit, and no further
 * action is taken in this state. We expect to get a TX FIFO stretch interrupt
 * that activates the next state's handler.
 */
static status_t message_cmd_dispatch(dif_i2c_irq_state_snapshot_t irq_snapshot,
                                     dif_i2c_status_t i2c_status) {
  bool acq_stretch = bitfield_bit32_read(irq_snapshot, kDifI2cIrqAcqStretch);
  bool cmd_complete = bitfield_bit32_read(irq_snapshot, kDifI2cIrqCmdComplete);
  const uint8_t message_addr = (uint8_t)kMessageAddr;

  // The command byte should at least still be in the FIFO.
  TRY_CHECK(!i2c_status.acq_fifo_empty);

  uint8_t data = 0;
  dif_i2c_signal_t signal;
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalNone);
  TRY_CHECK(data == message_addr);

  if (acq_stretch && !cmd_complete) {
    // This is a write command. ACK the bytes and let them in.
    state = kI2cStateMessageReceive;
    TRY(dif_i2c_set_auto_ack_count(&i2c, sizeof(message)));
  } else if (cmd_complete) {
    // A read should be coming, but don't process it here. There may be a delay
    // between the "command complete" IRQ and the push of the Repeated Start to
    // the ACQ FIFO. Assume it hasn't arrived yet, and process the Read in the
    // next state.
    TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));
    state = kI2cStateMessageTransmit;
  } else {
    TRY_CHECK(false, "Unknown state of message command");
  }

  return OK_STATUS();
}

/**
 * This function handles the data of the Message Receive command. Because we set
 * up the Auto ACK Counter to ACK all data bytes, we expect to see even the Stop
 * in the ACQ FIFO in this state. We write the Message register with all the
 * received data.
 */
static status_t message_receive(dif_i2c_irq_state_snapshot_t irq_snapshot,
                                dif_i2c_status_t i2c_status) {
  TRY_CHECK(!bitfield_bit32_read(irq_snapshot, kDifI2cIrqAcqStretch));
  TRY_CHECK(bitfield_bit32_read(irq_snapshot, kDifI2cIrqCmdComplete));
  TRY_CHECK(!i2c_status.acq_fifo_empty);

  // Check that the FIFO has the expected number of bytes, all 32 bytes of the
  // message, plus the STOP.
  dif_i2c_level_t acq_fifo_level;
  TRY(dif_i2c_get_fifo_levels(&i2c, NULL, NULL, NULL, &acq_fifo_level));
  TRY_CHECK(acq_fifo_level >= sizeof(message) + 1);

  uint8_t data = 0;
  dif_i2c_signal_t signal;
  for (size_t i = 0; i < sizeof(message); ++i) {
    TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
    TRY_CHECK(signal == kDifI2cSignalNone);
    message[i] = data;
  }

  // Then the Stop finishes the command.
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalStop);
  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));
  state = kI2cStateIdle;

  return OK_STATUS();
}

/**
 * This state handles preparing the TX FIFO for a Read Message command.
 */
static status_t message_transmit(dif_i2c_irq_state_snapshot_t irq_snapshot,
                                 dif_i2c_status_t i2c_status) {
  TRY_CHECK(bitfield_bit32_read(irq_snapshot, kDifI2cIrqTxStretch));
  TRY_CHECK(i2c_status.tx_fifo_empty);
  // Should see the address byte still there.
  TRY_CHECK(!i2c_status.acq_fifo_empty);

  uint8_t data = 0;
  dif_i2c_signal_t signal;
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalRepeat);
  TRY_CHECK(data == ((i2c_id.address << 1) | 1));

  // Clear the TX pending bit.
  dif_i2c_target_tx_halt_events_t events = {0};
  TRY(dif_i2c_get_target_tx_halt_events(&i2c, &events));
  TRY_CHECK(events.tx_pending);
  TRY_CHECK(!events.bus_timeout);
  TRY(dif_i2c_clear_target_tx_halt_events(&i2c, events));

  // Prepare the TX FIFO.
  for (size_t i = 0; i < sizeof(message); ++i) {
    TRY(dif_i2c_transmit_byte(&i2c, message[i]));
  }

  state = kI2cStateMessageFinish;
  return OK_STATUS();
}

/**
 * This state completes the Read Message command. It drains the Stop from the
 * ACQ FIFO and clears the CmdComplete interrupt.
 */
static status_t message_finish(dif_i2c_irq_state_snapshot_t irq_snapshot,
                               dif_i2c_status_t i2c_status) {
  TRY_CHECK(bitfield_bit32_read(irq_snapshot, kDifI2cIrqCmdComplete));
  TRY_CHECK(!i2c_status.acq_fifo_empty);

  // Expecting only the STOP.
  uint8_t data = 0;
  dif_i2c_signal_t signal;
  TRY(dif_i2c_acquire_byte(&i2c, &data, &signal));
  TRY_CHECK(signal == kDifI2cSignalStop);

  TRY(dif_i2c_irq_acknowledge(&i2c, kDifI2cIrqCmdComplete));
  state = kI2cStateIdle;
  return OK_STATUS();
}

static status_t smbus_arp_test(void) {
  bool message_received = false;
  state = kI2cStateIdle;
  test_status_set(kTestStatusInWfi);
  while (!message_received) {
    ATOMIC_WAIT_FOR_INTERRUPT(i2c_event == true);
    i2c_event = false;

    dif_i2c_irq_state_snapshot_t irq_snapshot = {0};
    CHECK_DIF_OK(dif_i2c_irq_get_state(&i2c, &irq_snapshot));

    dif_i2c_status_t i2c_status = {0};
    CHECK_DIF_OK(dif_i2c_get_status(&i2c, &i2c_status));

    switch (state) {
      case kI2cStateIdle:
        TRY(process_new_command(irq_snapshot, i2c_status));
        break;
      case kI2cStateArpPec:
        TRY(check_arp_pec(irq_snapshot, i2c_status));
        break;
      case kI2cStateArpGetUdidWait:
        TRY(prepare_udid_reply(irq_snapshot, i2c_status));
        break;
      case kI2cStateArpGetUdidTransmit:
        TRY(complete_get_udid(irq_snapshot, i2c_status));
        break;
      case kI2cStateArpCheckUdid:
        TRY(check_received_udid(irq_snapshot, i2c_status));
        break;
      case kI2cStateMessageWait:
        TRY(message_cmd_dispatch(irq_snapshot, i2c_status));
        break;
      case kI2cStateMessageReceive:
        TRY(message_receive(irq_snapshot, i2c_status));
        break;
      case kI2cStateMessageTransmit:
        TRY(message_transmit(irq_snapshot, i2c_status));
        break;
      case kI2cStateMessageFinish:
        TRY(message_finish(irq_snapshot, i2c_status));
        message_received = true;
        break;
      case kI2cStateAssignAddressComplete:
        TRY(finish_assign_addr(irq_snapshot, i2c_status));
        break;
      case kI2cStateTransactionNack:
        TRY(finish_nack(irq_snapshot, i2c_status));
        break;
      default:
        TRY_CHECK(false, "Reached invalid state %d", state);
    }

    dif_i2c_irq_enable_snapshot_t enables = i2c_irq_enables;
    CHECK_DIF_OK(dif_i2c_irq_restore_all(&i2c, &enables));
  }
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(test_init());
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, smbus_arp_test);
  return status_ok(result);
}
