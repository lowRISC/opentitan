// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include "sw/device/lib/testing/json/i2c_target.h"

#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/i2c_testutils.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "i2c_regs.h"  // Generated.
#include "sw/device/lib/testing/autogen/isr_testutils.h"

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

enum {
  kTestTimeout = 1000000,     // 1 second
  kTransactionDelay = 10000,  // 10 ms
};

static dif_pinmux_t pinmux;
static dif_pwrmgr_t pwrmgr;
static dif_rv_plic_t plic;
static dif_i2c_t i2c;

static uint8_t i2c_instance_under_test = 0;
static uint32_t i2c_clock_stretching_delay_micros = 0;

static plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};

static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

/**
 * External interrupt handler.
 */
void ottf_external_isr(uint32_t *exc_info) {
  dif_rv_plic_irq_id_t plic_irq_id = 0;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, plic_ctx.hart_id, &plic_irq_id));
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];

  // Check that both the peripheral and the irq id is correct
  switch (peripheral) {
    case kTopEarlgreyPlicPeripheralUart0:
      CHECK(ottf_console_flow_control_isr(exc_info),
            "Unexpected non-flow control UART IRQ, with PLIC ID %d",
            plic_irq_id);
      break;
    case kTopEarlgreyPlicPeripheralPwrmgrAon: {
      dif_pwrmgr_irq_t irq =
          (dif_pwrmgr_irq_t)(plic_irq_id -
                             pwrmgr_isr_ctx.plic_pwrmgr_start_irq_id);
      dif_irq_type_t type;
      CHECK_DIF_OK(dif_pwrmgr_irq_get_type(&pwrmgr, irq, &type));
      CHECK(irq == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq);
      if (type == kDifIrqTypeEvent) {
        CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(pwrmgr_isr_ctx.pwrmgr, irq));
      }
    } break;
    default:
      CHECK(false, "IRQ peripheral: %d is incorrect", peripheral);
      break;
  }
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, plic_ctx.hart_id, plic_irq_id));
}

static status_t reset_fifos(dif_i2c_t *i2c) {
  TRY(dif_i2c_reset_rx_fifo(i2c));
  TRY(dif_i2c_reset_tx_fifo(i2c));
  TRY(dif_i2c_reset_fmt_fifo(i2c));
  TRY(dif_i2c_reset_acq_fifo(i2c));
  return OK_STATUS();
}

static status_t i2c_detach_instance(dif_i2c_t *i2c, dif_pinmux_t *pinmux,
                                    uint8_t i2c_instance) {
  TRY(dif_i2c_host_set_enabled(i2c, kDifToggleDisabled));
  return i2c_testutils_detach_pinmux(pinmux, i2c_instance);
}

static status_t i2c_configure_instance(dif_i2c_t *i2c, dif_pinmux_t *pinmux,
                                       uint8_t i2c_instance) {
  const uintptr_t kI2cBaseAddrTable[] = {TOP_EARLGREY_I2C0_BASE_ADDR,
                                         TOP_EARLGREY_I2C1_BASE_ADDR,
                                         TOP_EARLGREY_I2C2_BASE_ADDR};
  TRY_CHECK(i2c_instance < ARRAYSIZE(kI2cBaseAddrTable));

  mmio_region_t base_addr =
      mmio_region_from_addr(kI2cBaseAddrTable[i2c_instance]);
  TRY(dif_i2c_init(base_addr, i2c));

  TRY(i2c_testutils_select_pinmux(pinmux, i2c_instance,
                                  I2cPinmuxPlatformIdHyper310));
  TRY(i2c_testutils_set_speed(i2c, kDifI2cSpeedStandard));
  TRY(dif_i2c_host_set_enabled(i2c, kDifToggleEnabled));
  return OK_STATUS();
}

static status_t configure_device_address(ujson_t *uj, dif_i2c_t *i2c) {
  i2c_target_address_t address;
  TRY(UJSON_WITH_CRC(ujson_deserialize_i2c_target_address_t, uj, &address));

  TRY(dif_i2c_host_set_enabled(i2c, kDifToggleDisabled));
  TRY(dif_i2c_device_set_enabled(i2c, kDifToggleDisabled));

  TRY(i2c_detach_instance(i2c, &pinmux, i2c_instance_under_test));
  i2c_instance_under_test = address.instance;
  TRY(i2c_configure_instance(i2c, &pinmux, i2c_instance_under_test));

  dif_i2c_id_t id0 = {
      .mask = address.mask0,
      .address = address.id0,
  };
  dif_i2c_id_t id1 = {
      .mask = address.mask1,
      .address = address.id1,
  };
  TRY(dif_i2c_set_device_id(i2c, &id0, &id1));
  TRY(dif_i2c_device_set_enabled(i2c, kDifToggleEnabled));
  // After enabling target mode, reset all of the FIFOs to clear out
  // any leftover junk.
  TRY(reset_fifos(i2c));
  return RESP_OK_STATUS(uj);
}

static status_t wait_for_acq_fifo(dif_i2c_t *i2c, dif_i2c_level_t at_least,
                                  const ibex_timeout_t *deadline) {
  dif_i2c_level_t acq_fifo_lvl;
  while (!ibex_timeout_check(deadline)) {
    if (dif_i2c_get_fifo_levels(i2c, NULL, NULL, NULL, &acq_fifo_lvl) ==
            kDifOk &&
        acq_fifo_lvl >= at_least) {
      return OK_STATUS();
    }
  }
  return DEADLINE_EXCEEDED();
}

static status_t recv_write_transfer(dif_i2c_t *i2c, i2c_transfer_start_t *txn,
                                    uint32_t micros, uint32_t delay_micros) {
  ibex_timeout_t deadline = ibex_timeout_init(micros);
  uint8_t byte;
  dif_i2c_signal_t signal;

  // Address phase.
  TRY(wait_for_acq_fifo(i2c, 1, &deadline));
  TRY(dif_i2c_acquire_byte(i2c, &byte, &signal));

  TRY_CHECK(signal == kDifI2cSignalStart || signal == kDifI2cSignalRepeat,
            "Expected SignalStart(%u), got %u", kDifI2cSignalStart, signal);
  txn->address = byte >> 1;

  // Data phase.
  while (true) {
    if (txn->length % 64 == 0 && delay_micros) {
      busy_spin_micros(delay_micros);
    }
    TRY(wait_for_acq_fifo(i2c, 1, &deadline));
    TRY(dif_i2c_acquire_byte(i2c, &byte, &signal));
    if (signal != kDifI2cSignalNone) {
      break;
    }
    txn->data[txn->length++] = byte;
  }

  // End of transfer.
  switch (signal) {
    case kDifI2cSignalStop:
      txn->stop = true;
      return OK_STATUS(0);
    case kDifI2cSignalRepeat:
      txn->stop = false;
      // Repeated start, return the address of the next operation.
      return OK_STATUS(txn->address);
    default:
      return INTERNAL();
  }
}

static status_t start_read_transaction(ujson_t *uj, dif_i2c_t *i2c) {
  i2c_transfer_start_t txn;
  TRY(UJSON_WITH_CRC(ujson_deserialize_i2c_transfer_start_t, uj, &txn));
  busy_spin_micros(i2c_clock_stretching_delay_micros);
  TRY(i2c_testutils_target_read(i2c, txn.length, txn.data));
  ibex_timeout_t deadline = ibex_timeout_init(kTestTimeout);
  TRY(wait_for_acq_fifo(i2c, 2, &deadline));
  uint8_t address = 0;
  TRY(i2c_testutils_target_check_read(i2c, &address, NULL));
  TRY_CHECK(txn.address == address, "Address read (%x) is not the expected(%x)",
            address, txn.address);
  return RESP_OK_STATUS(uj);
}

static status_t start_write_transaction(ujson_t *uj, dif_i2c_t *i2c,
                                        uint32_t delay_micros) {
  i2c_transfer_start_t txn = (i2c_transfer_start_t){0};
  TRY(recv_write_transfer(i2c, &txn, kTestTimeout, delay_micros));
  return RESP_OK(ujson_serialize_i2c_transfer_start_t, uj, &txn);
}

static status_t start_write_read_transaction(ujson_t *uj, dif_i2c_t *i2c) {
  i2c_transfer_start_t read_trans;
  TRY(UJSON_WITH_CRC(ujson_deserialize_i2c_transfer_start_t, uj, &read_trans));
  TRY(i2c_testutils_target_read(i2c, read_trans.length, read_trans.data));

  i2c_transfer_start_t write_trans = (i2c_transfer_start_t){0};
  uint8_t address =
      (uint8_t)TRY(recv_write_transfer(i2c, &write_trans, kTestTimeout, 0));
  TRY_CHECK(write_trans.stop == false, "Stop bit not expected at this point.");
  TRY_CHECK(read_trans.address == address,
            "Address (0x%x) is not the expected(0x%x)", address,
            read_trans.address);
  ibex_timeout_t deadline = ibex_timeout_init(kTestTimeout);
  TRY(wait_for_acq_fifo(i2c, 1, &deadline));

  return RESP_OK(ujson_serialize_i2c_transfer_start_t, uj, &write_trans);
}

static status_t enter_sleep(ujson_t *uj, dif_i2c_t *i2c, bool normal) {
  dif_pinmux_wakeup_config_t wakeup_cfg = {
      .mode = kDifPinmuxWakeupModeAnyEdge,
      .signal_filter = false,
      .pad_type = kDifPinmuxPadKindMio,
      .pad_select = kTopEarlgreyPinmuxInselIoa7,
  };
  TRY(dif_pinmux_wakeup_detector_enable(&pinmux, 0, wakeup_cfg));
  dif_pwrmgr_domain_config_t pwrmgr_domain_cfg = 0;
  if (normal) {
    // Normal sleep wakes up from an interrupt, so enable the relevant sources.
    // Enable all the AON interrupts used in this test.
    rv_plic_testutils_irq_range_enable(&plic, kTopEarlgreyPlicTargetIbex0,
                                       kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                       kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
    // Enable pwrmgr interrupt.
    TRY(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

    // Configure the power domains for normal sleep.
    pwrmgr_domain_cfg = kDifPwrmgrDomainOptionMainPowerInLowPower |
                        kDifPwrmgrDomainOptionUsbClockInActivePower;
  }

  TRY(pwrmgr_testutils_enable_low_power(
      &pwrmgr, kDifPwrmgrWakeupRequestSourceThree, pwrmgr_domain_cfg));

  LOG_INFO("Going to sleep.");
  wait_for_interrupt();

  if (normal) {
    LOG_INFO("Woke from sleep.");
    reset_fifos(i2c);
    return RESP_OK_STATUS(uj);
  } else {
    // Deep sleep wakes up with a reset; we should never get here.
    // A deep-sleep wakeup resets the chip, and we should detect that
    // condition in `wakeup_check` before starting the command processor.
    LOG_ERROR("Unexpected wake from deep sleep.");
    return INTERNAL();
  }
}

static status_t wakeup_check(ujson_t *uj, dif_i2c_t *i2c) {
  if (TRY(pwrmgr_testutils_is_wakeup_reason(
          &pwrmgr, kDifPwrmgrWakeupRequestSourceThree)) == true) {
    LOG_ERROR("Woke from deep sleep; resuming test.");
    TRY(dif_pinmux_wakeup_detector_disable(&pinmux, 0));
    // If we get here, the test harness is expecting to receive a
    // status_t to know we woke back up.
    return RESP_OK_STATUS(uj);
  }
  return OK_STATUS();
}

static status_t command_processor(ujson_t *uj) {
  TRY(wakeup_check(uj, &i2c));
  while (true) {
    test_command_t command;
    TRY(UJSON_WITH_CRC(ujson_deserialize_test_command_t, uj, &command));
    switch (command) {
      case kTestCommandEnterNormalSleep:
        RESP_ERR(uj, enter_sleep(uj, &i2c, true));
        break;
      case kTestCommandEnterDeepSleep:
        RESP_ERR(uj, enter_sleep(uj, &i2c, false));
        break;
      case kTestCommandI2cTargetAddress:
        RESP_ERR(uj, configure_device_address(uj, &i2c));
        break;
      case kTestCommandI2cStartTransferWrite:
        RESP_ERR(uj, start_write_transaction(uj, &i2c, 0));
        break;
      case kTestCommandI2cStartTransferRead:
        RESP_ERR(uj, start_read_transaction(uj, &i2c));
        break;
      case kTestCommandI2cStartTransferWriteRead:
        RESP_ERR(uj, start_write_read_transaction(uj, &i2c));
        break;
      case kTestCommandI2cStartTransferWriteSlow:
        // We'll insert a 10ms delay every 64 bytes, which is a huge delay
        // at 100 KHz, forcing the peripheral to stretch the clock.
        RESP_ERR(uj, start_write_transaction(uj, &i2c, kTransactionDelay));
        break;
      case kTestCommandI2cTestConfig: {
        i2c_test_config_t config;
        TRY(UJSON_WITH_CRC(ujson_deserialize_i2c_test_config_t, uj, &config));
        i2c_clock_stretching_delay_micros =
            config.clock_stretching_delay_millis * 1000;
        RESP_ERR(uj, RESP_OK_STATUS(uj));
      } break;
      default:
        LOG_ERROR("Unrecognized command: %d", command);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }
  // We should never reach here.
  return INTERNAL();
}

static status_t test_init(void) {
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  TRY(dif_pinmux_init(base_addr, &pinmux));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  TRY(dif_pwrmgr_init(base_addr, &pwrmgr));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  TRY(dif_rv_plic_init(base_addr, &plic));
  TRY(dif_rv_plic_reset(&plic));
  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(test_init());
  CHECK_STATUS_OK(
      i2c_configure_instance(&i2c, &pinmux, i2c_instance_under_test));
  status_t status;
  ujson_t uj = ujson_ottf_console();
  status = command_processor(&uj);
  LOG_INFO("status = %r", status);
  return status_ok(status);
}
