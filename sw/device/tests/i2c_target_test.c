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

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

enum {
  kTestTimeout = 1000000,     // 1 second
  kTransactionDelay = 10000,  // 10 ms
  kPlicTarget = 0,
};

static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this test expects a pwrmgr");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount == 1, "this test expects exactly one rv_plic");
static const dt_pinmux_t kPinmuxDt = 0;
static_assert(kDtPinmuxCount == 1, "this test expects exactly one pinmux");

static dif_pinmux_t pinmux;
static dif_pwrmgr_t pwrmgr;
static dif_rv_plic_t plic;
static dif_i2c_t i2c;

static dif_pwrmgr_request_sources_t wakeup_sources;
static uint8_t i2c_instance_under_test = 0;
static uint32_t i2c_clock_stretching_delay_micros = 0;

/**
 * External interrupt handler.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid == dt_pwrmgr_instance_id(kPwrmgrDt) &&
      irq_id == dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup)) {
    CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr, kDtPwrmgrIrqWakeup));
    return true;
  } else {
    return false;
  }
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
  TRY_CHECK(i2c_instance < kDtI2cCount);

  dt_i2c_t dt_i2c = i2c_instance;  // Starts at 0.
  TRY(dif_i2c_init_from_dt(dt_i2c, i2c));

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
    dif_rv_plic_irq_id_t plic_id =
        dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
    rv_plic_testutils_irq_range_enable(&plic, kPlicTarget, plic_id, plic_id);
    // Enable pwrmgr interrupt.
    TRY(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

    // Configure the power domains for normal sleep.
    TRY(dif_pwrmgr_get_domain_config(&pwrmgr, &pwrmgr_domain_cfg));
    pwrmgr_domain_cfg |= kDifPwrmgrDomainOptionMainPowerInLowPower;
  }

  TRY(pwrmgr_testutils_enable_low_power(&pwrmgr, wakeup_sources,
                                        pwrmgr_domain_cfg));

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
  if (TRY(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, wakeup_sources)) == true) {
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
  TRY(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));

  TRY(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));

  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_pinmux_instance_id(kPinmuxDt),
      kDtPinmuxWakeupPinWkupReq, &wakeup_sources));

  TRY(dif_rv_plic_init_from_dt(kRvPlicDt, &plic));
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
