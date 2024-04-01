// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// clang-format off
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
// -o hw/top_earlgrey
#include <limits.h>

// This test should avoid otp_ctrl interrupts in rom_ext, since the rom
// extension configures CSR accesses to OTP and AST to become illegal.
//
// This test is getting too big so we need to split it up. To do so,
// each peripheral is given an ID (according to their alphabetical order)
// and we define TEST_MIN_IRQ_PERIPHERAL and TEST_MAX_IRQ_PERIPHERAL to
// choose which ones are being tested.

#ifndef TEST_MIN_IRQ_PERIPHERAL
#define TEST_MIN_IRQ_PERIPHERAL 0
#endif

#ifndef TEST_MAX_IRQ_PERIPHERAL
#define TEST_MAX_IRQ_PERIPHERAL 23
#endif

#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
#include "sw/device/lib/dif/dif_pattgen.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_sensor_ctrl.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#if TEST_MIN_IRQ_PERIPHERAL <= 0 && 0 < TEST_MAX_IRQ_PERIPHERAL
static dif_adc_ctrl_t adc_ctrl_aon;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 1 && 1 < TEST_MAX_IRQ_PERIPHERAL
static dif_alert_handler_t alert_handler;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 2 && 2 < TEST_MAX_IRQ_PERIPHERAL
static dif_aon_timer_t aon_timer_aon;
#endif

// TODO(lowrisc/opentitan#20747) Adjust csrng special handling once this is
// fixed.
static dif_csrng_t csrng;

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
static dif_edn_t edn0;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
static dif_edn_t edn1;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 5 && 5 < TEST_MAX_IRQ_PERIPHERAL
static dif_entropy_src_t entropy_src;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 6 && 6 < TEST_MAX_IRQ_PERIPHERAL
static dif_flash_ctrl_t flash_ctrl;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 7 && 7 < TEST_MAX_IRQ_PERIPHERAL
static dif_gpio_t gpio;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 8 && 8 < TEST_MAX_IRQ_PERIPHERAL
static dif_hmac_t hmac;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
static dif_i2c_t i2c0;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
static dif_i2c_t i2c1;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
static dif_i2c_t i2c2;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 10 && 10 < TEST_MAX_IRQ_PERIPHERAL
static dif_keymgr_t keymgr;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 11 && 11 < TEST_MAX_IRQ_PERIPHERAL
static dif_kmac_t kmac;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 12 && 12 < TEST_MAX_IRQ_PERIPHERAL
static dif_otbn_t otbn;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 13 && 13 < TEST_MAX_IRQ_PERIPHERAL
static dif_otp_ctrl_t otp_ctrl;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 14 && 14 < TEST_MAX_IRQ_PERIPHERAL
static dif_pattgen_t pattgen;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 15 && 15 < TEST_MAX_IRQ_PERIPHERAL
static dif_pwrmgr_t pwrmgr_aon;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 16 && 16 < TEST_MAX_IRQ_PERIPHERAL
static dif_rv_timer_t rv_timer;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 17 && 17 < TEST_MAX_IRQ_PERIPHERAL
static dif_sensor_ctrl_t sensor_ctrl_aon;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 18 && 18 < TEST_MAX_IRQ_PERIPHERAL
static dif_spi_device_t spi_device;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
static dif_spi_host_t spi_host0;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
static dif_spi_host_t spi_host1;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 20 && 20 < TEST_MAX_IRQ_PERIPHERAL
static dif_sysrst_ctrl_t sysrst_ctrl_aon;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
static dif_uart_t uart0;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
static dif_uart_t uart1;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
static dif_uart_t uart2;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
static dif_uart_t uart3;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 22 && 22 < TEST_MAX_IRQ_PERIPHERAL
static dif_usbdev_t usbdev;
#endif

static dif_rv_plic_t plic;
static const top_earlgrey_plic_target_t kHart = kTopEarlgreyPlicTargetIbex0;

/**
 * Flag indicating which peripheral is under test.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
static volatile top_earlgrey_plic_peripheral_t peripheral_expected;

/**
 * Flags indicating the IRQ expected to have triggered and serviced within the
 * peripheral.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */

#if TEST_MIN_IRQ_PERIPHERAL <= 0 && 0 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_adc_ctrl_irq_t adc_ctrl_irq_expected;
static volatile dif_adc_ctrl_irq_t adc_ctrl_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 1 && 1 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_alert_handler_irq_t alert_handler_irq_expected;
static volatile dif_alert_handler_irq_t alert_handler_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 2 && 2 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_aon_timer_irq_t aon_timer_irq_expected;
static volatile dif_aon_timer_irq_t aon_timer_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 3 && 3 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_csrng_irq_t csrng_irq_expected;
static volatile dif_csrng_irq_t csrng_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_edn_irq_t edn_irq_expected;
static volatile dif_edn_irq_t edn_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 5 && 5 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_entropy_src_irq_t entropy_src_irq_expected;
static volatile dif_entropy_src_irq_t entropy_src_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 6 && 6 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_flash_ctrl_irq_t flash_ctrl_irq_expected;
static volatile dif_flash_ctrl_irq_t flash_ctrl_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 7 && 7 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_gpio_irq_t gpio_irq_expected;
static volatile dif_gpio_irq_t gpio_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 8 && 8 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_hmac_irq_t hmac_irq_expected;
static volatile dif_hmac_irq_t hmac_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_i2c_irq_t i2c_irq_expected;
static volatile dif_i2c_irq_t i2c_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 10 && 10 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_keymgr_irq_t keymgr_irq_expected;
static volatile dif_keymgr_irq_t keymgr_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 11 && 11 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_kmac_irq_t kmac_irq_expected;
static volatile dif_kmac_irq_t kmac_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 12 && 12 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_otbn_irq_t otbn_irq_expected;
static volatile dif_otbn_irq_t otbn_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 13 && 13 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_otp_ctrl_irq_t otp_ctrl_irq_expected;
static volatile dif_otp_ctrl_irq_t otp_ctrl_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 14 && 14 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_pattgen_irq_t pattgen_irq_expected;
static volatile dif_pattgen_irq_t pattgen_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 15 && 15 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_pwrmgr_irq_t pwrmgr_irq_expected;
static volatile dif_pwrmgr_irq_t pwrmgr_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 16 && 16 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_rv_timer_irq_t rv_timer_irq_expected;
static volatile dif_rv_timer_irq_t rv_timer_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 17 && 17 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_sensor_ctrl_irq_t sensor_ctrl_irq_expected;
static volatile dif_sensor_ctrl_irq_t sensor_ctrl_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 18 && 18 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_spi_device_irq_t spi_device_irq_expected;
static volatile dif_spi_device_irq_t spi_device_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_spi_host_irq_t spi_host_irq_expected;
static volatile dif_spi_host_irq_t spi_host_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 20 && 20 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_sysrst_ctrl_irq_t sysrst_ctrl_irq_expected;
static volatile dif_sysrst_ctrl_irq_t sysrst_ctrl_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_uart_irq_t uart_irq_expected;
static volatile dif_uart_irq_t uart_irq_serviced;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 22 && 22 < TEST_MAX_IRQ_PERIPHERAL
static volatile dif_usbdev_irq_t usbdev_irq_expected;
static volatile dif_usbdev_irq_t usbdev_irq_serviced;
#endif


#if TEST_MIN_IRQ_PERIPHERAL <= 3 < TEST_MAX_IRQ_PERIPHERAL
static volatile bool allow_csrng_irq = true;
#else
static volatile bool allow_csrng_irq = false;
#endif

/**
 * Provides external IRQ handling for this test.
 *
 * This function overrides the default OTTF external ISR.
 *
 * For each IRQ, it performs the following:
 * 1. Claims the IRQ fired (finds PLIC IRQ index).
 * 2. Checks that the index belongs to the expected peripheral.
 * 3. Checks that the correct and the only IRQ from the expected peripheral
 *    triggered.
 * 4. Clears the IRQ at the peripheral.
 * 5. Completes the IRQ service at PLIC.
 */
void ottf_external_isr(uint32_t *exc_info) {
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kHart, &plic_irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  // TODO(lowrisc/opentitan#20747) Adjust code once this issue is fixed.
  if (allow_csrng_irq && kBootStage == kBootStageOwner &&
      peripheral != peripheral_expected &&
      peripheral == kTopEarlgreyPlicPeripheralCsrng) {
    dif_csrng_irq_t irq = (dif_csrng_irq_t)(
        plic_irq_id -
        (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone);

    dif_csrng_irq_state_snapshot_t snapshot;
    CHECK_DIF_OK(dif_csrng_irq_get_state(&csrng, &snapshot));
    CHECK(snapshot == (dif_csrng_irq_state_snapshot_t)(1 << irq),
          "Only csrng IRQ %d expected to fire. Actual interrupt status = %x",
          irq, snapshot);
    CHECK_DIF_OK(dif_csrng_irq_acknowledge(&csrng, irq));
  } else {
    CHECK(peripheral == peripheral_expected,
          "Interrupt from incorrect peripheral: exp = %d, obs = %d",
          peripheral_expected, peripheral);

    switch (peripheral) {
#if TEST_MIN_IRQ_PERIPHERAL <= 0 && 0 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralAdcCtrlAon: {
        dif_adc_ctrl_irq_t irq = (dif_adc_ctrl_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAdcCtrlAonMatchPending);
        CHECK(irq == adc_ctrl_irq_expected,
              "Incorrect adc_ctrl_aon IRQ triggered: exp = %d, obs = %d",
              adc_ctrl_irq_expected, irq);
        adc_ctrl_irq_serviced = irq;

        dif_adc_ctrl_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_adc_ctrl_irq_get_state(&adc_ctrl_aon, &snapshot));
        CHECK(snapshot == (dif_adc_ctrl_irq_state_snapshot_t)(1 << irq),
              "Only adc_ctrl_aon IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x1 & (1 << irq)) {
          CHECK_DIF_OK(dif_adc_ctrl_irq_force(&adc_ctrl_aon, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_adc_ctrl_irq_set_enabled(&adc_ctrl_aon, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_adc_ctrl_irq_acknowledge(&adc_ctrl_aon, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 1 && 1 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralAlertHandler: {
        dif_alert_handler_irq_t irq = (dif_alert_handler_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAlertHandlerClassa);
        CHECK(irq == alert_handler_irq_expected,
              "Incorrect alert_handler IRQ triggered: exp = %d, obs = %d",
              alert_handler_irq_expected, irq);
        alert_handler_irq_serviced = irq;

        dif_alert_handler_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_alert_handler_irq_get_state(&alert_handler, &snapshot));
        CHECK(snapshot == (dif_alert_handler_irq_state_snapshot_t)(1 << irq),
              "Only alert_handler IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(&alert_handler, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 2 && 2 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralAonTimerAon: {
        dif_aon_timer_irq_t irq = (dif_aon_timer_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired);
        CHECK(irq == aon_timer_irq_expected,
              "Incorrect aon_timer_aon IRQ triggered: exp = %d, obs = %d",
              aon_timer_irq_expected, irq);
        aon_timer_irq_serviced = irq;

        dif_aon_timer_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_aon_timer_irq_get_state(&aon_timer_aon, &snapshot));
        CHECK(snapshot == (dif_aon_timer_irq_state_snapshot_t)(1 << irq),
              "Only aon_timer_aon IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&aon_timer_aon, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 3 && 3 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralCsrng: {
        dif_csrng_irq_t irq = (dif_csrng_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone);
        // This special handling of CSRNG is because it is configured
        // to constantly generate interrupts. There may be better ways
        // to configure the entropy complex so it is less noisy.
        // TODO(lowrisc/opentitan#20747) Adjust code once this is fixed.
        if (kBootStage != kBootStageOwner) {
          CHECK(irq == csrng_irq_expected,
                "Incorrect csrng IRQ triggered: exp = %d, obs = %d",
                csrng_irq_expected, irq);
        }
        csrng_irq_serviced = irq;

        dif_csrng_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_csrng_irq_get_state(&csrng, &snapshot));
        CHECK(snapshot == (dif_csrng_irq_state_snapshot_t)(1 << irq),
              "Only csrng IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_csrng_irq_acknowledge(&csrng, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralEdn0: {
        dif_edn_irq_t irq = (dif_edn_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone);
        CHECK(irq == edn_irq_expected,
              "Incorrect edn0 IRQ triggered: exp = %d, obs = %d",
              edn_irq_expected, irq);
        edn_irq_serviced = irq;

        dif_edn_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_edn_irq_get_state(&edn0, &snapshot));
        CHECK(snapshot == (dif_edn_irq_state_snapshot_t)(1 << irq),
              "Only edn0 IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_edn_irq_acknowledge(&edn0, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralEdn1: {
        dif_edn_irq_t irq = (dif_edn_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone);
        CHECK(irq == edn_irq_expected,
              "Incorrect edn1 IRQ triggered: exp = %d, obs = %d",
              edn_irq_expected, irq);
        edn_irq_serviced = irq;

        dif_edn_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_edn_irq_get_state(&edn1, &snapshot));
        CHECK(snapshot == (dif_edn_irq_state_snapshot_t)(1 << irq),
              "Only edn1 IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_edn_irq_acknowledge(&edn1, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 5 && 5 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralEntropySrc: {
        dif_entropy_src_irq_t irq = (dif_entropy_src_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdEntropySrcEsEntropyValid);
        CHECK(irq == entropy_src_irq_expected,
              "Incorrect entropy_src IRQ triggered: exp = %d, obs = %d",
              entropy_src_irq_expected, irq);
        entropy_src_irq_serviced = irq;

        dif_entropy_src_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_entropy_src_irq_get_state(&entropy_src, &snapshot));
        CHECK(snapshot == (dif_entropy_src_irq_state_snapshot_t)(1 << irq),
              "Only entropy_src IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_entropy_src_irq_acknowledge(&entropy_src, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 6 && 6 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralFlashCtrl: {
        dif_flash_ctrl_irq_t irq = (dif_flash_ctrl_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty);
        CHECK(irq == flash_ctrl_irq_expected,
              "Incorrect flash_ctrl IRQ triggered: exp = %d, obs = %d",
              flash_ctrl_irq_expected, irq);
        flash_ctrl_irq_serviced = irq;

        dif_flash_ctrl_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_flash_ctrl_irq_get_state(&flash_ctrl, &snapshot));
        CHECK(snapshot == (dif_flash_ctrl_irq_state_snapshot_t)((1 << irq) | 0x3),
              "Expected flash_ctrl interrupt status %x. Actual interrupt "
              "status = %x", (1 << irq) | 0x3, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0xf & (1 << irq)) {
          CHECK_DIF_OK(dif_flash_ctrl_irq_force(&flash_ctrl, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x3 & (1 << irq))) {
            CHECK_DIF_OK(dif_flash_ctrl_irq_set_enabled(&flash_ctrl, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_flash_ctrl_irq_acknowledge(&flash_ctrl, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 7 && 7 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralGpio: {
        dif_gpio_irq_t irq = (dif_gpio_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdGpioGpio0);
        CHECK(irq == gpio_irq_expected,
              "Incorrect gpio IRQ triggered: exp = %d, obs = %d",
              gpio_irq_expected, irq);
        gpio_irq_serviced = irq;

        dif_gpio_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_gpio_irq_get_state(&gpio, &snapshot));
        CHECK(snapshot == (dif_gpio_irq_state_snapshot_t)(1 << irq),
              "Only gpio IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_gpio_irq_acknowledge(&gpio, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 8 && 8 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralHmac: {
        dif_hmac_irq_t irq = (dif_hmac_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdHmacHmacDone);
        CHECK(irq == hmac_irq_expected,
              "Incorrect hmac IRQ triggered: exp = %d, obs = %d",
              hmac_irq_expected, irq);
        hmac_irq_serviced = irq;

        dif_hmac_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_hmac_irq_get_state(&hmac, &snapshot));
        CHECK(snapshot == (dif_hmac_irq_state_snapshot_t)(1 << irq),
              "Only hmac IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x2 & (1 << irq)) {
          CHECK_DIF_OK(dif_hmac_irq_force(&hmac, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_hmac_irq_set_enabled(&hmac, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_hmac_irq_acknowledge(&hmac, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralI2c0: {
        dif_i2c_irq_t irq = (dif_i2c_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdI2c0FmtThreshold);
        CHECK(irq == i2c_irq_expected,
              "Incorrect i2c0 IRQ triggered: exp = %d, obs = %d",
              i2c_irq_expected, irq);
        i2c_irq_serviced = irq;

        dif_i2c_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_i2c_irq_get_state(&i2c0, &snapshot));
        CHECK(snapshot == (dif_i2c_irq_state_snapshot_t)(1 << irq),
              "Only i2c0 IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x1c07 & (1 << irq)) {
          CHECK_DIF_OK(dif_i2c_irq_force(&i2c0, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_i2c_irq_set_enabled(&i2c0, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_i2c_irq_acknowledge(&i2c0, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralI2c1: {
        dif_i2c_irq_t irq = (dif_i2c_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdI2c1FmtThreshold);
        CHECK(irq == i2c_irq_expected,
              "Incorrect i2c1 IRQ triggered: exp = %d, obs = %d",
              i2c_irq_expected, irq);
        i2c_irq_serviced = irq;

        dif_i2c_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_i2c_irq_get_state(&i2c1, &snapshot));
        CHECK(snapshot == (dif_i2c_irq_state_snapshot_t)(1 << irq),
              "Only i2c1 IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x1c07 & (1 << irq)) {
          CHECK_DIF_OK(dif_i2c_irq_force(&i2c1, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_i2c_irq_set_enabled(&i2c1, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_i2c_irq_acknowledge(&i2c1, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralI2c2: {
        dif_i2c_irq_t irq = (dif_i2c_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdI2c2FmtThreshold);
        CHECK(irq == i2c_irq_expected,
              "Incorrect i2c2 IRQ triggered: exp = %d, obs = %d",
              i2c_irq_expected, irq);
        i2c_irq_serviced = irq;

        dif_i2c_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_i2c_irq_get_state(&i2c2, &snapshot));
        CHECK(snapshot == (dif_i2c_irq_state_snapshot_t)(1 << irq),
              "Only i2c2 IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x1c07 & (1 << irq)) {
          CHECK_DIF_OK(dif_i2c_irq_force(&i2c2, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_i2c_irq_set_enabled(&i2c2, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_i2c_irq_acknowledge(&i2c2, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 10 && 10 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralKeymgr: {
        dif_keymgr_irq_t irq = (dif_keymgr_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdKeymgrOpDone);
        CHECK(irq == keymgr_irq_expected,
              "Incorrect keymgr IRQ triggered: exp = %d, obs = %d",
              keymgr_irq_expected, irq);
        keymgr_irq_serviced = irq;

        dif_keymgr_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_keymgr_irq_get_state(&keymgr, &snapshot));
        CHECK(snapshot == (dif_keymgr_irq_state_snapshot_t)(1 << irq),
              "Only keymgr IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_keymgr_irq_acknowledge(&keymgr, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 11 && 11 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralKmac: {
        dif_kmac_irq_t irq = (dif_kmac_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdKmacKmacDone);
        CHECK(irq == kmac_irq_expected,
              "Incorrect kmac IRQ triggered: exp = %d, obs = %d",
              kmac_irq_expected, irq);
        kmac_irq_serviced = irq;

        dif_kmac_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_kmac_irq_get_state(&kmac, &snapshot));
        CHECK(snapshot == (dif_kmac_irq_state_snapshot_t)(1 << irq),
              "Only kmac IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x2 & (1 << irq)) {
          CHECK_DIF_OK(dif_kmac_irq_force(&kmac, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_kmac_irq_set_enabled(&kmac, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_kmac_irq_acknowledge(&kmac, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 12 && 12 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralOtbn: {
        dif_otbn_irq_t irq = (dif_otbn_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdOtbnDone);
        CHECK(irq == otbn_irq_expected,
              "Incorrect otbn IRQ triggered: exp = %d, obs = %d",
              otbn_irq_expected, irq);
        otbn_irq_serviced = irq;

        dif_otbn_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_otbn_irq_get_state(&otbn, &snapshot));
        CHECK(snapshot == (dif_otbn_irq_state_snapshot_t)(1 << irq),
              "Only otbn IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_otbn_irq_acknowledge(&otbn, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 13 && 13 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralOtpCtrl: {
        dif_otp_ctrl_irq_t irq = (dif_otp_ctrl_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdOtpCtrlOtpOperationDone);
        CHECK(irq == otp_ctrl_irq_expected,
              "Incorrect otp_ctrl IRQ triggered: exp = %d, obs = %d",
              otp_ctrl_irq_expected, irq);
        otp_ctrl_irq_serviced = irq;

        dif_otp_ctrl_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_otp_ctrl_irq_get_state(&otp_ctrl, &snapshot));
        CHECK(snapshot == (dif_otp_ctrl_irq_state_snapshot_t)(1 << irq),
              "Only otp_ctrl IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_otp_ctrl_irq_acknowledge(&otp_ctrl, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 14 && 14 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralPattgen: {
        dif_pattgen_irq_t irq = (dif_pattgen_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdPattgenDoneCh0);
        CHECK(irq == pattgen_irq_expected,
              "Incorrect pattgen IRQ triggered: exp = %d, obs = %d",
              pattgen_irq_expected, irq);
        pattgen_irq_serviced = irq;

        dif_pattgen_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_pattgen_irq_get_state(&pattgen, &snapshot));
        CHECK(snapshot == (dif_pattgen_irq_state_snapshot_t)(1 << irq),
              "Only pattgen IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_pattgen_irq_acknowledge(&pattgen, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 15 && 15 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralPwrmgrAon: {
        dif_pwrmgr_irq_t irq = (dif_pwrmgr_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
        CHECK(irq == pwrmgr_irq_expected,
              "Incorrect pwrmgr_aon IRQ triggered: exp = %d, obs = %d",
              pwrmgr_irq_expected, irq);
        pwrmgr_irq_serviced = irq;

        dif_pwrmgr_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_pwrmgr_irq_get_state(&pwrmgr_aon, &snapshot));
        CHECK(snapshot == (dif_pwrmgr_irq_state_snapshot_t)(1 << irq),
              "Only pwrmgr_aon IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr_aon, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 16 && 16 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralRvTimer: {
        dif_rv_timer_irq_t irq = (dif_rv_timer_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdRvTimerTimerExpiredHart0Timer0);
        CHECK(irq == rv_timer_irq_expected,
              "Incorrect rv_timer IRQ triggered: exp = %d, obs = %d",
              rv_timer_irq_expected, irq);
        rv_timer_irq_serviced = irq;

        dif_rv_timer_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_rv_timer_irq_get_state(&rv_timer, kHart, &snapshot));
        CHECK(snapshot == (dif_rv_timer_irq_state_snapshot_t)(1 << irq),
              "Only rv_timer IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_rv_timer_irq_acknowledge(&rv_timer, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 17 && 17 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralSensorCtrlAon: {
        dif_sensor_ctrl_irq_t irq = (dif_sensor_ctrl_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdSensorCtrlAonIoStatusChange);
        CHECK(irq == sensor_ctrl_irq_expected,
              "Incorrect sensor_ctrl_aon IRQ triggered: exp = %d, obs = %d",
              sensor_ctrl_irq_expected, irq);
        sensor_ctrl_irq_serviced = irq;

        dif_sensor_ctrl_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_sensor_ctrl_irq_get_state(&sensor_ctrl_aon, &snapshot));
        CHECK(snapshot == (dif_sensor_ctrl_irq_state_snapshot_t)(1 << irq),
              "Only sensor_ctrl_aon IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        CHECK_DIF_OK(dif_sensor_ctrl_irq_acknowledge(&sensor_ctrl_aon, irq));
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 18 && 18 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralSpiDevice: {
        dif_spi_device_irq_t irq = (dif_spi_device_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty);
        CHECK(irq == spi_device_irq_expected,
              "Incorrect spi_device IRQ triggered: exp = %d, obs = %d",
              spi_device_irq_expected, irq);
        spi_device_irq_serviced = irq;

        dif_spi_device_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_spi_device_irq_get_state(&spi_device, &snapshot));
        CHECK(snapshot == (dif_spi_device_irq_state_snapshot_t)(1 << irq),
              "Only spi_device IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x20 & (1 << irq)) {
          CHECK_DIF_OK(dif_spi_device_irq_force(&spi_device, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_spi_device_irq_set_enabled(&spi_device, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_spi_device_irq_acknowledge(&spi_device, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralSpiHost0: {
        dif_spi_host_irq_t irq = (dif_spi_host_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdSpiHost0Error);
        CHECK(irq == spi_host_irq_expected,
              "Incorrect spi_host0 IRQ triggered: exp = %d, obs = %d",
              spi_host_irq_expected, irq);
        spi_host_irq_serviced = irq;

        dif_spi_host_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_spi_host_irq_get_state(&spi_host0, &snapshot));
        CHECK(snapshot == (dif_spi_host_irq_state_snapshot_t)(1 << irq),
              "Only spi_host0 IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x2 & (1 << irq)) {
          CHECK_DIF_OK(dif_spi_host_irq_force(&spi_host0, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_spi_host_irq_set_enabled(&spi_host0, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_spi_host_irq_acknowledge(&spi_host0, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralSpiHost1: {
        dif_spi_host_irq_t irq = (dif_spi_host_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdSpiHost1Error);
        CHECK(irq == spi_host_irq_expected,
              "Incorrect spi_host1 IRQ triggered: exp = %d, obs = %d",
              spi_host_irq_expected, irq);
        spi_host_irq_serviced = irq;

        dif_spi_host_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_spi_host_irq_get_state(&spi_host1, &snapshot));
        CHECK(snapshot == (dif_spi_host_irq_state_snapshot_t)(1 << irq),
              "Only spi_host1 IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x2 & (1 << irq)) {
          CHECK_DIF_OK(dif_spi_host_irq_force(&spi_host1, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_spi_host_irq_set_enabled(&spi_host1, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_spi_host_irq_acknowledge(&spi_host1, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 20 && 20 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralSysrstCtrlAon: {
        dif_sysrst_ctrl_irq_t irq = (dif_sysrst_ctrl_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected);
        CHECK(irq == sysrst_ctrl_irq_expected,
              "Incorrect sysrst_ctrl_aon IRQ triggered: exp = %d, obs = %d",
              sysrst_ctrl_irq_expected, irq);
        sysrst_ctrl_irq_serviced = irq;

        dif_sysrst_ctrl_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_sysrst_ctrl_irq_get_state(&sysrst_ctrl_aon, &snapshot));
        CHECK(snapshot == (dif_sysrst_ctrl_irq_state_snapshot_t)(1 << irq),
              "Only sysrst_ctrl_aon IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x1 & (1 << irq)) {
          CHECK_DIF_OK(dif_sysrst_ctrl_irq_force(&sysrst_ctrl_aon, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_sysrst_ctrl_irq_set_enabled(&sysrst_ctrl_aon, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_sysrst_ctrl_irq_acknowledge(&sysrst_ctrl_aon, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralUart0: {
        dif_uart_irq_t irq = (dif_uart_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdUart0TxWatermark);
        CHECK(irq == uart_irq_expected,
              "Incorrect uart0 IRQ triggered: exp = %d, obs = %d",
              uart_irq_expected, irq);
        uart_irq_serviced = irq;

        dif_uart_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_uart_irq_get_state(&uart0, &snapshot));
        CHECK(snapshot == (dif_uart_irq_state_snapshot_t)((1 << irq) | 0x1),
              "Expected uart0 interrupt status %x. Actual interrupt "
              "status = %x", (1 << irq) | 0x1, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x3 & (1 << irq)) {
          CHECK_DIF_OK(dif_uart_irq_force(&uart0, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x1 & (1 << irq))) {
            CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart0, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart0, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralUart1: {
        dif_uart_irq_t irq = (dif_uart_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdUart1TxWatermark);
        CHECK(irq == uart_irq_expected,
              "Incorrect uart1 IRQ triggered: exp = %d, obs = %d",
              uart_irq_expected, irq);
        uart_irq_serviced = irq;

        dif_uart_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_uart_irq_get_state(&uart1, &snapshot));
        CHECK(snapshot == (dif_uart_irq_state_snapshot_t)((1 << irq) | 0x1),
              "Expected uart1 interrupt status %x. Actual interrupt "
              "status = %x", (1 << irq) | 0x1, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x3 & (1 << irq)) {
          CHECK_DIF_OK(dif_uart_irq_force(&uart1, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x1 & (1 << irq))) {
            CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart1, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart1, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralUart2: {
        dif_uart_irq_t irq = (dif_uart_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdUart2TxWatermark);
        CHECK(irq == uart_irq_expected,
              "Incorrect uart2 IRQ triggered: exp = %d, obs = %d",
              uart_irq_expected, irq);
        uart_irq_serviced = irq;

        dif_uart_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_uart_irq_get_state(&uart2, &snapshot));
        CHECK(snapshot == (dif_uart_irq_state_snapshot_t)((1 << irq) | 0x1),
              "Expected uart2 interrupt status %x. Actual interrupt "
              "status = %x", (1 << irq) | 0x1, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x3 & (1 << irq)) {
          CHECK_DIF_OK(dif_uart_irq_force(&uart2, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x1 & (1 << irq))) {
            CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart2, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart2, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralUart3: {
        dif_uart_irq_t irq = (dif_uart_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdUart3TxWatermark);
        CHECK(irq == uart_irq_expected,
              "Incorrect uart3 IRQ triggered: exp = %d, obs = %d",
              uart_irq_expected, irq);
        uart_irq_serviced = irq;

        dif_uart_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_uart_irq_get_state(&uart3, &snapshot));
        CHECK(snapshot == (dif_uart_irq_state_snapshot_t)((1 << irq) | 0x1),
              "Expected uart3 interrupt status %x. Actual interrupt "
              "status = %x", (1 << irq) | 0x1, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x3 & (1 << irq)) {
          CHECK_DIF_OK(dif_uart_irq_force(&uart3, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x1 & (1 << irq))) {
            CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart3, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart3, irq));
        }
        break;
      }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 22 && 22 < TEST_MAX_IRQ_PERIPHERAL
      case kTopEarlgreyPlicPeripheralUsbdev: {
        dif_usbdev_irq_t irq = (dif_usbdev_irq_t)(
            plic_irq_id -
            (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdUsbdevPktReceived);
        CHECK(irq == usbdev_irq_expected,
              "Incorrect usbdev IRQ triggered: exp = %d, obs = %d",
              usbdev_irq_expected, irq);
        usbdev_irq_serviced = irq;

        dif_usbdev_irq_state_snapshot_t snapshot;
        CHECK_DIF_OK(dif_usbdev_irq_get_state(&usbdev, &snapshot));
        CHECK(snapshot == (dif_usbdev_irq_state_snapshot_t)(1 << irq),
              "Only usbdev IRQ %d expected to fire. Actual interrupt "
              "status = %x", irq, snapshot);

        // If this is a status type interrupt, we do not have to acknowledge the interrupt at
        // the IP side, but we need to clear the test force register.
        if (0x20183 & (1 << irq)) {
          CHECK_DIF_OK(dif_usbdev_irq_force(&usbdev, irq, false));
          // In case this status interrupt is asserted by default, we also disable it at
          // this point so that it does not interfere with the rest of the test.
          if ((0x0 & (1 << irq))) {
            CHECK_DIF_OK(dif_usbdev_irq_set_enabled(&usbdev, irq, false));
          }
        // If this is a regular event type interrupt, we acknowledge it at this point.
        } else {
          CHECK_DIF_OK(dif_usbdev_irq_acknowledge(&usbdev, irq));
        }
        break;
      }
#endif

      default:
        LOG_FATAL("ISR is not implemented!");
        test_status_set(kTestStatusFailed);
    }
  }
  // Complete the IRQ at PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kHart, plic_irq_id));
}

/**
 * Initializes the handles to all peripherals.
 */
static void peripherals_init(void) {
  mmio_region_t base_addr;

#if TEST_MIN_IRQ_PERIPHERAL <= 0 && 0 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_adc_ctrl_init(base_addr, &adc_ctrl_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 1 && 1 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 2 && 2 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_aon_timer_init(base_addr, &aon_timer_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 3 && 3 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR);
  CHECK_DIF_OK(dif_csrng_init(base_addr, &csrng));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn0));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn1));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 5 && 5 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR);
  CHECK_DIF_OK(dif_entropy_src_init(base_addr, &entropy_src));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 6 && 6 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_flash_ctrl_init(base_addr, &flash_ctrl));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 7 && 7 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR);
  CHECK_DIF_OK(dif_gpio_init(base_addr, &gpio));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 8 && 8 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_hmac_init(base_addr, &hmac));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c0));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C1_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c1));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C2_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c2));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 10 && 10 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR);
  CHECK_DIF_OK(dif_keymgr_init(base_addr, &keymgr));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 11 && 11 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_kmac_init(base_addr, &kmac));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 12 && 12 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);
  CHECK_DIF_OK(dif_otbn_init(base_addr, &otbn));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 13 && 13 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(base_addr, &otp_ctrl));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 14 && 14 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_PATTGEN_BASE_ADDR);
  CHECK_DIF_OK(dif_pattgen_init(base_addr, &pattgen));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 15 && 15 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(base_addr, &pwrmgr_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 16 && 16 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_timer_init(base_addr, &rv_timer));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 17 && 17 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_sensor_ctrl_init(base_addr, &sensor_ctrl_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 18 && 18 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_device_init(base_addr, &spi_device));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host0));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host1));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 20 && 20 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_sysrst_ctrl_init(base_addr, &sysrst_ctrl_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart0));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart1));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART2_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart2));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART3_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart3));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 22 && 22 < TEST_MAX_IRQ_PERIPHERAL
  base_addr = mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR);
  CHECK_DIF_OK(dif_usbdev_init(base_addr, &usbdev));
#endif

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));
}

/**
 * Clears pending IRQs in all peripherals.
 */
static void peripheral_irqs_clear(void) {
#if TEST_MIN_IRQ_PERIPHERAL <= 0 && 0 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_adc_ctrl_irq_acknowledge_all(&adc_ctrl_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 1 && 1 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_alert_handler_irq_acknowledge_all(&alert_handler));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 2 && 2 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_aon_timer_irq_acknowledge_all(&aon_timer_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 3 && 3 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_csrng_irq_acknowledge_all(&csrng));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_edn_irq_acknowledge_all(&edn0));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_edn_irq_acknowledge_all(&edn1));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 5 && 5 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_entropy_src_irq_acknowledge_all(&entropy_src));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 6 && 6 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_flash_ctrl_irq_acknowledge_all(&flash_ctrl));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 7 && 7 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_gpio_irq_acknowledge_all(&gpio));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 8 && 8 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_hmac_irq_acknowledge_all(&hmac));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_i2c_irq_acknowledge_all(&i2c0));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_i2c_irq_acknowledge_all(&i2c1));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_i2c_irq_acknowledge_all(&i2c2));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 10 && 10 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_keymgr_irq_acknowledge_all(&keymgr));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 11 && 11 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_kmac_irq_acknowledge_all(&kmac));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 12 && 12 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_otbn_irq_acknowledge_all(&otbn));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 13 && 13 < TEST_MAX_IRQ_PERIPHERAL
  if (kBootStage != kBootStageOwner) {
    CHECK_DIF_OK(dif_otp_ctrl_irq_acknowledge_all(&otp_ctrl));
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 14 && 14 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_pattgen_irq_acknowledge_all(&pattgen));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 15 && 15 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge_all(&pwrmgr_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 16 && 16 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_rv_timer_irq_acknowledge_all(&rv_timer, kHart));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 17 && 17 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_sensor_ctrl_irq_acknowledge_all(&sensor_ctrl_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 18 && 18 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_spi_device_irq_acknowledge_all(&spi_device));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_spi_host_irq_acknowledge_all(&spi_host0));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_spi_host_irq_acknowledge_all(&spi_host1));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 20 && 20 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_sysrst_ctrl_irq_acknowledge_all(&sysrst_ctrl_aon));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_uart_irq_acknowledge_all(&uart0));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_uart_irq_acknowledge_all(&uart1));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_uart_irq_acknowledge_all(&uart2));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_uart_irq_acknowledge_all(&uart3));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 22 && 22 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(dif_usbdev_irq_acknowledge_all(&usbdev));
#endif
}

/**
 * Enables all IRQs in all peripherals.
 */
static void peripheral_irqs_enable(void) {
#if TEST_MIN_IRQ_PERIPHERAL <= 0 && 0 < TEST_MAX_IRQ_PERIPHERAL
  dif_adc_ctrl_irq_state_snapshot_t adc_ctrl_irqs =
      (dif_adc_ctrl_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 1 && 1 < TEST_MAX_IRQ_PERIPHERAL
  dif_alert_handler_irq_state_snapshot_t alert_handler_irqs =
      (dif_alert_handler_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 3 && 3 < TEST_MAX_IRQ_PERIPHERAL
  dif_csrng_irq_state_snapshot_t csrng_irqs =
      (dif_csrng_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
  dif_edn_irq_state_snapshot_t edn_irqs =
      (dif_edn_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 5 && 5 < TEST_MAX_IRQ_PERIPHERAL
  dif_entropy_src_irq_state_snapshot_t entropy_src_irqs =
      (dif_entropy_src_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 6 && 6 < TEST_MAX_IRQ_PERIPHERAL
  // Note: this peripheral contains status interrupts that are asserted by
  // default. Therefore, not all interrupts are enabled here, since that
  // would interfere with this test. Instead, these interrupts are enabled on
  // demand once they are being tested.
  dif_flash_ctrl_irq_state_snapshot_t flash_ctrl_irqs =
      (dif_flash_ctrl_irq_state_snapshot_t)0xfffffffc;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 7 && 7 < TEST_MAX_IRQ_PERIPHERAL
  dif_gpio_irq_state_snapshot_t gpio_irqs =
      (dif_gpio_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 8 && 8 < TEST_MAX_IRQ_PERIPHERAL
  dif_hmac_irq_state_snapshot_t hmac_irqs =
      (dif_hmac_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  dif_i2c_irq_state_snapshot_t i2c_irqs =
      (dif_i2c_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 10 && 10 < TEST_MAX_IRQ_PERIPHERAL
  dif_keymgr_irq_state_snapshot_t keymgr_irqs =
      (dif_keymgr_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 11 && 11 < TEST_MAX_IRQ_PERIPHERAL
  dif_kmac_irq_state_snapshot_t kmac_irqs =
      (dif_kmac_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 12 && 12 < TEST_MAX_IRQ_PERIPHERAL
  dif_otbn_irq_state_snapshot_t otbn_irqs =
      (dif_otbn_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 13 && 13 < TEST_MAX_IRQ_PERIPHERAL
  dif_otp_ctrl_irq_state_snapshot_t otp_ctrl_irqs =
      (dif_otp_ctrl_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 14 && 14 < TEST_MAX_IRQ_PERIPHERAL
  dif_pattgen_irq_state_snapshot_t pattgen_irqs =
      (dif_pattgen_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 15 && 15 < TEST_MAX_IRQ_PERIPHERAL
  dif_pwrmgr_irq_state_snapshot_t pwrmgr_irqs =
      (dif_pwrmgr_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 16 && 16 < TEST_MAX_IRQ_PERIPHERAL
  dif_rv_timer_irq_state_snapshot_t rv_timer_irqs =
      (dif_rv_timer_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 17 && 17 < TEST_MAX_IRQ_PERIPHERAL
  dif_sensor_ctrl_irq_state_snapshot_t sensor_ctrl_irqs =
      (dif_sensor_ctrl_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 18 && 18 < TEST_MAX_IRQ_PERIPHERAL
  dif_spi_device_irq_state_snapshot_t spi_device_irqs =
      (dif_spi_device_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
  dif_spi_host_irq_state_snapshot_t spi_host_irqs =
      (dif_spi_host_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 20 && 20 < TEST_MAX_IRQ_PERIPHERAL
  dif_sysrst_ctrl_irq_state_snapshot_t sysrst_ctrl_irqs =
      (dif_sysrst_ctrl_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  // Note: this peripheral contains status interrupts that are asserted by
  // default. Therefore, not all interrupts are enabled here, since that
  // would interfere with this test. Instead, these interrupts are enabled on
  // demand once they are being tested.
  dif_uart_irq_state_snapshot_t uart_irqs =
      (dif_uart_irq_state_snapshot_t)0xfffffffe;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 22 && 22 < TEST_MAX_IRQ_PERIPHERAL
  dif_usbdev_irq_state_snapshot_t usbdev_irqs =
      (dif_usbdev_irq_state_snapshot_t)0xffffffff;
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 0 && 0 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_adc_ctrl_irq_restore_all(&adc_ctrl_aon, &adc_ctrl_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 1 && 1 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_alert_handler_irq_restore_all(&alert_handler, &alert_handler_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 3 && 3 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_csrng_irq_restore_all(&csrng, &csrng_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_edn_irq_restore_all(&edn0, &edn_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_edn_irq_restore_all(&edn1, &edn_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 5 && 5 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_entropy_src_irq_restore_all(&entropy_src, &entropy_src_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 6 && 6 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_flash_ctrl_irq_restore_all(&flash_ctrl, &flash_ctrl_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 7 && 7 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_gpio_irq_restore_all(&gpio, &gpio_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 8 && 8 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_hmac_irq_restore_all(&hmac, &hmac_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_i2c_irq_restore_all(&i2c0, &i2c_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_i2c_irq_restore_all(&i2c1, &i2c_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_i2c_irq_restore_all(&i2c2, &i2c_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 10 && 10 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_keymgr_irq_restore_all(&keymgr, &keymgr_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 11 && 11 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_kmac_irq_restore_all(&kmac, &kmac_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 12 && 12 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_otbn_irq_restore_all(&otbn, &otbn_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 13 && 13 < TEST_MAX_IRQ_PERIPHERAL
  if (kBootStage != kBootStageOwner) {
    CHECK_DIF_OK(
        dif_otp_ctrl_irq_restore_all(&otp_ctrl, &otp_ctrl_irqs));
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 14 && 14 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_pattgen_irq_restore_all(&pattgen, &pattgen_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 15 && 15 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_pwrmgr_irq_restore_all(&pwrmgr_aon, &pwrmgr_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 16 && 16 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_rv_timer_irq_restore_all(&rv_timer, kHart, &rv_timer_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 17 && 17 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_sensor_ctrl_irq_restore_all(&sensor_ctrl_aon, &sensor_ctrl_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 18 && 18 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_spi_device_irq_restore_all(&spi_device, &spi_device_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_spi_host_irq_restore_all(&spi_host0, &spi_host_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_spi_host_irq_restore_all(&spi_host1, &spi_host_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 20 && 20 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_sysrst_ctrl_irq_restore_all(&sysrst_ctrl_aon, &sysrst_ctrl_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  if (kDeviceType == kDeviceSimDV) {
    CHECK_DIF_OK(
        dif_uart_irq_restore_all(&uart0, &uart_irqs));
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_uart_irq_restore_all(&uart1, &uart_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_uart_irq_restore_all(&uart2, &uart_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_uart_irq_restore_all(&uart3, &uart_irqs));
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 22 && 22 < TEST_MAX_IRQ_PERIPHERAL
  CHECK_DIF_OK(
      dif_usbdev_irq_restore_all(&usbdev, &usbdev_irqs));
#endif
}

/**
 * Triggers all IRQs in all peripherals one by one.
 *
 * Walks through all instances of all peripherals and triggers an interrupt one
 * by one, by forcing with the `intr_test` CSR. On trigger, the CPU instantly
 * jumps into the ISR. The main flow of execution thus proceeds to check that
 * the correct IRQ was serviced immediately. The ISR, in turn checks if the
 * expected IRQ from the expected peripheral triggered.
 */
static void peripheral_irqs_trigger(void) {
  unsigned int status_default_mask;
  // Depending on the build configuration, this variable may show up as unused
  // in the clang linter. This statement waives that error.
  (void) status_default_mask;

#if TEST_MIN_IRQ_PERIPHERAL <= 0 && 0 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralAdcCtrlAon;
  status_default_mask = 0x0;
  for (dif_adc_ctrl_irq_t irq = kDifAdcCtrlIrqMatchPending;
       irq <= kDifAdcCtrlIrqMatchPending; ++irq) {

    adc_ctrl_irq_expected = irq;
    LOG_INFO("Triggering adc_ctrl_aon IRQ %d.", irq);
    CHECK_DIF_OK(dif_adc_ctrl_irq_force(&adc_ctrl_aon, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_adc_ctrl_irq_set_enabled(&adc_ctrl_aon, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(adc_ctrl_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from adc_ctrl_aon is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 1 && 1 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralAlertHandler;
  for (dif_alert_handler_irq_t irq = kDifAlertHandlerIrqClassa;
       irq <= kDifAlertHandlerIrqClassd; ++irq) {

    alert_handler_irq_expected = irq;
    LOG_INFO("Triggering alert_handler IRQ %d.", irq);
    CHECK_DIF_OK(dif_alert_handler_irq_force(&alert_handler, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(alert_handler_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from alert_handler is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 2 && 2 < TEST_MAX_IRQ_PERIPHERAL
  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  // aon_timer may generate a NMI instead of a PLIC IRQ depending on the ROM.
  // Since there are other tests covering this already, we just skip this for
  // non-DV setups.
  if (kDeviceType == kDeviceSimDV) {
    peripheral_expected = kTopEarlgreyPlicPeripheralAonTimerAon;
    for (dif_aon_timer_irq_t irq = kDifAonTimerIrqWkupTimerExpired;
         irq <= kDifAonTimerIrqWdogTimerBark; ++irq) {

      aon_timer_irq_expected = irq;
      LOG_INFO("Triggering aon_timer_aon IRQ %d.", irq);
      CHECK_DIF_OK(dif_aon_timer_irq_force(&aon_timer_aon, irq, true));

      // This avoids a race where *irq_serviced is read before
      // entering the ISR.
      IBEX_SPIN_FOR(aon_timer_irq_serviced == irq, 1);
      LOG_INFO("IRQ %d from aon_timer_aon is serviced.", irq);
    }
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 3 && 3 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralCsrng;
  for (dif_csrng_irq_t irq = kDifCsrngIrqCsCmdReqDone;
       irq <= kDifCsrngIrqCsFatalErr; ++irq) {

    csrng_irq_expected = irq;
    LOG_INFO("Triggering csrng IRQ %d.", irq);
    CHECK_DIF_OK(dif_csrng_irq_force(&csrng, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(csrng_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from csrng is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralEdn0;
  for (dif_edn_irq_t irq = kDifEdnIrqEdnCmdReqDone;
       irq <= kDifEdnIrqEdnFatalErr; ++irq) {

    edn_irq_expected = irq;
    LOG_INFO("Triggering edn0 IRQ %d.", irq);
    CHECK_DIF_OK(dif_edn_irq_force(&edn0, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(edn_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from edn0 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 4 && 4 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralEdn1;
  for (dif_edn_irq_t irq = kDifEdnIrqEdnCmdReqDone;
       irq <= kDifEdnIrqEdnFatalErr; ++irq) {

    edn_irq_expected = irq;
    LOG_INFO("Triggering edn1 IRQ %d.", irq);
    CHECK_DIF_OK(dif_edn_irq_force(&edn1, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(edn_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from edn1 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 5 && 5 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralEntropySrc;
  for (dif_entropy_src_irq_t irq = kDifEntropySrcIrqEsEntropyValid;
       irq <= kDifEntropySrcIrqEsFatalErr; ++irq) {

    entropy_src_irq_expected = irq;
    LOG_INFO("Triggering entropy_src IRQ %d.", irq);
    CHECK_DIF_OK(dif_entropy_src_irq_force(&entropy_src, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(entropy_src_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from entropy_src is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 6 && 6 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralFlashCtrl;
  status_default_mask = 0x3;
  for (dif_flash_ctrl_irq_t irq = kDifFlashCtrlIrqProgEmpty;
       irq <= kDifFlashCtrlIrqCorrErr; ++irq) {

    flash_ctrl_irq_expected = irq;
    LOG_INFO("Triggering flash_ctrl IRQ %d.", irq);
    CHECK_DIF_OK(dif_flash_ctrl_irq_force(&flash_ctrl, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_flash_ctrl_irq_set_enabled(&flash_ctrl, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(flash_ctrl_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from flash_ctrl is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 7 && 7 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralGpio;
  for (dif_gpio_irq_t irq = kDifGpioIrqGpio0;
       irq <= kDifGpioIrqGpio31; ++irq) {

    gpio_irq_expected = irq;
    LOG_INFO("Triggering gpio IRQ %d.", irq);
    CHECK_DIF_OK(dif_gpio_irq_force(&gpio, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(gpio_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from gpio is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 8 && 8 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralHmac;
  status_default_mask = 0x0;
  for (dif_hmac_irq_t irq = kDifHmacIrqHmacDone;
       irq <= kDifHmacIrqHmacErr; ++irq) {

    hmac_irq_expected = irq;
    LOG_INFO("Triggering hmac IRQ %d.", irq);
    CHECK_DIF_OK(dif_hmac_irq_force(&hmac, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_hmac_irq_set_enabled(&hmac, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(hmac_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from hmac is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralI2c0;
  status_default_mask = 0x0;
  for (dif_i2c_irq_t irq = kDifI2cIrqFmtThreshold;
       irq <= kDifI2cIrqHostTimeout; ++irq) {

    i2c_irq_expected = irq;
    LOG_INFO("Triggering i2c0 IRQ %d.", irq);
    CHECK_DIF_OK(dif_i2c_irq_force(&i2c0, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_i2c_irq_set_enabled(&i2c0, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(i2c_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from i2c0 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralI2c1;
  status_default_mask = 0x0;
  for (dif_i2c_irq_t irq = kDifI2cIrqFmtThreshold;
       irq <= kDifI2cIrqHostTimeout; ++irq) {

    i2c_irq_expected = irq;
    LOG_INFO("Triggering i2c1 IRQ %d.", irq);
    CHECK_DIF_OK(dif_i2c_irq_force(&i2c1, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_i2c_irq_set_enabled(&i2c1, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(i2c_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from i2c1 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 9 && 9 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralI2c2;
  status_default_mask = 0x0;
  for (dif_i2c_irq_t irq = kDifI2cIrqFmtThreshold;
       irq <= kDifI2cIrqHostTimeout; ++irq) {

    i2c_irq_expected = irq;
    LOG_INFO("Triggering i2c2 IRQ %d.", irq);
    CHECK_DIF_OK(dif_i2c_irq_force(&i2c2, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_i2c_irq_set_enabled(&i2c2, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(i2c_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from i2c2 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 10 && 10 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralKeymgr;
  for (dif_keymgr_irq_t irq = kDifKeymgrIrqOpDone;
       irq <= kDifKeymgrIrqOpDone; ++irq) {

    keymgr_irq_expected = irq;
    LOG_INFO("Triggering keymgr IRQ %d.", irq);
    CHECK_DIF_OK(dif_keymgr_irq_force(&keymgr, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(keymgr_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from keymgr is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 11 && 11 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralKmac;
  status_default_mask = 0x0;
  for (dif_kmac_irq_t irq = kDifKmacIrqKmacDone;
       irq <= kDifKmacIrqKmacErr; ++irq) {

    kmac_irq_expected = irq;
    LOG_INFO("Triggering kmac IRQ %d.", irq);
    CHECK_DIF_OK(dif_kmac_irq_force(&kmac, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_kmac_irq_set_enabled(&kmac, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(kmac_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from kmac is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 12 && 12 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralOtbn;
  for (dif_otbn_irq_t irq = kDifOtbnIrqDone;
       irq <= kDifOtbnIrqDone; ++irq) {

    otbn_irq_expected = irq;
    LOG_INFO("Triggering otbn IRQ %d.", irq);
    CHECK_DIF_OK(dif_otbn_irq_force(&otbn, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(otbn_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from otbn is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 13 && 13 < TEST_MAX_IRQ_PERIPHERAL
  // Skip OTP_CTRL in boot stage owner since ROM_EXT configures all accesses
  // to OTP_CTRL and AST to be illegal.
  if (kBootStage != kBootStageOwner) {
    peripheral_expected = kTopEarlgreyPlicPeripheralOtpCtrl;
    for (dif_otp_ctrl_irq_t irq = kDifOtpCtrlIrqOtpOperationDone;
         irq <= kDifOtpCtrlIrqOtpError; ++irq) {

      otp_ctrl_irq_expected = irq;
      LOG_INFO("Triggering otp_ctrl IRQ %d.", irq);
      CHECK_DIF_OK(dif_otp_ctrl_irq_force(&otp_ctrl, irq, true));

      // This avoids a race where *irq_serviced is read before
      // entering the ISR.
      IBEX_SPIN_FOR(otp_ctrl_irq_serviced == irq, 1);
      LOG_INFO("IRQ %d from otp_ctrl is serviced.", irq);
    }
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 14 && 14 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralPattgen;
  for (dif_pattgen_irq_t irq = kDifPattgenIrqDoneCh0;
       irq <= kDifPattgenIrqDoneCh1; ++irq) {

    pattgen_irq_expected = irq;
    LOG_INFO("Triggering pattgen IRQ %d.", irq);
    CHECK_DIF_OK(dif_pattgen_irq_force(&pattgen, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(pattgen_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from pattgen is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 15 && 15 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralPwrmgrAon;
  for (dif_pwrmgr_irq_t irq = kDifPwrmgrIrqWakeup;
       irq <= kDifPwrmgrIrqWakeup; ++irq) {

    pwrmgr_irq_expected = irq;
    LOG_INFO("Triggering pwrmgr_aon IRQ %d.", irq);
    CHECK_DIF_OK(dif_pwrmgr_irq_force(&pwrmgr_aon, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(pwrmgr_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from pwrmgr_aon is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 16 && 16 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralRvTimer;
  for (dif_rv_timer_irq_t irq = kDifRvTimerIrqTimerExpiredHart0Timer0;
       irq <= kDifRvTimerIrqTimerExpiredHart0Timer0; ++irq) {

    rv_timer_irq_expected = irq;
    LOG_INFO("Triggering rv_timer IRQ %d.", irq);
    CHECK_DIF_OK(dif_rv_timer_irq_force(&rv_timer, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(rv_timer_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from rv_timer is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 17 && 17 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralSensorCtrlAon;
  for (dif_sensor_ctrl_irq_t irq = kDifSensorCtrlIrqIoStatusChange;
       irq <= kDifSensorCtrlIrqInitStatusChange; ++irq) {

    sensor_ctrl_irq_expected = irq;
    LOG_INFO("Triggering sensor_ctrl_aon IRQ %d.", irq);
    CHECK_DIF_OK(dif_sensor_ctrl_irq_force(&sensor_ctrl_aon, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(sensor_ctrl_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from sensor_ctrl_aon is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 18 && 18 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralSpiDevice;
  status_default_mask = 0x0;
  for (dif_spi_device_irq_t irq = kDifSpiDeviceIrqUploadCmdfifoNotEmpty;
       irq <= kDifSpiDeviceIrqTpmRdfifoDrop; ++irq) {

    spi_device_irq_expected = irq;
    LOG_INFO("Triggering spi_device IRQ %d.", irq);
    CHECK_DIF_OK(dif_spi_device_irq_force(&spi_device, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_spi_device_irq_set_enabled(&spi_device, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(spi_device_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from spi_device is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralSpiHost0;
  status_default_mask = 0x0;
  for (dif_spi_host_irq_t irq = kDifSpiHostIrqError;
       irq <= kDifSpiHostIrqSpiEvent; ++irq) {

    spi_host_irq_expected = irq;
    LOG_INFO("Triggering spi_host0 IRQ %d.", irq);
    CHECK_DIF_OK(dif_spi_host_irq_force(&spi_host0, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_spi_host_irq_set_enabled(&spi_host0, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(spi_host_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from spi_host0 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 19 && 19 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralSpiHost1;
  status_default_mask = 0x0;
  for (dif_spi_host_irq_t irq = kDifSpiHostIrqError;
       irq <= kDifSpiHostIrqSpiEvent; ++irq) {

    spi_host_irq_expected = irq;
    LOG_INFO("Triggering spi_host1 IRQ %d.", irq);
    CHECK_DIF_OK(dif_spi_host_irq_force(&spi_host1, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_spi_host_irq_set_enabled(&spi_host1, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(spi_host_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from spi_host1 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 20 && 20 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralSysrstCtrlAon;
  status_default_mask = 0x0;
  for (dif_sysrst_ctrl_irq_t irq = kDifSysrstCtrlIrqEventDetected;
       irq <= kDifSysrstCtrlIrqEventDetected; ++irq) {

    sysrst_ctrl_irq_expected = irq;
    LOG_INFO("Triggering sysrst_ctrl_aon IRQ %d.", irq);
    CHECK_DIF_OK(dif_sysrst_ctrl_irq_force(&sysrst_ctrl_aon, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_sysrst_ctrl_irq_set_enabled(&sysrst_ctrl_aon, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(sysrst_ctrl_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from sysrst_ctrl_aon is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  // aon_timer may generate a NMI instead of a PLIC IRQ depending on the ROM.
  // Since there are other tests covering this already, we just skip this for
  // non-DV setups.
  if (kDeviceType == kDeviceSimDV) {
    peripheral_expected = kTopEarlgreyPlicPeripheralUart0;
    status_default_mask = 0x1;
    for (dif_uart_irq_t irq = kDifUartIrqTxWatermark;
         irq <= kDifUartIrqRxParityErr; ++irq) {

      uart_irq_expected = irq;
      LOG_INFO("Triggering uart0 IRQ %d.", irq);
      CHECK_DIF_OK(dif_uart_irq_force(&uart0, irq, true));

      // In this case, the interrupt has not been enabled yet because that would
      // interfere with testing other interrupts. We enable it here and let the
      // interrupt handler disable it again.
      if ((status_default_mask & 0x1)) {
         CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart0, irq, true));
      }
      status_default_mask >>= 1;

      // This avoids a race where *irq_serviced is read before
      // entering the ISR.
      IBEX_SPIN_FOR(uart_irq_serviced == irq, 1);
      LOG_INFO("IRQ %d from uart0 is serviced.", irq);
    }
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralUart1;
  status_default_mask = 0x1;
  for (dif_uart_irq_t irq = kDifUartIrqTxWatermark;
       irq <= kDifUartIrqRxParityErr; ++irq) {

    uart_irq_expected = irq;
    LOG_INFO("Triggering uart1 IRQ %d.", irq);
    CHECK_DIF_OK(dif_uart_irq_force(&uart1, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart1, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(uart_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from uart1 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralUart2;
  status_default_mask = 0x1;
  for (dif_uart_irq_t irq = kDifUartIrqTxWatermark;
       irq <= kDifUartIrqRxParityErr; ++irq) {

    uart_irq_expected = irq;
    LOG_INFO("Triggering uart2 IRQ %d.", irq);
    CHECK_DIF_OK(dif_uart_irq_force(&uart2, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart2, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(uart_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from uart2 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 21 && 21 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralUart3;
  status_default_mask = 0x1;
  for (dif_uart_irq_t irq = kDifUartIrqTxWatermark;
       irq <= kDifUartIrqRxParityErr; ++irq) {

    uart_irq_expected = irq;
    LOG_INFO("Triggering uart3 IRQ %d.", irq);
    CHECK_DIF_OK(dif_uart_irq_force(&uart3, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart3, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(uart_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from uart3 is serviced.", irq);
  }
#endif

#if TEST_MIN_IRQ_PERIPHERAL <= 22 && 22 < TEST_MAX_IRQ_PERIPHERAL
  peripheral_expected = kTopEarlgreyPlicPeripheralUsbdev;
  status_default_mask = 0x0;
  for (dif_usbdev_irq_t irq = kDifUsbdevIrqPktReceived;
       irq <= kDifUsbdevIrqAvSetupEmpty; ++irq) {

    usbdev_irq_expected = irq;
    LOG_INFO("Triggering usbdev IRQ %d.", irq);
    CHECK_DIF_OK(dif_usbdev_irq_force(&usbdev, irq, true));

    // In this case, the interrupt has not been enabled yet because that would
    // interfere with testing other interrupts. We enable it here and let the
    // interrupt handler disable it again.
    if ((status_default_mask & 0x1)) {
       CHECK_DIF_OK(dif_usbdev_irq_set_enabled(&usbdev, irq, true));
    }
    status_default_mask >>= 1;

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(usbdev_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from usbdev is serviced.", irq);
  }
#endif
}

/**
 * Checks that the target ID corresponds to the ID of the hart on which
 * this test is executed on. This check is meant to be used in a
 * single-hart system only.
 */
static void check_hart_id(uint32_t exp_hart_id) {
  uint32_t act_hart_id;
  CSR_READ(CSR_REG_MHARTID, &act_hart_id);
  CHECK(act_hart_id == exp_hart_id, "Processor has unexpected HART ID.");
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  peripherals_init();
  check_hart_id((uint32_t)kHart);
  rv_plic_testutils_irq_range_enable(
      &plic, kHart, kTopEarlgreyPlicIrqIdNone + 1, kTopEarlgreyPlicIrqIdLast);
  peripheral_irqs_clear();
  peripheral_irqs_enable();
  peripheral_irqs_trigger();
  return true;
}

// clang-format on
