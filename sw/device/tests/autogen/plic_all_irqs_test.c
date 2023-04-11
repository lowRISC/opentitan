// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// clang-format off
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
// -o hw/top_earlgrey
#include <limits.h>

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

static dif_adc_ctrl_t adc_ctrl_aon;
static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer_aon;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_entropy_src_t entropy_src;
static dif_flash_ctrl_t flash_ctrl;
static dif_gpio_t gpio;
static dif_hmac_t hmac;
static dif_i2c_t i2c0;
static dif_i2c_t i2c1;
static dif_i2c_t i2c2;
static dif_keymgr_t keymgr;
static dif_kmac_t kmac;
static dif_otbn_t otbn;
static dif_otp_ctrl_t otp_ctrl;
static dif_pattgen_t pattgen;
static dif_pwrmgr_t pwrmgr_aon;
static dif_rv_timer_t rv_timer;
static dif_sensor_ctrl_t sensor_ctrl_aon;
static dif_spi_device_t spi_device;
static dif_spi_host_t spi_host0;
static dif_spi_host_t spi_host1;
static dif_sysrst_ctrl_t sysrst_ctrl_aon;
static dif_uart_t uart0;
static dif_uart_t uart1;
static dif_uart_t uart2;
static dif_uart_t uart3;
static dif_usbdev_t usbdev;
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
static volatile dif_adc_ctrl_irq_t adc_ctrl_irq_expected;
static volatile dif_adc_ctrl_irq_t adc_ctrl_irq_serviced;
static volatile dif_alert_handler_irq_t alert_handler_irq_expected;
static volatile dif_alert_handler_irq_t alert_handler_irq_serviced;
static volatile dif_aon_timer_irq_t aon_timer_irq_expected;
static volatile dif_aon_timer_irq_t aon_timer_irq_serviced;
static volatile dif_csrng_irq_t csrng_irq_expected;
static volatile dif_csrng_irq_t csrng_irq_serviced;
static volatile dif_edn_irq_t edn_irq_expected;
static volatile dif_edn_irq_t edn_irq_serviced;
static volatile dif_entropy_src_irq_t entropy_src_irq_expected;
static volatile dif_entropy_src_irq_t entropy_src_irq_serviced;
static volatile dif_flash_ctrl_irq_t flash_ctrl_irq_expected;
static volatile dif_flash_ctrl_irq_t flash_ctrl_irq_serviced;
static volatile dif_gpio_irq_t gpio_irq_expected;
static volatile dif_gpio_irq_t gpio_irq_serviced;
static volatile dif_hmac_irq_t hmac_irq_expected;
static volatile dif_hmac_irq_t hmac_irq_serviced;
static volatile dif_i2c_irq_t i2c_irq_expected;
static volatile dif_i2c_irq_t i2c_irq_serviced;
static volatile dif_keymgr_irq_t keymgr_irq_expected;
static volatile dif_keymgr_irq_t keymgr_irq_serviced;
static volatile dif_kmac_irq_t kmac_irq_expected;
static volatile dif_kmac_irq_t kmac_irq_serviced;
static volatile dif_otbn_irq_t otbn_irq_expected;
static volatile dif_otbn_irq_t otbn_irq_serviced;
static volatile dif_otp_ctrl_irq_t otp_ctrl_irq_expected;
static volatile dif_otp_ctrl_irq_t otp_ctrl_irq_serviced;
static volatile dif_pattgen_irq_t pattgen_irq_expected;
static volatile dif_pattgen_irq_t pattgen_irq_serviced;
static volatile dif_pwrmgr_irq_t pwrmgr_irq_expected;
static volatile dif_pwrmgr_irq_t pwrmgr_irq_serviced;
static volatile dif_rv_timer_irq_t rv_timer_irq_expected;
static volatile dif_rv_timer_irq_t rv_timer_irq_serviced;
static volatile dif_sensor_ctrl_irq_t sensor_ctrl_irq_expected;
static volatile dif_sensor_ctrl_irq_t sensor_ctrl_irq_serviced;
static volatile dif_spi_device_irq_t spi_device_irq_expected;
static volatile dif_spi_device_irq_t spi_device_irq_serviced;
static volatile dif_spi_host_irq_t spi_host_irq_expected;
static volatile dif_spi_host_irq_t spi_host_irq_serviced;
static volatile dif_sysrst_ctrl_irq_t sysrst_ctrl_irq_expected;
static volatile dif_sysrst_ctrl_irq_t sysrst_ctrl_irq_serviced;
static volatile dif_uart_irq_t uart_irq_expected;
static volatile dif_uart_irq_t uart_irq_serviced;
static volatile dif_usbdev_irq_t usbdev_irq_expected;
static volatile dif_usbdev_irq_t usbdev_irq_serviced;

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
void ottf_external_isr(void) {
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kHart, &plic_irq_id));

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == peripheral_expected,
        "Interrupt from incorrect peripheral: exp = %d, obs = %d",
        peripheral_expected, peripheral);

  switch (peripheral) {
    case kTopEarlgreyPlicPeripheralAdcCtrlAon: {
      dif_adc_ctrl_irq_t irq = (dif_adc_ctrl_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdAdcCtrlAonMatchDone);
      CHECK(irq == adc_ctrl_irq_expected,
            "Incorrect adc_ctrl_aon IRQ triggered: exp = %d, obs = %d",
            adc_ctrl_irq_expected, irq);
      adc_ctrl_irq_serviced = irq;

      dif_adc_ctrl_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_adc_ctrl_irq_get_state(&adc_ctrl_aon, &snapshot));
      CHECK(snapshot == (dif_adc_ctrl_irq_state_snapshot_t)(1 << irq),
            "Only adc_ctrl_aon IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_adc_ctrl_irq_force(&adc_ctrl_aon, irq, false));
      CHECK_DIF_OK(dif_adc_ctrl_irq_acknowledge(&adc_ctrl_aon, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_alert_handler_irq_force(&alert_handler, irq, false));
      CHECK_DIF_OK(dif_alert_handler_irq_acknowledge(&alert_handler, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_aon_timer_irq_force(&aon_timer_aon, irq, false));
      CHECK_DIF_OK(dif_aon_timer_irq_acknowledge(&aon_timer_aon, irq));
      break;
    }

    case kTopEarlgreyPlicPeripheralCsrng: {
      dif_csrng_irq_t irq = (dif_csrng_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone);
      CHECK(irq == csrng_irq_expected,
            "Incorrect csrng IRQ triggered: exp = %d, obs = %d",
            csrng_irq_expected, irq);
      csrng_irq_serviced = irq;

      dif_csrng_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_csrng_irq_get_state(&csrng, &snapshot));
      CHECK(snapshot == (dif_csrng_irq_state_snapshot_t)(1 << irq),
            "Only csrng IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_csrng_irq_force(&csrng, irq, false));
      CHECK_DIF_OK(dif_csrng_irq_acknowledge(&csrng, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_edn_irq_force(&edn0, irq, false));
      CHECK_DIF_OK(dif_edn_irq_acknowledge(&edn0, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_edn_irq_force(&edn1, irq, false));
      CHECK_DIF_OK(dif_edn_irq_acknowledge(&edn1, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_entropy_src_irq_force(&entropy_src, irq, false));
      CHECK_DIF_OK(dif_entropy_src_irq_acknowledge(&entropy_src, irq));
      break;
    }

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
      CHECK(snapshot == (dif_flash_ctrl_irq_state_snapshot_t)(1 << irq),
            "Only flash_ctrl IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_flash_ctrl_irq_force(&flash_ctrl, irq, false));
      CHECK_DIF_OK(dif_flash_ctrl_irq_acknowledge(&flash_ctrl, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_gpio_irq_force(&gpio, irq, false));
      CHECK_DIF_OK(dif_gpio_irq_acknowledge(&gpio, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_hmac_irq_force(&hmac, irq, false));
      CHECK_DIF_OK(dif_hmac_irq_acknowledge(&hmac, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_i2c_irq_force(&i2c0, irq, false));
      CHECK_DIF_OK(dif_i2c_irq_acknowledge(&i2c0, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_i2c_irq_force(&i2c1, irq, false));
      CHECK_DIF_OK(dif_i2c_irq_acknowledge(&i2c1, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_i2c_irq_force(&i2c2, irq, false));
      CHECK_DIF_OK(dif_i2c_irq_acknowledge(&i2c2, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_keymgr_irq_force(&keymgr, irq, false));
      CHECK_DIF_OK(dif_keymgr_irq_acknowledge(&keymgr, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_kmac_irq_force(&kmac, irq, false));
      CHECK_DIF_OK(dif_kmac_irq_acknowledge(&kmac, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_otbn_irq_force(&otbn, irq, false));
      CHECK_DIF_OK(dif_otbn_irq_acknowledge(&otbn, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_otp_ctrl_irq_force(&otp_ctrl, irq, false));
      CHECK_DIF_OK(dif_otp_ctrl_irq_acknowledge(&otp_ctrl, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_pattgen_irq_force(&pattgen, irq, false));
      CHECK_DIF_OK(dif_pattgen_irq_acknowledge(&pattgen, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_pwrmgr_irq_force(&pwrmgr_aon, irq, false));
      CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr_aon, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_rv_timer_irq_force(&rv_timer, irq, false));
      CHECK_DIF_OK(dif_rv_timer_irq_acknowledge(&rv_timer, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_sensor_ctrl_irq_force(&sensor_ctrl_aon, irq, false));
      CHECK_DIF_OK(dif_sensor_ctrl_irq_acknowledge(&sensor_ctrl_aon, irq));
      break;
    }

    case kTopEarlgreyPlicPeripheralSpiDevice: {
      dif_spi_device_irq_t irq = (dif_spi_device_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopEarlgreyPlicIrqIdSpiDeviceGenericRxFull);
      CHECK(irq == spi_device_irq_expected,
            "Incorrect spi_device IRQ triggered: exp = %d, obs = %d",
            spi_device_irq_expected, irq);
      spi_device_irq_serviced = irq;

      dif_spi_device_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_spi_device_irq_get_state(&spi_device, &snapshot));
      CHECK(snapshot == (dif_spi_device_irq_state_snapshot_t)(1 << irq),
            "Only spi_device IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_spi_device_irq_force(&spi_device, irq, false));
      CHECK_DIF_OK(dif_spi_device_irq_acknowledge(&spi_device, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_spi_host_irq_force(&spi_host0, irq, false));
      CHECK_DIF_OK(dif_spi_host_irq_acknowledge(&spi_host0, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_spi_host_irq_force(&spi_host1, irq, false));
      CHECK_DIF_OK(dif_spi_host_irq_acknowledge(&spi_host1, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_sysrst_ctrl_irq_force(&sysrst_ctrl_aon, irq, false));
      CHECK_DIF_OK(dif_sysrst_ctrl_irq_acknowledge(&sysrst_ctrl_aon, irq));
      break;
    }

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
      CHECK(snapshot == (dif_uart_irq_state_snapshot_t)(1 << irq),
            "Only uart0 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_uart_irq_force(&uart0, irq, false));
      CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart0, irq));
      break;
    }

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
      CHECK(snapshot == (dif_uart_irq_state_snapshot_t)(1 << irq),
            "Only uart1 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_uart_irq_force(&uart1, irq, false));
      CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart1, irq));
      break;
    }

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
      CHECK(snapshot == (dif_uart_irq_state_snapshot_t)(1 << irq),
            "Only uart2 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_uart_irq_force(&uart2, irq, false));
      CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart2, irq));
      break;
    }

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
      CHECK(snapshot == (dif_uart_irq_state_snapshot_t)(1 << irq),
            "Only uart3 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_uart_irq_force(&uart3, irq, false));
      CHECK_DIF_OK(dif_uart_irq_acknowledge(&uart3, irq));
      break;
    }

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
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_usbdev_irq_force(&usbdev, irq, false));
      CHECK_DIF_OK(dif_usbdev_irq_acknowledge(&usbdev, irq));
      break;
    }

    default:
      LOG_FATAL("ISR is not implemented!");
      test_status_set(kTestStatusFailed);
  }

  // Complete the IRQ at PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic, kHart, plic_irq_id));
}

/**
 * Initializes the handles to all peripherals.
 */
static void peripherals_init(void) {
  mmio_region_t base_addr;

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_adc_ctrl_init(base_addr, &adc_ctrl_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_aon_timer_init(base_addr, &aon_timer_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_CSRNG_BASE_ADDR);
  CHECK_DIF_OK(dif_csrng_init(base_addr, &csrng));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN0_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn0));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_EDN1_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn1));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR);
  CHECK_DIF_OK(dif_entropy_src_init(base_addr, &entropy_src));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_flash_ctrl_init(base_addr, &flash_ctrl));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR);
  CHECK_DIF_OK(dif_gpio_init(base_addr, &gpio));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_hmac_init(base_addr, &hmac));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C0_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c0));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C1_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c1));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_I2C2_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c2));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_KEYMGR_BASE_ADDR);
  CHECK_DIF_OK(dif_keymgr_init(base_addr, &keymgr));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_kmac_init(base_addr, &kmac));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);
  CHECK_DIF_OK(dif_otbn_init(base_addr, &otbn));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(base_addr, &otp_ctrl));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PATTGEN_BASE_ADDR);
  CHECK_DIF_OK(dif_pattgen_init(base_addr, &pattgen));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(base_addr, &pwrmgr_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_TIMER_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_timer_init(base_addr, &rv_timer));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_sensor_ctrl_init(base_addr, &sensor_ctrl_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_device_init(base_addr, &spi_device));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host0));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host1));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_sysrst_ctrl_init(base_addr, &sysrst_ctrl_aon));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart0));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART1_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart1));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART2_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart2));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_UART3_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart3));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR);
  CHECK_DIF_OK(dif_usbdev_init(base_addr, &usbdev));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));
}

/**
 * Clears pending IRQs in all peripherals.
 */
static void peripheral_irqs_clear(void) {
  CHECK_DIF_OK(dif_adc_ctrl_irq_acknowledge_all(&adc_ctrl_aon));
  CHECK_DIF_OK(dif_alert_handler_irq_acknowledge_all(&alert_handler));
  CHECK_DIF_OK(dif_aon_timer_irq_acknowledge_all(&aon_timer_aon));
  CHECK_DIF_OK(dif_csrng_irq_acknowledge_all(&csrng));
  CHECK_DIF_OK(dif_edn_irq_acknowledge_all(&edn0));
  CHECK_DIF_OK(dif_edn_irq_acknowledge_all(&edn1));
  CHECK_DIF_OK(dif_entropy_src_irq_acknowledge_all(&entropy_src));
  CHECK_DIF_OK(dif_flash_ctrl_irq_acknowledge_all(&flash_ctrl));
  CHECK_DIF_OK(dif_gpio_irq_acknowledge_all(&gpio));
  CHECK_DIF_OK(dif_hmac_irq_acknowledge_all(&hmac));
  CHECK_DIF_OK(dif_i2c_irq_acknowledge_all(&i2c0));
  CHECK_DIF_OK(dif_i2c_irq_acknowledge_all(&i2c1));
  CHECK_DIF_OK(dif_i2c_irq_acknowledge_all(&i2c2));
  CHECK_DIF_OK(dif_keymgr_irq_acknowledge_all(&keymgr));
  CHECK_DIF_OK(dif_kmac_irq_acknowledge_all(&kmac));
  CHECK_DIF_OK(dif_otbn_irq_acknowledge_all(&otbn));
  CHECK_DIF_OK(dif_otp_ctrl_irq_acknowledge_all(&otp_ctrl));
  CHECK_DIF_OK(dif_pattgen_irq_acknowledge_all(&pattgen));
  CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge_all(&pwrmgr_aon));
  CHECK_DIF_OK(dif_rv_timer_irq_acknowledge_all(&rv_timer, kHart));
  CHECK_DIF_OK(dif_sensor_ctrl_irq_acknowledge_all(&sensor_ctrl_aon));
  CHECK_DIF_OK(dif_spi_device_irq_acknowledge_all(&spi_device));
  CHECK_DIF_OK(dif_spi_host_irq_acknowledge_all(&spi_host0));
  CHECK_DIF_OK(dif_spi_host_irq_acknowledge_all(&spi_host1));
  CHECK_DIF_OK(dif_sysrst_ctrl_irq_acknowledge_all(&sysrst_ctrl_aon));
  CHECK_DIF_OK(dif_uart_irq_acknowledge_all(&uart0));
  CHECK_DIF_OK(dif_uart_irq_acknowledge_all(&uart1));
  CHECK_DIF_OK(dif_uart_irq_acknowledge_all(&uart2));
  CHECK_DIF_OK(dif_uart_irq_acknowledge_all(&uart3));
  CHECK_DIF_OK(dif_usbdev_irq_acknowledge_all(&usbdev));
}

/**
 * Enables all IRQs in all peripherals.
 */
static void peripheral_irqs_enable(void) {
  dif_adc_ctrl_irq_state_snapshot_t adc_ctrl_irqs =
      (dif_adc_ctrl_irq_state_snapshot_t)UINT_MAX;
  dif_alert_handler_irq_state_snapshot_t alert_handler_irqs =
      (dif_alert_handler_irq_state_snapshot_t)UINT_MAX;
  dif_csrng_irq_state_snapshot_t csrng_irqs =
      (dif_csrng_irq_state_snapshot_t)UINT_MAX;
  dif_edn_irq_state_snapshot_t edn_irqs =
      (dif_edn_irq_state_snapshot_t)UINT_MAX;
  dif_entropy_src_irq_state_snapshot_t entropy_src_irqs =
      (dif_entropy_src_irq_state_snapshot_t)UINT_MAX;
  dif_flash_ctrl_irq_state_snapshot_t flash_ctrl_irqs =
      (dif_flash_ctrl_irq_state_snapshot_t)UINT_MAX;
  dif_gpio_irq_state_snapshot_t gpio_irqs =
      (dif_gpio_irq_state_snapshot_t)UINT_MAX;
  dif_hmac_irq_state_snapshot_t hmac_irqs =
      (dif_hmac_irq_state_snapshot_t)UINT_MAX;
  dif_i2c_irq_state_snapshot_t i2c_irqs =
      (dif_i2c_irq_state_snapshot_t)UINT_MAX;
  dif_keymgr_irq_state_snapshot_t keymgr_irqs =
      (dif_keymgr_irq_state_snapshot_t)UINT_MAX;
  dif_kmac_irq_state_snapshot_t kmac_irqs =
      (dif_kmac_irq_state_snapshot_t)UINT_MAX;
  dif_otbn_irq_state_snapshot_t otbn_irqs =
      (dif_otbn_irq_state_snapshot_t)UINT_MAX;
  dif_otp_ctrl_irq_state_snapshot_t otp_ctrl_irqs =
      (dif_otp_ctrl_irq_state_snapshot_t)UINT_MAX;
  dif_pattgen_irq_state_snapshot_t pattgen_irqs =
      (dif_pattgen_irq_state_snapshot_t)UINT_MAX;
  dif_pwrmgr_irq_state_snapshot_t pwrmgr_irqs =
      (dif_pwrmgr_irq_state_snapshot_t)UINT_MAX;
  dif_rv_timer_irq_state_snapshot_t rv_timer_irqs =
      (dif_rv_timer_irq_state_snapshot_t)UINT_MAX;
  dif_sensor_ctrl_irq_state_snapshot_t sensor_ctrl_irqs =
      (dif_sensor_ctrl_irq_state_snapshot_t)UINT_MAX;
  dif_spi_device_irq_state_snapshot_t spi_device_irqs =
      (dif_spi_device_irq_state_snapshot_t)UINT_MAX;
  dif_spi_host_irq_state_snapshot_t spi_host_irqs =
      (dif_spi_host_irq_state_snapshot_t)UINT_MAX;
  dif_sysrst_ctrl_irq_state_snapshot_t sysrst_ctrl_irqs =
      (dif_sysrst_ctrl_irq_state_snapshot_t)UINT_MAX;
  dif_uart_irq_state_snapshot_t uart_irqs =
      (dif_uart_irq_state_snapshot_t)UINT_MAX;
  dif_usbdev_irq_state_snapshot_t usbdev_irqs =
      (dif_usbdev_irq_state_snapshot_t)UINT_MAX;

  CHECK_DIF_OK(
      dif_adc_ctrl_irq_restore_all(&adc_ctrl_aon, &adc_ctrl_irqs));
  CHECK_DIF_OK(
      dif_alert_handler_irq_restore_all(&alert_handler, &alert_handler_irqs));
  CHECK_DIF_OK(
      dif_csrng_irq_restore_all(&csrng, &csrng_irqs));
  CHECK_DIF_OK(
      dif_edn_irq_restore_all(&edn0, &edn_irqs));
  CHECK_DIF_OK(
      dif_edn_irq_restore_all(&edn1, &edn_irqs));
  CHECK_DIF_OK(
      dif_entropy_src_irq_restore_all(&entropy_src, &entropy_src_irqs));
  CHECK_DIF_OK(
      dif_flash_ctrl_irq_restore_all(&flash_ctrl, &flash_ctrl_irqs));
  CHECK_DIF_OK(
      dif_gpio_irq_restore_all(&gpio, &gpio_irqs));
  CHECK_DIF_OK(
      dif_hmac_irq_restore_all(&hmac, &hmac_irqs));
  CHECK_DIF_OK(
      dif_i2c_irq_restore_all(&i2c0, &i2c_irqs));
  CHECK_DIF_OK(
      dif_i2c_irq_restore_all(&i2c1, &i2c_irqs));
  CHECK_DIF_OK(
      dif_i2c_irq_restore_all(&i2c2, &i2c_irqs));
  CHECK_DIF_OK(
      dif_keymgr_irq_restore_all(&keymgr, &keymgr_irqs));
  CHECK_DIF_OK(
      dif_kmac_irq_restore_all(&kmac, &kmac_irqs));
  CHECK_DIF_OK(
      dif_otbn_irq_restore_all(&otbn, &otbn_irqs));
  CHECK_DIF_OK(
      dif_otp_ctrl_irq_restore_all(&otp_ctrl, &otp_ctrl_irqs));
  CHECK_DIF_OK(
      dif_pattgen_irq_restore_all(&pattgen, &pattgen_irqs));
  CHECK_DIF_OK(
      dif_pwrmgr_irq_restore_all(&pwrmgr_aon, &pwrmgr_irqs));
  CHECK_DIF_OK(
      dif_rv_timer_irq_restore_all(&rv_timer, kHart, &rv_timer_irqs));
  CHECK_DIF_OK(
      dif_sensor_ctrl_irq_restore_all(&sensor_ctrl_aon, &sensor_ctrl_irqs));
  CHECK_DIF_OK(
      dif_spi_device_irq_restore_all(&spi_device, &spi_device_irqs));
  CHECK_DIF_OK(
      dif_spi_host_irq_restore_all(&spi_host0, &spi_host_irqs));
  CHECK_DIF_OK(
      dif_spi_host_irq_restore_all(&spi_host1, &spi_host_irqs));
  CHECK_DIF_OK(
      dif_sysrst_ctrl_irq_restore_all(&sysrst_ctrl_aon, &sysrst_ctrl_irqs));
  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  if (kDeviceType == kDeviceSimDV) {
    CHECK_DIF_OK(
        dif_uart_irq_restore_all(&uart0, &uart_irqs));
  }
  CHECK_DIF_OK(
      dif_uart_irq_restore_all(&uart1, &uart_irqs));
  CHECK_DIF_OK(
      dif_uart_irq_restore_all(&uart2, &uart_irqs));
  CHECK_DIF_OK(
      dif_uart_irq_restore_all(&uart3, &uart_irqs));
  CHECK_DIF_OK(
      dif_usbdev_irq_restore_all(&usbdev, &usbdev_irqs));
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
  peripheral_expected = kTopEarlgreyPlicPeripheralAdcCtrlAon;
  for (dif_adc_ctrl_irq_t irq = kDifAdcCtrlIrqMatchDone;
       irq <= kDifAdcCtrlIrqMatchDone; ++irq) {
    adc_ctrl_irq_expected = irq;
    LOG_INFO("Triggering adc_ctrl_aon IRQ %d.", irq);
    CHECK_DIF_OK(dif_adc_ctrl_irq_force(&adc_ctrl_aon, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(adc_ctrl_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from adc_ctrl_aon is serviced.", irq);
  }

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

  peripheral_expected = kTopEarlgreyPlicPeripheralFlashCtrl;
  for (dif_flash_ctrl_irq_t irq = kDifFlashCtrlIrqProgEmpty;
       irq <= kDifFlashCtrlIrqCorrErr; ++irq) {
    flash_ctrl_irq_expected = irq;
    LOG_INFO("Triggering flash_ctrl IRQ %d.", irq);
    CHECK_DIF_OK(dif_flash_ctrl_irq_force(&flash_ctrl, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(flash_ctrl_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from flash_ctrl is serviced.", irq);
  }

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

  peripheral_expected = kTopEarlgreyPlicPeripheralHmac;
  for (dif_hmac_irq_t irq = kDifHmacIrqHmacDone;
       irq <= kDifHmacIrqHmacErr; ++irq) {
    hmac_irq_expected = irq;
    LOG_INFO("Triggering hmac IRQ %d.", irq);
    CHECK_DIF_OK(dif_hmac_irq_force(&hmac, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(hmac_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from hmac is serviced.", irq);
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralI2c0;
  for (dif_i2c_irq_t irq = kDifI2cIrqFmtThreshold;
       irq <= kDifI2cIrqHostTimeout; ++irq) {
    i2c_irq_expected = irq;
    LOG_INFO("Triggering i2c0 IRQ %d.", irq);
    CHECK_DIF_OK(dif_i2c_irq_force(&i2c0, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(i2c_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from i2c0 is serviced.", irq);
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralI2c1;
  for (dif_i2c_irq_t irq = kDifI2cIrqFmtThreshold;
       irq <= kDifI2cIrqHostTimeout; ++irq) {
    i2c_irq_expected = irq;
    LOG_INFO("Triggering i2c1 IRQ %d.", irq);
    CHECK_DIF_OK(dif_i2c_irq_force(&i2c1, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(i2c_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from i2c1 is serviced.", irq);
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralI2c2;
  for (dif_i2c_irq_t irq = kDifI2cIrqFmtThreshold;
       irq <= kDifI2cIrqHostTimeout; ++irq) {
    i2c_irq_expected = irq;
    LOG_INFO("Triggering i2c2 IRQ %d.", irq);
    CHECK_DIF_OK(dif_i2c_irq_force(&i2c2, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(i2c_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from i2c2 is serviced.", irq);
  }

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

  peripheral_expected = kTopEarlgreyPlicPeripheralKmac;
  for (dif_kmac_irq_t irq = kDifKmacIrqKmacDone;
       irq <= kDifKmacIrqKmacErr; ++irq) {
    kmac_irq_expected = irq;
    LOG_INFO("Triggering kmac IRQ %d.", irq);
    CHECK_DIF_OK(dif_kmac_irq_force(&kmac, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(kmac_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from kmac is serviced.", irq);
  }

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

  peripheral_expected = kTopEarlgreyPlicPeripheralSpiDevice;
  for (dif_spi_device_irq_t irq = kDifSpiDeviceIrqGenericRxFull;
       irq <= kDifSpiDeviceIrqTpmHeaderNotEmpty; ++irq) {
    spi_device_irq_expected = irq;
    LOG_INFO("Triggering spi_device IRQ %d.", irq);
    CHECK_DIF_OK(dif_spi_device_irq_force(&spi_device, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(spi_device_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from spi_device is serviced.", irq);
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralSpiHost0;
  for (dif_spi_host_irq_t irq = kDifSpiHostIrqError;
       irq <= kDifSpiHostIrqSpiEvent; ++irq) {
    spi_host_irq_expected = irq;
    LOG_INFO("Triggering spi_host0 IRQ %d.", irq);
    CHECK_DIF_OK(dif_spi_host_irq_force(&spi_host0, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(spi_host_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from spi_host0 is serviced.", irq);
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralSpiHost1;
  for (dif_spi_host_irq_t irq = kDifSpiHostIrqError;
       irq <= kDifSpiHostIrqSpiEvent; ++irq) {
    spi_host_irq_expected = irq;
    LOG_INFO("Triggering spi_host1 IRQ %d.", irq);
    CHECK_DIF_OK(dif_spi_host_irq_force(&spi_host1, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(spi_host_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from spi_host1 is serviced.", irq);
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralSysrstCtrlAon;
  for (dif_sysrst_ctrl_irq_t irq = kDifSysrstCtrlIrqEventDetected;
       irq <= kDifSysrstCtrlIrqEventDetected; ++irq) {
    sysrst_ctrl_irq_expected = irq;
    LOG_INFO("Triggering sysrst_ctrl_aon IRQ %d.", irq);
    CHECK_DIF_OK(dif_sysrst_ctrl_irq_force(&sysrst_ctrl_aon, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(sysrst_ctrl_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from sysrst_ctrl_aon is serviced.", irq);
  }

  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  if (kDeviceType == kDeviceSimDV) {
    peripheral_expected = kTopEarlgreyPlicPeripheralUart0;
    for (dif_uart_irq_t irq = kDifUartIrqTxWatermark;
         irq <= kDifUartIrqRxParityErr; ++irq) {
      uart_irq_expected = irq;
      LOG_INFO("Triggering uart0 IRQ %d.", irq);
      CHECK_DIF_OK(dif_uart_irq_force(&uart0, irq, true));

      // This avoids a race where *irq_serviced is read before
      // entering the ISR.
      IBEX_SPIN_FOR(uart_irq_serviced == irq, 1);
      LOG_INFO("IRQ %d from uart0 is serviced.", irq);
    }
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralUart1;
  for (dif_uart_irq_t irq = kDifUartIrqTxWatermark;
       irq <= kDifUartIrqRxParityErr; ++irq) {
    uart_irq_expected = irq;
    LOG_INFO("Triggering uart1 IRQ %d.", irq);
    CHECK_DIF_OK(dif_uart_irq_force(&uart1, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(uart_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from uart1 is serviced.", irq);
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralUart2;
  for (dif_uart_irq_t irq = kDifUartIrqTxWatermark;
       irq <= kDifUartIrqRxParityErr; ++irq) {
    uart_irq_expected = irq;
    LOG_INFO("Triggering uart2 IRQ %d.", irq);
    CHECK_DIF_OK(dif_uart_irq_force(&uart2, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(uart_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from uart2 is serviced.", irq);
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralUart3;
  for (dif_uart_irq_t irq = kDifUartIrqTxWatermark;
       irq <= kDifUartIrqRxParityErr; ++irq) {
    uart_irq_expected = irq;
    LOG_INFO("Triggering uart3 IRQ %d.", irq);
    CHECK_DIF_OK(dif_uart_irq_force(&uart3, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(uart_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from uart3 is serviced.", irq);
  }

  peripheral_expected = kTopEarlgreyPlicPeripheralUsbdev;
  for (dif_usbdev_irq_t irq = kDifUsbdevIrqPktReceived;
       irq <= kDifUsbdevIrqLinkOutErr; ++irq) {
    usbdev_irq_expected = irq;
    LOG_INFO("Triggering usbdev IRQ %d.", irq);
    CHECK_DIF_OK(dif_usbdev_irq_force(&usbdev, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(usbdev_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from usbdev is serviced.", irq);
  }
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
