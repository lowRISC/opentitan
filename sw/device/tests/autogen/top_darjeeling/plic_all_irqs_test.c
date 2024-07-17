// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// clang-format off
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
// -o hw/top_darjeeling
#include <limits.h>

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/ip/alert_handler/dif/dif_alert_handler.h"
#include "sw/ip/aon_timer/dif/dif_aon_timer.h"
#include "sw/ip/csrng/dif/dif_csrng.h"
#include "sw/ip/dma/dif/dif_dma.h"
#include "sw/ip/edn/dif/dif_edn.h"
#include "sw/ip/gpio/dif/dif_gpio.h"
#include "sw/ip/hmac/dif/dif_hmac.h"
#include "sw/ip/i2c/dif/dif_i2c.h"
#include "sw/ip/keymgr_dpe/dif/dif_keymgr_dpe.h"
#include "sw/ip/kmac/dif/dif_kmac.h"
#include "sw/ip/mbx/dif/dif_mbx.h"
#include "sw/ip/otbn/dif/dif_otbn.h"
#include "sw/ip/otp_ctrl/dif/dif_otp_ctrl.h"
#include "sw/ip/pwrmgr/dif/dif_pwrmgr.h"
#include "sw/ip/rv_plic/dif/dif_rv_plic.h"
#include "sw/ip/rv_timer/dif/dif_rv_timer.h"
#include "sw/ip/sensor_ctrl/dif/dif_sensor_ctrl.h"
#include "sw/ip/soc_proxy/dif/dif_soc_proxy.h"
#include "sw/ip/spi_device/dif/dif_spi_device.h"
#include "sw/ip/spi_host/dif/dif_spi_host.h"
#include "sw/ip/uart/dif/dif_uart.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/csr.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/ibex.h"
#include "sw/lib/sw/device/runtime/irq.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "sw/ip/rv_plic/test/utils/rv_plic_testutils.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

static dif_alert_handler_t alert_handler;
static dif_aon_timer_t aon_timer_aon;
static dif_csrng_t csrng;
static dif_dma_t dma;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_gpio_t gpio;
static dif_hmac_t hmac;
static dif_i2c_t i2c0;
static dif_keymgr_dpe_t keymgr_dpe;
static dif_kmac_t kmac;
static dif_mbx_t mbx0;
static dif_mbx_t mbx1;
static dif_mbx_t mbx2;
static dif_mbx_t mbx3;
static dif_mbx_t mbx4;
static dif_mbx_t mbx5;
static dif_mbx_t mbx6;
static dif_mbx_t mbx_jtag;
static dif_mbx_t mbx_pcie0;
static dif_mbx_t mbx_pcie1;
static dif_otbn_t otbn;
static dif_otp_ctrl_t otp_ctrl;
static dif_pwrmgr_t pwrmgr_aon;
static dif_rv_timer_t rv_timer;
static dif_sensor_ctrl_t sensor_ctrl;
static dif_soc_proxy_t soc_proxy;
static dif_spi_device_t spi_device;
static dif_spi_host_t spi_host0;
static dif_uart_t uart0;
static dif_rv_plic_t plic;
static const top_darjeeling_plic_target_t kHart = kTopDarjeelingPlicTargetIbex0;

/**
 * Flag indicating which peripheral is under test.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
static volatile top_darjeeling_plic_peripheral_t peripheral_expected;

/**
 * Flags indicating the IRQ expected to have triggered and serviced within the
 * peripheral.
 *
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
static volatile dif_alert_handler_irq_t alert_handler_irq_expected;
static volatile dif_alert_handler_irq_t alert_handler_irq_serviced;
static volatile dif_aon_timer_irq_t aon_timer_irq_expected;
static volatile dif_aon_timer_irq_t aon_timer_irq_serviced;
static volatile dif_csrng_irq_t csrng_irq_expected;
static volatile dif_csrng_irq_t csrng_irq_serviced;
static volatile dif_dma_irq_t dma_irq_expected;
static volatile dif_dma_irq_t dma_irq_serviced;
static volatile dif_edn_irq_t edn_irq_expected;
static volatile dif_edn_irq_t edn_irq_serviced;
static volatile dif_gpio_irq_t gpio_irq_expected;
static volatile dif_gpio_irq_t gpio_irq_serviced;
static volatile dif_hmac_irq_t hmac_irq_expected;
static volatile dif_hmac_irq_t hmac_irq_serviced;
static volatile dif_i2c_irq_t i2c_irq_expected;
static volatile dif_i2c_irq_t i2c_irq_serviced;
static volatile dif_keymgr_dpe_irq_t keymgr_dpe_irq_expected;
static volatile dif_keymgr_dpe_irq_t keymgr_dpe_irq_serviced;
static volatile dif_kmac_irq_t kmac_irq_expected;
static volatile dif_kmac_irq_t kmac_irq_serviced;
static volatile dif_mbx_irq_t mbx_irq_expected;
static volatile dif_mbx_irq_t mbx_irq_serviced;
static volatile dif_otbn_irq_t otbn_irq_expected;
static volatile dif_otbn_irq_t otbn_irq_serviced;
static volatile dif_otp_ctrl_irq_t otp_ctrl_irq_expected;
static volatile dif_otp_ctrl_irq_t otp_ctrl_irq_serviced;
static volatile dif_pwrmgr_irq_t pwrmgr_irq_expected;
static volatile dif_pwrmgr_irq_t pwrmgr_irq_serviced;
static volatile dif_rv_timer_irq_t rv_timer_irq_expected;
static volatile dif_rv_timer_irq_t rv_timer_irq_serviced;
static volatile dif_sensor_ctrl_irq_t sensor_ctrl_irq_expected;
static volatile dif_sensor_ctrl_irq_t sensor_ctrl_irq_serviced;
static volatile dif_soc_proxy_irq_t soc_proxy_irq_expected;
static volatile dif_soc_proxy_irq_t soc_proxy_irq_serviced;
static volatile dif_spi_device_irq_t spi_device_irq_expected;
static volatile dif_spi_device_irq_t spi_device_irq_serviced;
static volatile dif_spi_host_irq_t spi_host_irq_expected;
static volatile dif_spi_host_irq_t spi_host_irq_serviced;
static volatile dif_uart_irq_t uart_irq_expected;
static volatile dif_uart_irq_t uart_irq_serviced;

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

  top_darjeeling_plic_peripheral_t peripheral = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == peripheral_expected,
        "Interrupt from incorrect peripheral: exp = %d, obs = %d",
        peripheral_expected, peripheral);

  switch (peripheral) {
    case kTopDarjeelingPlicPeripheralAlertHandler: {
      dif_alert_handler_irq_t irq = (dif_alert_handler_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdAlertHandlerClassa);
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

    case kTopDarjeelingPlicPeripheralAonTimerAon: {
      dif_aon_timer_irq_t irq = (dif_aon_timer_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdAonTimerAonWkupTimerExpired);
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

    case kTopDarjeelingPlicPeripheralCsrng: {
      dif_csrng_irq_t irq = (dif_csrng_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdCsrngCsCmdReqDone);
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

    case kTopDarjeelingPlicPeripheralDma: {
      dif_dma_irq_t irq = (dif_dma_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdDmaDmaDone);
      CHECK(irq == dma_irq_expected,
            "Incorrect dma IRQ triggered: exp = %d, obs = %d",
            dma_irq_expected, irq);
      dma_irq_serviced = irq;

      dif_dma_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_dma_irq_get_state(&dma, &snapshot));
      CHECK(snapshot == (dif_dma_irq_state_snapshot_t)(1 << irq),
            "Only dma IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_dma_irq_force(&dma, irq, false));
      CHECK_DIF_OK(dif_dma_irq_acknowledge(&dma, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralEdn0: {
      dif_edn_irq_t irq = (dif_edn_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdEdn0EdnCmdReqDone);
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

    case kTopDarjeelingPlicPeripheralEdn1: {
      dif_edn_irq_t irq = (dif_edn_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdEdn1EdnCmdReqDone);
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

    case kTopDarjeelingPlicPeripheralGpio: {
      dif_gpio_irq_t irq = (dif_gpio_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdGpioGpio0);
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

    case kTopDarjeelingPlicPeripheralHmac: {
      dif_hmac_irq_t irq = (dif_hmac_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdHmacHmacDone);
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

    case kTopDarjeelingPlicPeripheralI2c0: {
      dif_i2c_irq_t irq = (dif_i2c_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdI2c0FmtThreshold);
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

    case kTopDarjeelingPlicPeripheralKeymgrDpe: {
      dif_keymgr_dpe_irq_t irq = (dif_keymgr_dpe_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdKeymgrDpeOpDone);
      CHECK(irq == keymgr_dpe_irq_expected,
            "Incorrect keymgr_dpe IRQ triggered: exp = %d, obs = %d",
            keymgr_dpe_irq_expected, irq);
      keymgr_dpe_irq_serviced = irq;

      dif_keymgr_dpe_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_keymgr_dpe_irq_get_state(&keymgr_dpe, &snapshot));
      CHECK(snapshot == (dif_keymgr_dpe_irq_state_snapshot_t)(1 << irq),
            "Only keymgr_dpe IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_keymgr_dpe_irq_force(&keymgr_dpe, irq, false));
      CHECK_DIF_OK(dif_keymgr_dpe_irq_acknowledge(&keymgr_dpe, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralKmac: {
      dif_kmac_irq_t irq = (dif_kmac_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdKmacKmacDone);
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

    case kTopDarjeelingPlicPeripheralMbx0: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbx0MbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx0 IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx0, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx0 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx0, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx0, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralMbx1: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbx1MbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx1 IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx1, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx1 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx1, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx1, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralMbx2: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbx2MbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx2 IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx2, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx2 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx2, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx2, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralMbx3: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbx3MbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx3 IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx3, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx3 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx3, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx3, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralMbx4: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbx4MbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx4 IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx4, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx4 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx4, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx4, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralMbx5: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbx5MbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx5 IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx5, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx5 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx5, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx5, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralMbx6: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbx6MbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx6 IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx6, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx6 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx6, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx6, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralMbxJtag: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbxJtagMbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx_jtag IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx_jtag, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx_jtag IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx_jtag, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx_jtag, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralMbxPcie0: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbxPcie0MbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx_pcie0 IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx_pcie0, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx_pcie0 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx_pcie0, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx_pcie0, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralMbxPcie1: {
      dif_mbx_irq_t irq = (dif_mbx_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdMbxPcie1MbxReady);
      CHECK(irq == mbx_irq_expected,
            "Incorrect mbx_pcie1 IRQ triggered: exp = %d, obs = %d",
            mbx_irq_expected, irq);
      mbx_irq_serviced = irq;

      dif_mbx_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_mbx_irq_get_state(&mbx_pcie1, &snapshot));
      CHECK(snapshot == (dif_mbx_irq_state_snapshot_t)(1 << irq),
            "Only mbx_pcie1 IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_mbx_irq_force(&mbx_pcie1, irq, false));
      CHECK_DIF_OK(dif_mbx_irq_acknowledge(&mbx_pcie1, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralOtbn: {
      dif_otbn_irq_t irq = (dif_otbn_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdOtbnDone);
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

    case kTopDarjeelingPlicPeripheralOtpCtrl: {
      dif_otp_ctrl_irq_t irq = (dif_otp_ctrl_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdOtpCtrlOtpOperationDone);
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

    case kTopDarjeelingPlicPeripheralPwrmgrAon: {
      dif_pwrmgr_irq_t irq = (dif_pwrmgr_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdPwrmgrAonWakeup);
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

    case kTopDarjeelingPlicPeripheralRvTimer: {
      dif_rv_timer_irq_t irq = (dif_rv_timer_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdRvTimerTimerExpiredHart0Timer0);
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

    case kTopDarjeelingPlicPeripheralSensorCtrl: {
      dif_sensor_ctrl_irq_t irq = (dif_sensor_ctrl_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdSensorCtrlIoStatusChange);
      CHECK(irq == sensor_ctrl_irq_expected,
            "Incorrect sensor_ctrl IRQ triggered: exp = %d, obs = %d",
            sensor_ctrl_irq_expected, irq);
      sensor_ctrl_irq_serviced = irq;

      dif_sensor_ctrl_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_sensor_ctrl_irq_get_state(&sensor_ctrl, &snapshot));
      CHECK(snapshot == (dif_sensor_ctrl_irq_state_snapshot_t)(1 << irq),
            "Only sensor_ctrl IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_sensor_ctrl_irq_force(&sensor_ctrl, irq, false));
      CHECK_DIF_OK(dif_sensor_ctrl_irq_acknowledge(&sensor_ctrl, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralSocProxy: {
      dif_soc_proxy_irq_t irq = (dif_soc_proxy_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdSocProxyExternal0);
      CHECK(irq == soc_proxy_irq_expected,
            "Incorrect soc_proxy IRQ triggered: exp = %d, obs = %d",
            soc_proxy_irq_expected, irq);
      soc_proxy_irq_serviced = irq;

      dif_soc_proxy_irq_state_snapshot_t snapshot;
      CHECK_DIF_OK(dif_soc_proxy_irq_get_state(&soc_proxy, &snapshot));
      CHECK(snapshot == (dif_soc_proxy_irq_state_snapshot_t)(1 << irq),
            "Only soc_proxy IRQ %d expected to fire. Actual interrupt "
            "status = %x",
            irq, snapshot);

      // TODO: Check Interrupt type then clear INTR_TEST if needed.
      CHECK_DIF_OK(dif_soc_proxy_irq_force(&soc_proxy, irq, false));
      CHECK_DIF_OK(dif_soc_proxy_irq_acknowledge(&soc_proxy, irq));
      break;
    }

    case kTopDarjeelingPlicPeripheralSpiDevice: {
      dif_spi_device_irq_t irq = (dif_spi_device_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdSpiDeviceGenericRxFull);
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

    case kTopDarjeelingPlicPeripheralSpiHost0: {
      dif_spi_host_irq_t irq = (dif_spi_host_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdSpiHost0Error);
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

    case kTopDarjeelingPlicPeripheralUart0: {
      dif_uart_irq_t irq = (dif_uart_irq_t)(
          plic_irq_id -
          (dif_rv_plic_irq_id_t)kTopDarjeelingPlicIrqIdUart0TxWatermark);
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

  base_addr = mmio_region_from_addr(TOP_DARJEELING_ALERT_HANDLER_BASE_ADDR);
  CHECK_DIF_OK(dif_alert_handler_init(base_addr, &alert_handler));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_aon_timer_init(base_addr, &aon_timer_aon));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_CSRNG_BASE_ADDR);
  CHECK_DIF_OK(dif_csrng_init(base_addr, &csrng));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_DMA_BASE_ADDR);
  CHECK_DIF_OK(dif_dma_init(base_addr, &dma));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_EDN0_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_EDN1_BASE_ADDR);
  CHECK_DIF_OK(dif_edn_init(base_addr, &edn1));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_GPIO_BASE_ADDR);
  CHECK_DIF_OK(dif_gpio_init(base_addr, &gpio));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_HMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_hmac_init(base_addr, &hmac));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_I2C0_BASE_ADDR);
  CHECK_DIF_OK(dif_i2c_init(base_addr, &i2c0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_KEYMGR_DPE_BASE_ADDR);
  CHECK_DIF_OK(dif_keymgr_dpe_init(base_addr, &keymgr_dpe));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_KMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_kmac_init(base_addr, &kmac));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX0_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX1_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx1));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX2_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx2));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX3_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx3));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX4_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx4));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX5_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx5));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX6_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx6));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX_JTAG_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx_jtag));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX_PCIE0_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx_pcie0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_MBX_PCIE1_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_mbx_init(base_addr, &mbx_pcie1));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_OTBN_BASE_ADDR);
  CHECK_DIF_OK(dif_otbn_init(base_addr, &otbn));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_otp_ctrl_init(base_addr, &otp_ctrl));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(base_addr, &pwrmgr_aon));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_RV_TIMER_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_timer_init(base_addr, &rv_timer));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SENSOR_CTRL_BASE_ADDR);
  CHECK_DIF_OK(dif_sensor_ctrl_init(base_addr, &sensor_ctrl));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SOC_PROXY_CORE_BASE_ADDR);
  CHECK_DIF_OK(dif_soc_proxy_init(base_addr, &soc_proxy));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SPI_DEVICE_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_device_init(base_addr, &spi_device));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_SPI_HOST0_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_UART0_BASE_ADDR);
  CHECK_DIF_OK(dif_uart_init(base_addr, &uart0));

  base_addr = mmio_region_from_addr(TOP_DARJEELING_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));
}

/**
 * Clears pending IRQs in all peripherals.
 */
static void peripheral_irqs_clear(void) {
  CHECK_DIF_OK(dif_alert_handler_irq_acknowledge_all(&alert_handler));
  CHECK_DIF_OK(dif_aon_timer_irq_acknowledge_all(&aon_timer_aon));
  CHECK_DIF_OK(dif_csrng_irq_acknowledge_all(&csrng));
  CHECK_DIF_OK(dif_dma_irq_acknowledge_all(&dma));
  CHECK_DIF_OK(dif_edn_irq_acknowledge_all(&edn0));
  CHECK_DIF_OK(dif_edn_irq_acknowledge_all(&edn1));
  CHECK_DIF_OK(dif_gpio_irq_acknowledge_all(&gpio));
  CHECK_DIF_OK(dif_hmac_irq_acknowledge_all(&hmac));
  CHECK_DIF_OK(dif_i2c_irq_acknowledge_all(&i2c0));
  CHECK_DIF_OK(dif_keymgr_dpe_irq_acknowledge_all(&keymgr_dpe));
  CHECK_DIF_OK(dif_kmac_irq_acknowledge_all(&kmac));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx0));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx1));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx2));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx3));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx4));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx5));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx6));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx_jtag));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx_pcie0));
  CHECK_DIF_OK(dif_mbx_irq_acknowledge_all(&mbx_pcie1));
  CHECK_DIF_OK(dif_otbn_irq_acknowledge_all(&otbn));
  CHECK_DIF_OK(dif_otp_ctrl_irq_acknowledge_all(&otp_ctrl));
  CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge_all(&pwrmgr_aon));
  CHECK_DIF_OK(dif_rv_timer_irq_acknowledge_all(&rv_timer, kHart));
  CHECK_DIF_OK(dif_sensor_ctrl_irq_acknowledge_all(&sensor_ctrl));
  CHECK_DIF_OK(dif_soc_proxy_irq_acknowledge_all(&soc_proxy));
  CHECK_DIF_OK(dif_spi_device_irq_acknowledge_all(&spi_device));
  CHECK_DIF_OK(dif_spi_host_irq_acknowledge_all(&spi_host0));
  CHECK_DIF_OK(dif_uart_irq_acknowledge_all(&uart0));
}

/**
 * Enables all IRQs in all peripherals.
 */
static void peripheral_irqs_enable(void) {
  dif_alert_handler_irq_state_snapshot_t alert_handler_irqs =
      (dif_alert_handler_irq_state_snapshot_t)UINT_MAX;
  dif_csrng_irq_state_snapshot_t csrng_irqs =
      (dif_csrng_irq_state_snapshot_t)UINT_MAX;
  dif_dma_irq_state_snapshot_t dma_irqs =
      (dif_dma_irq_state_snapshot_t)UINT_MAX;
  dif_edn_irq_state_snapshot_t edn_irqs =
      (dif_edn_irq_state_snapshot_t)UINT_MAX;
  dif_gpio_irq_state_snapshot_t gpio_irqs =
      (dif_gpio_irq_state_snapshot_t)UINT_MAX;
  dif_hmac_irq_state_snapshot_t hmac_irqs =
      (dif_hmac_irq_state_snapshot_t)UINT_MAX;
  dif_i2c_irq_state_snapshot_t i2c_irqs =
      (dif_i2c_irq_state_snapshot_t)UINT_MAX;
  dif_keymgr_dpe_irq_state_snapshot_t keymgr_dpe_irqs =
      (dif_keymgr_dpe_irq_state_snapshot_t)UINT_MAX;
  dif_kmac_irq_state_snapshot_t kmac_irqs =
      (dif_kmac_irq_state_snapshot_t)UINT_MAX;
  dif_mbx_irq_state_snapshot_t mbx_irqs =
      (dif_mbx_irq_state_snapshot_t)UINT_MAX;
  dif_otbn_irq_state_snapshot_t otbn_irqs =
      (dif_otbn_irq_state_snapshot_t)UINT_MAX;
  dif_otp_ctrl_irq_state_snapshot_t otp_ctrl_irqs =
      (dif_otp_ctrl_irq_state_snapshot_t)UINT_MAX;
  dif_pwrmgr_irq_state_snapshot_t pwrmgr_irqs =
      (dif_pwrmgr_irq_state_snapshot_t)UINT_MAX;
  dif_rv_timer_irq_state_snapshot_t rv_timer_irqs =
      (dif_rv_timer_irq_state_snapshot_t)UINT_MAX;
  dif_sensor_ctrl_irq_state_snapshot_t sensor_ctrl_irqs =
      (dif_sensor_ctrl_irq_state_snapshot_t)UINT_MAX;
  dif_soc_proxy_irq_state_snapshot_t soc_proxy_irqs =
      (dif_soc_proxy_irq_state_snapshot_t)UINT_MAX;
  dif_spi_device_irq_state_snapshot_t spi_device_irqs =
      (dif_spi_device_irq_state_snapshot_t)UINT_MAX;
  dif_spi_host_irq_state_snapshot_t spi_host_irqs =
      (dif_spi_host_irq_state_snapshot_t)UINT_MAX;
  dif_uart_irq_state_snapshot_t uart_irqs =
      (dif_uart_irq_state_snapshot_t)UINT_MAX;

  CHECK_DIF_OK(
      dif_alert_handler_irq_restore_all(&alert_handler, &alert_handler_irqs));
  CHECK_DIF_OK(
      dif_csrng_irq_restore_all(&csrng, &csrng_irqs));
  CHECK_DIF_OK(
      dif_dma_irq_restore_all(&dma, &dma_irqs));
  CHECK_DIF_OK(
      dif_edn_irq_restore_all(&edn0, &edn_irqs));
  CHECK_DIF_OK(
      dif_edn_irq_restore_all(&edn1, &edn_irqs));
  CHECK_DIF_OK(
      dif_gpio_irq_restore_all(&gpio, &gpio_irqs));
  CHECK_DIF_OK(
      dif_hmac_irq_restore_all(&hmac, &hmac_irqs));
  CHECK_DIF_OK(
      dif_i2c_irq_restore_all(&i2c0, &i2c_irqs));
  CHECK_DIF_OK(
      dif_keymgr_dpe_irq_restore_all(&keymgr_dpe, &keymgr_dpe_irqs));
  CHECK_DIF_OK(
      dif_kmac_irq_restore_all(&kmac, &kmac_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx0, &mbx_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx1, &mbx_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx2, &mbx_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx3, &mbx_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx4, &mbx_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx5, &mbx_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx6, &mbx_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx_jtag, &mbx_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx_pcie0, &mbx_irqs));
  CHECK_DIF_OK(
      dif_mbx_irq_restore_all(&mbx_pcie1, &mbx_irqs));
  CHECK_DIF_OK(
      dif_otbn_irq_restore_all(&otbn, &otbn_irqs));
  CHECK_DIF_OK(
      dif_otp_ctrl_irq_restore_all(&otp_ctrl, &otp_ctrl_irqs));
  CHECK_DIF_OK(
      dif_pwrmgr_irq_restore_all(&pwrmgr_aon, &pwrmgr_irqs));
  CHECK_DIF_OK(
      dif_rv_timer_irq_restore_all(&rv_timer, kHart, &rv_timer_irqs));
  CHECK_DIF_OK(
      dif_sensor_ctrl_irq_restore_all(&sensor_ctrl, &sensor_ctrl_irqs));
  CHECK_DIF_OK(
      dif_soc_proxy_irq_restore_all(&soc_proxy, &soc_proxy_irqs));
  CHECK_DIF_OK(
      dif_spi_device_irq_restore_all(&spi_device, &spi_device_irqs));
  CHECK_DIF_OK(
      dif_spi_host_irq_restore_all(&spi_host0, &spi_host_irqs));
  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  if (kDeviceType == kDeviceSimDV) {
    CHECK_DIF_OK(
        dif_uart_irq_restore_all(&uart0, &uart_irqs));
  }
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
  peripheral_expected = kTopDarjeelingPlicPeripheralAlertHandler;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralAonTimerAon;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralCsrng;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralDma;
  for (dif_dma_irq_t irq = kDifDmaIrqDmaDone;
       irq <= kDifDmaIrqDmaError; ++irq) {
    dma_irq_expected = irq;
    LOG_INFO("Triggering dma IRQ %d.", irq);
    CHECK_DIF_OK(dif_dma_irq_force(&dma, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(dma_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from dma is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralEdn0;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralEdn1;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralGpio;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralHmac;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralI2c0;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralKeymgrDpe;
  for (dif_keymgr_dpe_irq_t irq = kDifKeymgrDpeIrqOpDone;
       irq <= kDifKeymgrDpeIrqOpDone; ++irq) {
    keymgr_dpe_irq_expected = irq;
    LOG_INFO("Triggering keymgr_dpe IRQ %d.", irq);
    CHECK_DIF_OK(dif_keymgr_dpe_irq_force(&keymgr_dpe, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(keymgr_dpe_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from keymgr_dpe is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralKmac;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralMbx0;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx0 IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx0, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx0 is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralMbx1;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx1 IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx1, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx1 is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralMbx2;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx2 IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx2, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx2 is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralMbx3;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx3 IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx3, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx3 is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralMbx4;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx4 IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx4, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx4 is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralMbx5;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx5 IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx5, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx5 is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralMbx6;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx6 IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx6, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx6 is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralMbxJtag;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx_jtag IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx_jtag, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx_jtag is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralMbxPcie0;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx_pcie0 IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx_pcie0, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx_pcie0 is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralMbxPcie1;
  for (dif_mbx_irq_t irq = kDifMbxIrqMbxReady;
       irq <= kDifMbxIrqMbxError; ++irq) {
    mbx_irq_expected = irq;
    LOG_INFO("Triggering mbx_pcie1 IRQ %d.", irq);
    CHECK_DIF_OK(dif_mbx_irq_force(&mbx_pcie1, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(mbx_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from mbx_pcie1 is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralOtbn;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralOtpCtrl;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralPwrmgrAon;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralRvTimer;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralSensorCtrl;
  for (dif_sensor_ctrl_irq_t irq = kDifSensorCtrlIrqIoStatusChange;
       irq <= kDifSensorCtrlIrqInitStatusChange; ++irq) {
    sensor_ctrl_irq_expected = irq;
    LOG_INFO("Triggering sensor_ctrl IRQ %d.", irq);
    CHECK_DIF_OK(dif_sensor_ctrl_irq_force(&sensor_ctrl, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(sensor_ctrl_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from sensor_ctrl is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralSocProxy;
  for (dif_soc_proxy_irq_t irq = kDifSocProxyIrqExternal0;
       irq <= kDifSocProxyIrqExternal31; ++irq) {
    soc_proxy_irq_expected = irq;
    LOG_INFO("Triggering soc_proxy IRQ %d.", irq);
    CHECK_DIF_OK(dif_soc_proxy_irq_force(&soc_proxy, irq, true));

    // This avoids a race where *irq_serviced is read before
    // entering the ISR.
    IBEX_SPIN_FOR(soc_proxy_irq_serviced == irq, 1);
    LOG_INFO("IRQ %d from soc_proxy is serviced.", irq);
  }

  peripheral_expected = kTopDarjeelingPlicPeripheralSpiDevice;
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

  peripheral_expected = kTopDarjeelingPlicPeripheralSpiHost0;
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

  // lowrisc/opentitan#8656: Skip UART0 in non-DV setups due to interference
  // from the logging facility.
  if (kDeviceType == kDeviceSimDV) {
    peripheral_expected = kTopDarjeelingPlicPeripheralUart0;
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
      &plic, kHart, kTopDarjeelingPlicIrqIdNone + 1, kTopDarjeelingPlicIrqIdLast);
  peripheral_irqs_clear();
  peripheral_irqs_enable();
  peripheral_irqs_trigger();
  return true;
}

// clang-format on
