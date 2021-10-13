// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !!
// -------------------// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN
// AUTO-GENERATED WITH THE FOLLOWING COMMAND: util/topgen.py -t
// hw/top_earlgrey/data/top_earlgrey.hjson -o hw/top_earlgrey

#include "sw/device/lib/base/freestanding/limits.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
// #include "sw/device/lib/dif/dif_adc_ctrl.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
// #include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_csrng.h"
#include "sw/device/lib/dif/dif_edn.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
// #include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_i2c.h"
#include "sw/device/lib/dif/dif_keymgr.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_otp_ctrl.h"
// #include "sw/device/lib/dif/dif_pattgen.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
// #include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/dif/dif_spi_device.h"
// #include "sw/device/lib/dif/dif_spi_host.h"
// #include "sw/device/lib/dif/dif_sysrst_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/handler.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/test_main.h"
#include "sw/device/lib/testing/test_framework/test_status.h"
#include "sw/device/tests/plic_all_irqs_test_helper.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// static dif_adc_ctrl_t adc_ctrl_aon;
static dif_alert_handler_t alert_handler;
// static dif_aon_timer_t aon_timer_aon;
static dif_csrng_t csrng;
static dif_edn_t edn0;
static dif_edn_t edn1;
static dif_entropy_src_t entropy_src;
// static dif_flash_ctrl_t flash_ctrl;
static dif_gpio_t gpio;
static dif_hmac_t hmac;
static dif_i2c_t i2c0;
static dif_i2c_t i2c1;
static dif_i2c_t i2c2;
static dif_keymgr_t keymgr;
static dif_kmac_t kmac;
static dif_otbn_t otbn;
static dif_otp_ctrl_t otp_ctrl;
// static dif_pattgen_t pattgen;
static dif_pwrmgr_t pwrmgr_aon;
// static dif_rv_timer_t rv_timer;
static dif_spi_device_t spi_device;
// static dif_spi_host_t spi_host0;
// static dif_spi_host_t spi_host1;
// static dif_sysrst_ctrl_t sysrst_ctrl_aon;
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
// static volatile dif_adc_ctrl_irq_t adc_ctrl_irq_expected;
// static volatile dif_adc_ctrl_irq_t adc_ctrl_irq_serviced;
static volatile dif_alert_handler_irq_t alert_handler_irq_expected;
static volatile dif_alert_handler_irq_t alert_handler_irq_serviced;
// static volatile dif_aon_timer_irq_t aon_timer_irq_expected;
// static volatile dif_aon_timer_irq_t aon_timer_irq_serviced;
static volatile dif_csrng_irq_t csrng_irq_expected;
static volatile dif_csrng_irq_t csrng_irq_serviced;
static volatile dif_edn_irq_t edn_irq_expected;
static volatile dif_edn_irq_t edn_irq_serviced;
static volatile dif_entropy_src_irq_t entropy_src_irq_expected;
static volatile dif_entropy_src_irq_t entropy_src_irq_serviced;
// static volatile dif_flash_ctrl_irq_t flash_ctrl_irq_expected;
// static volatile dif_flash_ctrl_irq_t flash_ctrl_irq_serviced;
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
// static volatile dif_pattgen_irq_t pattgen_irq_expected;
// static volatile dif_pattgen_irq_t pattgen_irq_serviced;
static volatile dif_pwrmgr_irq_t pwrmgr_irq_expected;
static volatile dif_pwrmgr_irq_t pwrmgr_irq_serviced;
// static volatile dif_rv_timer_irq_t rv_timer_irq_expected;
// static volatile dif_rv_timer_irq_t rv_timer_irq_serviced;
static volatile dif_spi_device_irq_t spi_device_irq_expected;
static volatile dif_spi_device_irq_t spi_device_irq_serviced;
// static volatile dif_spi_host_irq_t spi_host_irq_expected;
// static volatile dif_spi_host_irq_t spi_host_irq_serviced;
// static volatile dif_sysrst_ctrl_irq_t sysrst_ctrl_irq_expected;
// static volatile dif_sysrst_ctrl_irq_t sysrst_ctrl_irq_serviced;
static volatile dif_uart_irq_t uart_irq_expected;
static volatile dif_uart_irq_t uart_irq_serviced;
static volatile dif_usbdev_irq_t usbdev_irq_expected;
static volatile dif_usbdev_irq_t usbdev_irq_serviced;

/**
 * Provides external IRQ handling for this test.
 *
 * This function overrides the default external IRQ handler in
 * `sw/device/lib/handler.h`.
 */
void handler_irq_external(void) {
  // Find which interrupt fired at PLIC by claiming it.
  dif_rv_plic_irq_id_t plic_irq_id;
  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic, kHart, &plic_irq_id));

  // Check if it is the right peripheral.
  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  CHECK(peripheral == peripheral_expected,
        "Interrupt from incorrect peripheral: exp = %d, obs = %d",
        peripheral_expected, peripheral);

  switch (peripheral) {
    // case kTopEarlgreyPlicPeripheralAdcCtrlAon:
    //   PERIPHERAL_ISR(adc_ctrl, adc_ctrl_aon,
    //   kTopEarlgreyPlicIrqIdAdcCtrlAonDebugCable); break;
    case kTopEarlgreyPlicPeripheralAlertHandler:
      PERIPHERAL_ISR(alert_handler, alert_handler,
                     kTopEarlgreyPlicIrqIdAlertHandlerClassa);
      break;
    // case kTopEarlgreyPlicPeripheralAonTimerAon:
    //   PERIPHERAL_ISR(aon_timer, aon_timer_aon,
    //   kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired); break;
    case kTopEarlgreyPlicPeripheralCsrng:
      PERIPHERAL_ISR(csrng, csrng, kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone);
      break;
    case kTopEarlgreyPlicPeripheralEdn0:
      PERIPHERAL_ISR(edn, edn0, kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone);
      break;
    case kTopEarlgreyPlicPeripheralEdn1:
      PERIPHERAL_ISR(edn, edn1, kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone);
      break;
    case kTopEarlgreyPlicPeripheralEntropySrc:
      PERIPHERAL_ISR(entropy_src, entropy_src,
                     kTopEarlgreyPlicIrqIdEntropySrcEsEntropyValid);
      break;
    // case kTopEarlgreyPlicPeripheralFlashCtrl:
    //   PERIPHERAL_ISR(flash_ctrl, flash_ctrl,
    //   kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty); break;
    case kTopEarlgreyPlicPeripheralGpio:
      PERIPHERAL_ISR(gpio, gpio, kTopEarlgreyPlicIrqIdGpioGpio0);
      break;
    case kTopEarlgreyPlicPeripheralHmac:
      PERIPHERAL_ISR(hmac, hmac, kTopEarlgreyPlicIrqIdHmacHmacDone);
      break;
    case kTopEarlgreyPlicPeripheralI2c0:
      PERIPHERAL_ISR(i2c, i2c0, kTopEarlgreyPlicIrqIdI2c0FmtWatermark);
      break;
    case kTopEarlgreyPlicPeripheralI2c1:
      PERIPHERAL_ISR(i2c, i2c1, kTopEarlgreyPlicIrqIdI2c1FmtWatermark);
      break;
    case kTopEarlgreyPlicPeripheralI2c2:
      PERIPHERAL_ISR(i2c, i2c2, kTopEarlgreyPlicIrqIdI2c2FmtWatermark);
      break;
    case kTopEarlgreyPlicPeripheralKeymgr:
      PERIPHERAL_ISR(keymgr, keymgr, kTopEarlgreyPlicIrqIdKeymgrOpDone);
      break;
    case kTopEarlgreyPlicPeripheralKmac:
      PERIPHERAL_ISR(kmac, kmac, kTopEarlgreyPlicIrqIdKmacKmacDone);
      break;
    case kTopEarlgreyPlicPeripheralOtbn:
      PERIPHERAL_ISR(otbn, otbn, kTopEarlgreyPlicIrqIdOtbnDone);
      break;
    case kTopEarlgreyPlicPeripheralOtpCtrl:
      PERIPHERAL_ISR(otp_ctrl, otp_ctrl,
                     kTopEarlgreyPlicIrqIdOtpCtrlOtpOperationDone);
      break;
    // case kTopEarlgreyPlicPeripheralPattgen:
    //   PERIPHERAL_ISR(pattgen, pattgen, kTopEarlgreyPlicIrqIdPattgenDoneCh0);
    //   break;
    case kTopEarlgreyPlicPeripheralPwrmgrAon:
      PERIPHERAL_ISR(pwrmgr, pwrmgr_aon, kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
      break;
    // case kTopEarlgreyPlicPeripheralRvTimer:
    //   PERIPHERAL_ISR(rv_timer, rv_timer,
    //   kTopEarlgreyPlicIrqIdRvTimerTimerExpired0_0); break;
    case kTopEarlgreyPlicPeripheralSpiDevice:
      PERIPHERAL_ISR(spi_device, spi_device,
                     kTopEarlgreyPlicIrqIdSpiDeviceRxFull);
      break;
    // case kTopEarlgreyPlicPeripheralSpiHost0:
    //   PERIPHERAL_ISR(spi_host, spi_host0,
    //   kTopEarlgreyPlicIrqIdSpiHost0Error); break;
    // case kTopEarlgreyPlicPeripheralSpiHost1:
    //   PERIPHERAL_ISR(spi_host, spi_host1,
    //   kTopEarlgreyPlicIrqIdSpiHost1Error); break;
    // case kTopEarlgreyPlicPeripheralSysrstCtrlAon:
    //   PERIPHERAL_ISR(sysrst_ctrl, sysrst_ctrl_aon,
    //   kTopEarlgreyPlicIrqIdSysrstCtrlAonSysrstCtrl); break;
    case kTopEarlgreyPlicPeripheralUart0:
      PERIPHERAL_ISR(uart, uart0, kTopEarlgreyPlicIrqIdUart0TxWatermark);
      break;
    case kTopEarlgreyPlicPeripheralUart1:
      PERIPHERAL_ISR(uart, uart1, kTopEarlgreyPlicIrqIdUart1TxWatermark);
      break;
    case kTopEarlgreyPlicPeripheralUart2:
      PERIPHERAL_ISR(uart, uart2, kTopEarlgreyPlicIrqIdUart2TxWatermark);
      break;
    case kTopEarlgreyPlicPeripheralUart3:
      PERIPHERAL_ISR(uart, uart3, kTopEarlgreyPlicIrqIdUart3TxWatermark);
      break;
    case kTopEarlgreyPlicPeripheralUsbdev:
      PERIPHERAL_ISR(usbdev, usbdev, kTopEarlgreyPlicIrqIdUsbdevPktReceived);
      break;
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
  // PERIPHERAL_INIT(adc_ctrl, adc_ctrl_aon,
  // TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR);
  PERIPHERAL_INIT(alert_handler, alert_handler,
                  TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR);
  // PERIPHERAL_INIT(aon_timer, aon_timer_aon,
  // TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR);
  PERIPHERAL_INIT(csrng, csrng, TOP_EARLGREY_CSRNG_BASE_ADDR);
  PERIPHERAL_INIT(edn, edn0, TOP_EARLGREY_EDN0_BASE_ADDR);
  PERIPHERAL_INIT(edn, edn1, TOP_EARLGREY_EDN1_BASE_ADDR);
  PERIPHERAL_INIT(entropy_src, entropy_src, TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR);
  // PERIPHERAL_INIT(flash_ctrl, flash_ctrl,
  // TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR);
  PERIPHERAL_INIT(gpio, gpio, TOP_EARLGREY_GPIO_BASE_ADDR);
  PERIPHERAL_INIT(hmac, hmac, TOP_EARLGREY_HMAC_BASE_ADDR);
  PERIPHERAL_INIT(i2c, i2c0, TOP_EARLGREY_I2C0_BASE_ADDR);
  PERIPHERAL_INIT(i2c, i2c1, TOP_EARLGREY_I2C1_BASE_ADDR);
  PERIPHERAL_INIT(i2c, i2c2, TOP_EARLGREY_I2C2_BASE_ADDR);
  PERIPHERAL_INIT(keymgr, keymgr, TOP_EARLGREY_KEYMGR_BASE_ADDR);
  PERIPHERAL_INIT(kmac, kmac, TOP_EARLGREY_KMAC_BASE_ADDR);
  PERIPHERAL_INIT(otbn, otbn, TOP_EARLGREY_OTBN_BASE_ADDR);
  PERIPHERAL_INIT(otp_ctrl, otp_ctrl, TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  // PERIPHERAL_INIT(pattgen, pattgen, TOP_EARLGREY_PATTGEN_BASE_ADDR);
  PERIPHERAL_INIT(pwrmgr, pwrmgr_aon, TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  // PERIPHERAL_INIT(rv_timer, rv_timer, TOP_EARLGREY_RV_TIMER_BASE_ADDR);
  PERIPHERAL_INIT(spi_device, spi_device, TOP_EARLGREY_SPI_DEVICE_BASE_ADDR);
  // PERIPHERAL_INIT(spi_host, spi_host0, TOP_EARLGREY_SPI_HOST0_BASE_ADDR);
  // PERIPHERAL_INIT(spi_host, spi_host1, TOP_EARLGREY_SPI_HOST1_BASE_ADDR);
  // PERIPHERAL_INIT(sysrst_ctrl, sysrst_ctrl_aon,
  // TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR);
  PERIPHERAL_INIT(uart, uart0, TOP_EARLGREY_UART0_BASE_ADDR);
  PERIPHERAL_INIT(uart, uart1, TOP_EARLGREY_UART1_BASE_ADDR);
  PERIPHERAL_INIT(uart, uart2, TOP_EARLGREY_UART2_BASE_ADDR);
  PERIPHERAL_INIT(uart, uart3, TOP_EARLGREY_UART3_BASE_ADDR);
  PERIPHERAL_INIT(usbdev, usbdev, TOP_EARLGREY_USBDEV_BASE_ADDR);

  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(base_addr, &plic));
}

/**
 * Clears pending IRQs in all peripherals.
 */
static void peripheral_irqs_clear(void) {
  // PERIPHERAL_IRQS_CLEAR(adc_ctrl_aon);
  PERIPHERAL_IRQS_CLEAR(alert_handler);
  // PERIPHERAL_IRQS_CLEAR(aon_timer_aon);
  PERIPHERAL_IRQS_CLEAR(csrng);
  PERIPHERAL_IRQS_CLEAR(edn0);
  PERIPHERAL_IRQS_CLEAR(edn1);
  PERIPHERAL_IRQS_CLEAR(entropy_src);
  // PERIPHERAL_IRQS_CLEAR(flash_ctrl);
  PERIPHERAL_IRQS_CLEAR(gpio);
  PERIPHERAL_IRQS_CLEAR(hmac);
  PERIPHERAL_IRQS_CLEAR(i2c0);
  PERIPHERAL_IRQS_CLEAR(i2c1);
  PERIPHERAL_IRQS_CLEAR(i2c2);
  PERIPHERAL_IRQS_CLEAR(keymgr);
  PERIPHERAL_IRQS_CLEAR(kmac);
  PERIPHERAL_IRQS_CLEAR(otbn);
  PERIPHERAL_IRQS_CLEAR(otp_ctrl);
  // PERIPHERAL_IRQS_CLEAR(pattgen);
  PERIPHERAL_IRQS_CLEAR(pwrmgr_aon);
  // PERIPHERAL_IRQS_CLEAR(rv_timer);
  PERIPHERAL_IRQS_CLEAR(spi_device);
  // PERIPHERAL_IRQS_CLEAR(spi_host0);
  // PERIPHERAL_IRQS_CLEAR(spi_host1);
  // PERIPHERAL_IRQS_CLEAR(sysrst_ctrl_aon);
  PERIPHERAL_IRQS_CLEAR(uart0);
  PERIPHERAL_IRQS_CLEAR(uart1);
  PERIPHERAL_IRQS_CLEAR(uart2);
  PERIPHERAL_IRQS_CLEAR(uart3);
  PERIPHERAL_IRQS_CLEAR(usbdev);
}

/**
 * Enables all IRQs in all peripherals.
 */
static void peripheral_irqs_enable(void) {
  // PERIPHERAL_IRQS_ENABLE(adc_ctrl, adc_ctrl_aon);
  PERIPHERAL_IRQS_ENABLE(alert_handler, alert_handler);
  // PERIPHERAL_IRQS_ENABLE(aon_timer, aon_timer_aon);
  PERIPHERAL_IRQS_ENABLE(csrng, csrng);
  PERIPHERAL_IRQS_ENABLE(edn, edn0);
  PERIPHERAL_IRQS_ENABLE(edn, edn1);
  PERIPHERAL_IRQS_ENABLE(entropy_src, entropy_src);
  // PERIPHERAL_IRQS_ENABLE(flash_ctrl, flash_ctrl);
  PERIPHERAL_IRQS_ENABLE(gpio, gpio);
  PERIPHERAL_IRQS_ENABLE(hmac, hmac);
  PERIPHERAL_IRQS_ENABLE(i2c, i2c0);
  PERIPHERAL_IRQS_ENABLE(i2c, i2c1);
  PERIPHERAL_IRQS_ENABLE(i2c, i2c2);
  PERIPHERAL_IRQS_ENABLE(keymgr, keymgr);
  PERIPHERAL_IRQS_ENABLE(kmac, kmac);
  PERIPHERAL_IRQS_ENABLE(otbn, otbn);
  PERIPHERAL_IRQS_ENABLE(otp_ctrl, otp_ctrl);
  // PERIPHERAL_IRQS_ENABLE(pattgen, pattgen);
  PERIPHERAL_IRQS_ENABLE(pwrmgr, pwrmgr_aon);
  // PERIPHERAL_IRQS_ENABLE(rv_timer, rv_timer);
  PERIPHERAL_IRQS_ENABLE(spi_device, spi_device);
  // PERIPHERAL_IRQS_ENABLE(spi_host, spi_host0);
  // PERIPHERAL_IRQS_ENABLE(spi_host, spi_host1);
  // PERIPHERAL_IRQS_ENABLE(sysrst_ctrl, sysrst_ctrl_aon);
  PERIPHERAL_IRQS_ENABLE(uart, uart0);
  PERIPHERAL_IRQS_ENABLE(uart, uart1);
  PERIPHERAL_IRQS_ENABLE(uart, uart2);
  PERIPHERAL_IRQS_ENABLE(uart, uart3);
  PERIPHERAL_IRQS_ENABLE(usbdev, usbdev);
}

/**
 * Triggers all IRQs in all peripherals one by one.
 *
 * Walks through all instances of all peripherals and triggers an interrupt one
 * by one. Instead of invoking WFI, it waits for a couple of cycles with nops,
 * and then checks if the right interrupt was handled. The ISR which the CPU
 * jumps into checks if the correct interrupt from the right instance triggered.
 */
static void peripheral_irqs_trigger(void) {
  // PERIPHERAL_IRQS_TRIGGER(adc_ctrl, adc_ctrl_aon,
  // kTopEarlgreyPlicPeripheralAdcCtrlAon,
  //                         kDifAdcCtrlIrqDebugCable,
  //                         kDifAdcCtrlIrqDebugCable);
  PERIPHERAL_IRQS_TRIGGER(alert_handler, alert_handler,
                          kTopEarlgreyPlicPeripheralAlertHandler,
                          kDifAlertHandlerIrqClassa, kDifAlertHandlerIrqClassd);
  // PERIPHERAL_IRQS_TRIGGER(aon_timer, aon_timer_aon,
  // kTopEarlgreyPlicPeripheralAonTimerAon,
  //                         kDifAonTimerIrqWkupTimerExpired,
  //                         kDifAonTimerIrqWdogTimerBark);
  PERIPHERAL_IRQS_TRIGGER(csrng, csrng, kTopEarlgreyPlicPeripheralCsrng,
                          kDifCsrngIrqCsCmdReqDone, kDifCsrngIrqCsFatalErr);
  PERIPHERAL_IRQS_TRIGGER(edn, edn0, kTopEarlgreyPlicPeripheralEdn0,
                          kDifEdnIrqEdnCmdReqDone, kDifEdnIrqEdnFatalErr);
  PERIPHERAL_IRQS_TRIGGER(edn, edn1, kTopEarlgreyPlicPeripheralEdn1,
                          kDifEdnIrqEdnCmdReqDone, kDifEdnIrqEdnFatalErr);
  PERIPHERAL_IRQS_TRIGGER(
      entropy_src, entropy_src, kTopEarlgreyPlicPeripheralEntropySrc,
      kDifEntropySrcIrqEsEntropyValid, kDifEntropySrcIrqEsFatalErr);
  // PERIPHERAL_IRQS_TRIGGER(flash_ctrl, flash_ctrl,
  // kTopEarlgreyPlicPeripheralFlashCtrl,
  //                         kDifFlashCtrlIrqProgEmpty,
  //                         kDifFlashCtrlIrqCorrErr);
  PERIPHERAL_IRQS_TRIGGER(gpio, gpio, kTopEarlgreyPlicPeripheralGpio,
                          kDifGpioIrqGpio0, kDifGpioIrqGpio31);
  PERIPHERAL_IRQS_TRIGGER(hmac, hmac, kTopEarlgreyPlicPeripheralHmac,
                          kDifHmacIrqHmacDone, kDifHmacIrqHmacErr);
  PERIPHERAL_IRQS_TRIGGER(i2c, i2c0, kTopEarlgreyPlicPeripheralI2c0,
                          kDifI2cIrqFmtWatermark, kDifI2cIrqHostTimeout);
  PERIPHERAL_IRQS_TRIGGER(i2c, i2c1, kTopEarlgreyPlicPeripheralI2c1,
                          kDifI2cIrqFmtWatermark, kDifI2cIrqHostTimeout);
  PERIPHERAL_IRQS_TRIGGER(i2c, i2c2, kTopEarlgreyPlicPeripheralI2c2,
                          kDifI2cIrqFmtWatermark, kDifI2cIrqHostTimeout);
  PERIPHERAL_IRQS_TRIGGER(keymgr, keymgr, kTopEarlgreyPlicPeripheralKeymgr,
                          kDifKeymgrIrqOpDone, kDifKeymgrIrqOpDone);
  PERIPHERAL_IRQS_TRIGGER(kmac, kmac, kTopEarlgreyPlicPeripheralKmac,
                          kDifKmacIrqKmacDone, kDifKmacIrqKmacErr);
  PERIPHERAL_IRQS_TRIGGER(otbn, otbn, kTopEarlgreyPlicPeripheralOtbn,
                          kDifOtbnIrqDone, kDifOtbnIrqDone);
  PERIPHERAL_IRQS_TRIGGER(otp_ctrl, otp_ctrl, kTopEarlgreyPlicPeripheralOtpCtrl,
                          kDifOtpCtrlIrqOtpOperationDone,
                          kDifOtpCtrlIrqOtpError);
  // PERIPHERAL_IRQS_TRIGGER(pattgen, pattgen,
  // kTopEarlgreyPlicPeripheralPattgen,
  //                         kDifPattgenIrqDoneCh0, kDifPattgenIrqDoneCh1);
  PERIPHERAL_IRQS_TRIGGER(pwrmgr, pwrmgr_aon,
                          kTopEarlgreyPlicPeripheralPwrmgrAon,
                          kDifPwrmgrIrqWakeup, kDifPwrmgrIrqWakeup);
  // PERIPHERAL_IRQS_TRIGGER(rv_timer, rv_timer,
  // kTopEarlgreyPlicPeripheralRvTimer,
  //                         kDifRvTimerIrqTimerExpired0_0,
  //                         kDifRvTimerIrqTimerExpired0_0);
  PERIPHERAL_IRQS_TRIGGER(
      spi_device, spi_device, kTopEarlgreyPlicPeripheralSpiDevice,
      kDifSpiDeviceIrqRxFull, kDifSpiDeviceIrqTpmHeaderNotEmpty);
  // PERIPHERAL_IRQS_TRIGGER(spi_host, spi_host0,
  // kTopEarlgreyPlicPeripheralSpiHost0,
  //                         kDifSpiHostIrqError, kDifSpiHostIrqSpiEvent);
  // PERIPHERAL_IRQS_TRIGGER(spi_host, spi_host1,
  // kTopEarlgreyPlicPeripheralSpiHost1,
  //                         kDifSpiHostIrqError, kDifSpiHostIrqSpiEvent);
  // PERIPHERAL_IRQS_TRIGGER(sysrst_ctrl, sysrst_ctrl_aon,
  // kTopEarlgreyPlicPeripheralSysrstCtrlAon,
  //                         kDifSysrstCtrlIrqSysrstCtrl,
  //                         kDifSysrstCtrlIrqSysrstCtrl);
  PERIPHERAL_IRQS_TRIGGER(uart, uart0, kTopEarlgreyPlicPeripheralUart0,
                          kDifUartIrqTxWatermark, kDifUartIrqRxParityErr);
  PERIPHERAL_IRQS_TRIGGER(uart, uart1, kTopEarlgreyPlicPeripheralUart1,
                          kDifUartIrqTxWatermark, kDifUartIrqRxParityErr);
  PERIPHERAL_IRQS_TRIGGER(uart, uart2, kTopEarlgreyPlicPeripheralUart2,
                          kDifUartIrqTxWatermark, kDifUartIrqRxParityErr);
  PERIPHERAL_IRQS_TRIGGER(uart, uart3, kTopEarlgreyPlicPeripheralUart3,
                          kDifUartIrqTxWatermark, kDifUartIrqRxParityErr);
  PERIPHERAL_IRQS_TRIGGER(usbdev, usbdev, kTopEarlgreyPlicPeripheralUsbdev,
                          kDifUsbdevIrqPktReceived, kDifUsbdevIrqLinkOutErr);
}

const test_config_t kTestConfig;

bool test_main(void) {
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  peripherals_init();
  rv_plic_testutils_irq_range_enable(
      &plic, kHart, kTopEarlgreyPlicIrqIdNone + 1, kTopEarlgreyPlicIrqIdLast);
  peripheral_irqs_clear();
  peripheral_irqs_enable();
  peripheral_irqs_trigger();
  return true;
}
