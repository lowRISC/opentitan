// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_TOP_DARJEELING_SW_TEST_UTILS_AUTOGEN_ISR_TESTUTILS_H_
#define OPENTITAN_SW_TOP_DARJEELING_SW_TEST_UTILS_AUTOGEN_ISR_TESTUTILS_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/autogen_testutils.py

/**
 * @file
 * @brief Default ISRs for each IP
 */

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
#include "sw/ip/socdbg_ctrl/dif/dif_socdbg_ctrl.h"
#include "sw/ip/spi_device/dif/dif_spi_device.h"
#include "sw/ip/spi_host/dif/dif_spi_host.h"
#include "sw/ip/uart/dif/dif_uart.h"
#include "sw/lib/sw/device/arch/device.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"

/**
 * A handle to a PLIC ISR context struct.
 */
typedef struct plic_isr_ctx {
  /**
   * A handle to a rv_plic.
   */
  dif_rv_plic_t *rv_plic;
  /**
   * The HART ID associated with the PLIC (correspond to a PLIC "target").
   */
  uint32_t hart_id;
} plic_isr_ctx_t;

/**
 * A handle to a alert_handler ISR context struct.
 */
typedef struct alert_handler_isr_ctx {
  /**
   * A handle to a alert_handler.
   */
  dif_alert_handler_t *alert_handler;
  /**
   * The PLIC IRQ ID where this alert_handler instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_alert_handler_start_irq_id;
  /**
   * The alert_handler IRQ that is expected to be encountered in the ISR.
   */
  dif_alert_handler_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} alert_handler_isr_ctx_t;

/**
 * A handle to a aon_timer ISR context struct.
 */
typedef struct aon_timer_isr_ctx {
  /**
   * A handle to a aon_timer.
   */
  dif_aon_timer_t *aon_timer;
  /**
   * The PLIC IRQ ID where this aon_timer instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_aon_timer_start_irq_id;
  /**
   * The aon_timer IRQ that is expected to be encountered in the ISR.
   */
  dif_aon_timer_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} aon_timer_isr_ctx_t;

/**
 * A handle to a csrng ISR context struct.
 */
typedef struct csrng_isr_ctx {
  /**
   * A handle to a csrng.
   */
  dif_csrng_t *csrng;
  /**
   * The PLIC IRQ ID where this csrng instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_csrng_start_irq_id;
  /**
   * The csrng IRQ that is expected to be encountered in the ISR.
   */
  dif_csrng_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} csrng_isr_ctx_t;

/**
 * A handle to a dma ISR context struct.
 */
typedef struct dma_isr_ctx {
  /**
   * A handle to a dma.
   */
  dif_dma_t *dma;
  /**
   * The PLIC IRQ ID where this dma instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_dma_start_irq_id;
  /**
   * The dma IRQ that is expected to be encountered in the ISR.
   */
  dif_dma_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} dma_isr_ctx_t;

/**
 * A handle to a edn ISR context struct.
 */
typedef struct edn_isr_ctx {
  /**
   * A handle to a edn.
   */
  dif_edn_t *edn;
  /**
   * The PLIC IRQ ID where this edn instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_edn_start_irq_id;
  /**
   * The edn IRQ that is expected to be encountered in the ISR.
   */
  dif_edn_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} edn_isr_ctx_t;

/**
 * A handle to a gpio ISR context struct.
 */
typedef struct gpio_isr_ctx {
  /**
   * A handle to a gpio.
   */
  dif_gpio_t *gpio;
  /**
   * The PLIC IRQ ID where this gpio instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_gpio_start_irq_id;
  /**
   * The gpio IRQ that is expected to be encountered in the ISR.
   */
  dif_gpio_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} gpio_isr_ctx_t;

/**
 * A handle to a hmac ISR context struct.
 */
typedef struct hmac_isr_ctx {
  /**
   * A handle to a hmac.
   */
  dif_hmac_t *hmac;
  /**
   * The PLIC IRQ ID where this hmac instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_hmac_start_irq_id;
  /**
   * The hmac IRQ that is expected to be encountered in the ISR.
   */
  dif_hmac_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} hmac_isr_ctx_t;

/**
 * A handle to a i2c ISR context struct.
 */
typedef struct i2c_isr_ctx {
  /**
   * A handle to a i2c.
   */
  dif_i2c_t *i2c;
  /**
   * The PLIC IRQ ID where this i2c instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_i2c_start_irq_id;
  /**
   * The i2c IRQ that is expected to be encountered in the ISR.
   */
  dif_i2c_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} i2c_isr_ctx_t;

/**
 * A handle to a keymgr_dpe ISR context struct.
 */
typedef struct keymgr_dpe_isr_ctx {
  /**
   * A handle to a keymgr_dpe.
   */
  dif_keymgr_dpe_t *keymgr_dpe;
  /**
   * The PLIC IRQ ID where this keymgr_dpe instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_keymgr_dpe_start_irq_id;
  /**
   * The keymgr_dpe IRQ that is expected to be encountered in the ISR.
   */
  dif_keymgr_dpe_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} keymgr_dpe_isr_ctx_t;

/**
 * A handle to a kmac ISR context struct.
 */
typedef struct kmac_isr_ctx {
  /**
   * A handle to a kmac.
   */
  dif_kmac_t *kmac;
  /**
   * The PLIC IRQ ID where this kmac instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_kmac_start_irq_id;
  /**
   * The kmac IRQ that is expected to be encountered in the ISR.
   */
  dif_kmac_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} kmac_isr_ctx_t;

/**
 * A handle to a mbx ISR context struct.
 */
typedef struct mbx_isr_ctx {
  /**
   * A handle to a mbx.
   */
  dif_mbx_t *mbx;
  /**
   * The PLIC IRQ ID where this mbx instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_mbx_start_irq_id;
  /**
   * The mbx IRQ that is expected to be encountered in the ISR.
   */
  dif_mbx_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} mbx_isr_ctx_t;

/**
 * A handle to a otbn ISR context struct.
 */
typedef struct otbn_isr_ctx {
  /**
   * A handle to a otbn.
   */
  dif_otbn_t *otbn;
  /**
   * The PLIC IRQ ID where this otbn instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_otbn_start_irq_id;
  /**
   * The otbn IRQ that is expected to be encountered in the ISR.
   */
  dif_otbn_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} otbn_isr_ctx_t;

/**
 * A handle to a otp_ctrl ISR context struct.
 */
typedef struct otp_ctrl_isr_ctx {
  /**
   * A handle to a otp_ctrl.
   */
  dif_otp_ctrl_t *otp_ctrl;
  /**
   * The PLIC IRQ ID where this otp_ctrl instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_otp_ctrl_start_irq_id;
  /**
   * The otp_ctrl IRQ that is expected to be encountered in the ISR.
   */
  dif_otp_ctrl_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} otp_ctrl_isr_ctx_t;

/**
 * A handle to a pwrmgr ISR context struct.
 */
typedef struct pwrmgr_isr_ctx {
  /**
   * A handle to a pwrmgr.
   */
  dif_pwrmgr_t *pwrmgr;
  /**
   * The PLIC IRQ ID where this pwrmgr instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_pwrmgr_start_irq_id;
  /**
   * The pwrmgr IRQ that is expected to be encountered in the ISR.
   */
  dif_pwrmgr_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} pwrmgr_isr_ctx_t;

/**
 * A handle to a rv_timer ISR context struct.
 */
typedef struct rv_timer_isr_ctx {
  /**
   * A handle to a rv_timer.
   */
  dif_rv_timer_t *rv_timer;
  /**
   * The PLIC IRQ ID where this rv_timer instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_rv_timer_start_irq_id;
  /**
   * The rv_timer IRQ that is expected to be encountered in the ISR.
   */
  dif_rv_timer_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} rv_timer_isr_ctx_t;

/**
 * A handle to a sensor_ctrl ISR context struct.
 */
typedef struct sensor_ctrl_isr_ctx {
  /**
   * A handle to a sensor_ctrl.
   */
  dif_sensor_ctrl_t *sensor_ctrl;
  /**
   * The PLIC IRQ ID where this sensor_ctrl instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_sensor_ctrl_start_irq_id;
  /**
   * The sensor_ctrl IRQ that is expected to be encountered in the ISR.
   */
  dif_sensor_ctrl_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} sensor_ctrl_isr_ctx_t;

/**
 * A handle to a soc_proxy ISR context struct.
 */
typedef struct soc_proxy_isr_ctx {
  /**
   * A handle to a soc_proxy.
   */
  dif_soc_proxy_t *soc_proxy;
  /**
   * The PLIC IRQ ID where this soc_proxy instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_soc_proxy_start_irq_id;
  /**
   * The soc_proxy IRQ that is expected to be encountered in the ISR.
   */
  dif_soc_proxy_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} soc_proxy_isr_ctx_t;

/**
 * A handle to a soc_proxy ISR context struct.
 */
typedef struct soc_proxy_isr_ctx {
  /**
   * A handle to a soc_proxy.
   */
  dif_soc_proxy_t *soc_proxy;
  /**
   * The PLIC IRQ ID where this soc_proxy instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_soc_proxy_start_irq_id;
  /**
   * The soc_proxy IRQ that is expected to be encountered in the ISR.
   */
  dif_soc_proxy_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} soc_proxy_isr_ctx_t;

/**
 * A handle to a socdbg_ctrl ISR context struct.
 */
typedef struct socdbg_ctrl_isr_ctx {
  /**
   * A handle to a socdbg_ctrl.
   */
  dif_socdbg_ctrl_t *socdbg_ctrl;
  /**
   * The PLIC IRQ ID where this socdbg_ctrl instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_socdbg_ctrl_start_irq_id;
  /**
   * The socdbg_ctrl IRQ that is expected to be encountered in the ISR.
   */
  dif_socdbg_ctrl_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} socdbg_ctrl_isr_ctx_t;

/**
 * A handle to a spi_device ISR context struct.
 */
typedef struct spi_device_isr_ctx {
  /**
   * A handle to a spi_device.
   */
  dif_spi_device_t *spi_device;
  /**
   * The PLIC IRQ ID where this spi_device instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_spi_device_start_irq_id;
  /**
   * The spi_device IRQ that is expected to be encountered in the ISR.
   */
  dif_spi_device_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} spi_device_isr_ctx_t;

/**
 * A handle to a spi_host ISR context struct.
 */
typedef struct spi_host_isr_ctx {
  /**
   * A handle to a spi_host.
   */
  dif_spi_host_t *spi_host;
  /**
   * The PLIC IRQ ID where this spi_host instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_spi_host_start_irq_id;
  /**
   * The spi_host IRQ that is expected to be encountered in the ISR.
   */
  dif_spi_host_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} spi_host_isr_ctx_t;

/**
 * A handle to a uart ISR context struct.
 */
typedef struct uart_isr_ctx {
  /**
   * A handle to a uart.
   */
  dif_uart_t *uart;
  /**
   * The PLIC IRQ ID where this uart instance's IRQs start.
   */
  dif_rv_plic_irq_id_t plic_uart_start_irq_id;
  /**
   * The uart IRQ that is expected to be encountered in the ISR.
   */
  dif_uart_irq_t expected_irq;
  /**
   * Whether or not a single IRQ is expected to be encountered in the ISR.
   */
  bool is_only_irq;
} uart_isr_ctx_t;

/**
 * Services an alert_handler IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param alert_handler_ctx A(n) alert_handler ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_alert_handler_isr(
    plic_isr_ctx_t plic_ctx, alert_handler_isr_ctx_t alert_handler_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_alert_handler_irq_t *irq_serviced);

/**
 * Services an aon_timer IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param aon_timer_ctx A(n) aon_timer ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_aon_timer_isr(
    plic_isr_ctx_t plic_ctx, aon_timer_isr_ctx_t aon_timer_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_aon_timer_irq_t *irq_serviced);

/**
 * Services an csrng IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param csrng_ctx A(n) csrng ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_csrng_isr(
    plic_isr_ctx_t plic_ctx, csrng_isr_ctx_t csrng_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_csrng_irq_t *irq_serviced);

/**
 * Services an dma IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param dma_ctx A(n) dma ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_dma_isr(
    plic_isr_ctx_t plic_ctx, dma_isr_ctx_t dma_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_dma_irq_t *irq_serviced);

/**
 * Services an edn IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param edn_ctx A(n) edn ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_edn_isr(
    plic_isr_ctx_t plic_ctx, edn_isr_ctx_t edn_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_edn_irq_t *irq_serviced);

/**
 * Services an gpio IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param gpio_ctx A(n) gpio ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_gpio_isr(
    plic_isr_ctx_t plic_ctx, gpio_isr_ctx_t gpio_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_gpio_irq_t *irq_serviced);

/**
 * Services an hmac IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param hmac_ctx A(n) hmac ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_hmac_isr(
    plic_isr_ctx_t plic_ctx, hmac_isr_ctx_t hmac_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_hmac_irq_t *irq_serviced);

/**
 * Services an i2c IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param i2c_ctx A(n) i2c ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_i2c_isr(
    plic_isr_ctx_t plic_ctx, i2c_isr_ctx_t i2c_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_i2c_irq_t *irq_serviced);

/**
 * Services an keymgr_dpe IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param keymgr_dpe_ctx A(n) keymgr_dpe ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_keymgr_dpe_isr(
    plic_isr_ctx_t plic_ctx, keymgr_dpe_isr_ctx_t keymgr_dpe_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_keymgr_dpe_irq_t *irq_serviced);

/**
 * Services an kmac IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param kmac_ctx A(n) kmac ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_kmac_isr(
    plic_isr_ctx_t plic_ctx, kmac_isr_ctx_t kmac_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_kmac_irq_t *irq_serviced);

/**
 * Services an mbx IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param mbx_ctx A(n) mbx ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_mbx_isr(
    plic_isr_ctx_t plic_ctx, mbx_isr_ctx_t mbx_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_mbx_irq_t *irq_serviced);

/**
 * Services an otbn IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param otbn_ctx A(n) otbn ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_otbn_isr(
    plic_isr_ctx_t plic_ctx, otbn_isr_ctx_t otbn_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_otbn_irq_t *irq_serviced);

/**
 * Services an otp_ctrl IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param otp_ctrl_ctx A(n) otp_ctrl ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_otp_ctrl_isr(
    plic_isr_ctx_t plic_ctx, otp_ctrl_isr_ctx_t otp_ctrl_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_otp_ctrl_irq_t *irq_serviced);

/**
 * Services an pwrmgr IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param pwrmgr_ctx A(n) pwrmgr ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_pwrmgr_isr(
    plic_isr_ctx_t plic_ctx, pwrmgr_isr_ctx_t pwrmgr_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_pwrmgr_irq_t *irq_serviced);

/**
 * Services an rv_timer IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param rv_timer_ctx A(n) rv_timer ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_rv_timer_isr(
    plic_isr_ctx_t plic_ctx, rv_timer_isr_ctx_t rv_timer_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_rv_timer_irq_t *irq_serviced);

/**
 * Services an sensor_ctrl IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param sensor_ctrl_ctx A(n) sensor_ctrl ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_sensor_ctrl_isr(
    plic_isr_ctx_t plic_ctx, sensor_ctrl_isr_ctx_t sensor_ctrl_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_sensor_ctrl_irq_t *irq_serviced);

/**
 * Services an soc_proxy IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param soc_proxy_ctx A(n) soc_proxy ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_soc_proxy_isr(
    plic_isr_ctx_t plic_ctx, soc_proxy_isr_ctx_t soc_proxy_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_soc_proxy_irq_t *irq_serviced);

/**
 * Services an soc_proxy IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param soc_proxy_ctx A(n) soc_proxy ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_soc_proxy_isr(
    plic_isr_ctx_t plic_ctx, soc_proxy_isr_ctx_t soc_proxy_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_soc_proxy_irq_t *irq_serviced);

/**
 * Services an socdbg_ctrl IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param socdbg_ctrl_ctx A(n) socdbg_ctrl ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_socdbg_ctrl_isr(
    plic_isr_ctx_t plic_ctx, socdbg_ctrl_isr_ctx_t socdbg_ctrl_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_socdbg_ctrl_irq_t *irq_serviced);

/**
 * Services an spi_device IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param spi_device_ctx A(n) spi_device ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_spi_device_isr(
    plic_isr_ctx_t plic_ctx, spi_device_isr_ctx_t spi_device_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_spi_device_irq_t *irq_serviced);

/**
 * Services an spi_host IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param spi_host_ctx A(n) spi_host ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_spi_host_isr(
    plic_isr_ctx_t plic_ctx, spi_host_isr_ctx_t spi_host_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_spi_host_irq_t *irq_serviced);

/**
 * Services an uart IRQ.
 *
 * @param plic_ctx A PLIC ISR context handle.
 * @param uart_ctx A(n) uart ISR context handle.
 * @param[out] peripheral_serviced Out param for the peripheral that was
 * serviced.
 * @param[out] irq_serviced Out param for the IRQ that was serviced.
 */
void isr_testutils_uart_isr(
    plic_isr_ctx_t plic_ctx, uart_isr_ctx_t uart_ctx,
    top_darjeeling_plic_peripheral_t *peripheral_serviced,
    dif_uart_irq_t *irq_serviced);

#endif  // OPENTITAN_SW_TOP_DARJEELING_SW_TEST_UTILS_AUTOGEN_ISR_TESTUTILS_H_
