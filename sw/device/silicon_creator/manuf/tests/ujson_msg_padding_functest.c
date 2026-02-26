// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Peripheral handles.
 */
static dif_gpio_t gpio;
static dif_pinmux_t pinmux;

/**
 * ATE Indicator GPIOs.
 */
static const dif_gpio_pin_t kGpioPinSpiConsoleTxReady = 0;
static const dif_gpio_pin_t kGpioPinSpiConsoleRxReady = 1;

/**
 * UJSON payloads.
 */
static serdes_sha256_hash_t sha256_hash_msg;
static lc_token_hash_t lc_token_hash_msg;
static manuf_certgen_inputs_t certgen_inputs_msg;
static perso_blob_t perso_blob_msg;

OTTF_DEFINE_TEST_CONFIG(.console.type = kOttfConsoleSpiDevice,
                        .console.base_addr = TOP_EARLGREY_SPI_DEVICE_BASE_ADDR,
                        .console.test_may_clobber = false,
                        .console.putbuf_buffered = true,
                        .silence_console_prints = true,
                        .console_tx_indicator.enable = true,
                        .console_tx_indicator.spi_console_tx_ready_mio =
                            kTopEarlgreyPinmuxMioOutIoa5,
                        .console_tx_indicator.spi_console_tx_ready_gpio =
                            kGpioPinSpiConsoleTxReady);

static status_t peripheral_handles_init(void) {
  TRY(dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));
  TRY(dif_pinmux_init(mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR),
                      &pinmux));
  return OK_STATUS();
}

static status_t configure_ate_gpio_indicators(void) {
  // IOA6 / GPIO4 is for SPI console RX ready signal.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa6,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinSpiConsoleRxReady));
  // IOA5 / GPIO3 is for SPI console TX ready signal.
  TRY(dif_pinmux_output_select(
      &pinmux, kTopEarlgreyPinmuxMioOutIoa5,
      kTopEarlgreyPinmuxOutselGpioGpio0 + kGpioPinSpiConsoleTxReady));
  TRY(dif_gpio_output_set_enabled_all(&gpio, 0x3));  // Enable first 2 GPIOs.
  TRY(dif_gpio_write_all(&gpio, /*write_val=*/0));   // Intialize all to 0.
  return OK_STATUS();
}

static status_t send_ujson_msgs(ujson_t *uj) {
  // Set all fields in each UJSON payload to value with width less than max.
  perso_blob_msg.num_objs = 0x5;
  perso_blob_msg.next_free = 0x5;
  for (size_t i = 0; i < 100; ++i) {
    if (i < 2) {
      lc_token_hash_msg.hash[i] = 0x5;
    }
    if (i < 8) {
      sha256_hash_msg.data[i] = 0x5;
    }
    if (i < 20) {
      certgen_inputs_msg.dice_auth_key_key_id[i] = 0x5;
      certgen_inputs_msg.ext_auth_key_key_id[i] = 0x5;
    }
    perso_blob_msg.body[i] = 0x5;
  }

  // TX payloads to the host padding the payloads with whitespace.
  RESP_OK_PADDED_NO_CRC(ujson_serialize_with_padding_serdes_sha256_hash_t, uj,
                        &sha256_hash_msg, kSerdesSha256HashSerializedMaxSize);
  RESP_OK_PADDED_NO_CRC(ujson_serialize_with_padding_lc_token_hash_t, uj,
                        &lc_token_hash_msg, kLcTokenHashSerializedMaxSize);
  RESP_OK_PADDED_NO_CRC(ujson_serialize_with_padding_manuf_certgen_inputs_t, uj,
                        &certgen_inputs_msg,
                        kManufCertgenInputsSerializedMaxSize);
  RESP_OK_PADDED_NO_CRC(ujson_serialize_with_padding_perso_blob_t, uj,
                        &perso_blob_msg, kPersoBlobSerializedMaxSize);

  // RX payloads echoed back by host and check their sizes when received.
  TRY(ujson_deserialize_serdes_sha256_hash_t(uj, &sha256_hash_msg));
  TRY_CHECK(uj->str_size == kSerdesSha256HashSerializedMaxSize);
  TRY(ujson_deserialize_lc_token_hash_t(uj, &lc_token_hash_msg));
  TRY_CHECK(uj->str_size == kLcTokenHashSerializedMaxSize);
  TRY(ujson_deserialize_manuf_certgen_inputs_t(uj, &certgen_inputs_msg));
  TRY_CHECK(uj->str_size == kManufCertgenInputsSerializedMaxSize);
  TRY(ujson_deserialize_perso_blob_t(uj, &perso_blob_msg));
  TRY_CHECK(uj->str_size == kPersoBlobSerializedMaxSize);

  return OK_STATUS();
};

bool test_main(void) {
  CHECK_STATUS_OK(peripheral_handles_init());
  CHECK_STATUS_OK(configure_ate_gpio_indicators());
  ujson_t uj = ujson_ottf_console();
  CHECK_STATUS_OK(send_ujson_msgs(&uj));
  return true;
}
