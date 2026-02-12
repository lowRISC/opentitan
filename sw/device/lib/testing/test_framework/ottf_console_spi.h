// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_SPI_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_SPI_H_

#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/testing/test_framework/ottf_console_types.h"

struct ottf_console;

typedef struct ottf_console_spi {
  /** DIF handle. */
  dif_spi_device_handle_t dif;
  /** SPI device frame number. */
  uint32_t frame_num;
  /** TX ready GPIO, set to kOttfSpiNoTxGpio if not used. */
  dif_gpio_pin_t tx_ready_gpio;
} ottf_console_spi_t;

void *ottf_console_spi_get_main_staging_buffer(size_t *size);

/**
 * Configures the given SPI device to be used by the OTTF console.
 *
 * @param console Console pointer
 * @param base_addr The base address of the SPI device to use.
 * @param tx_ready_enable Enable TX indicator
 * @param tx_ready_gpio If TX indicator is enable, GPIO number to use.
 * @param tx_ready_mio If TX indicator is enable, MIO number to which to connect
 * it.
 */
void ottf_console_configure_spi_device(ottf_console_t *console,
                                       uintptr_t base_addr,
                                       bool tx_ready_enable,
                                       uint32_t tx_ready_gpio,
                                       uint32_t tx_ready_mio);

/**
 * Read data from the host via the OTTF SPI device console into a provided
 * buffer.
 *
 * The function waits for spi upload commands, then transfers data in chunks
 * until a transmission complete signal is received. If the size of data sent
 * from the host is greater than the provided buffer, then the excess data will
 * be discarded.
 *
 * @param console Pointer to the console.
 * @param buf_size The size, in bytes, of the `buf`.
 * @param[out] buf A pointer to the location where the data should be stored.
 * @return The number of bytes actually received from the host.
 */
size_t ottf_console_spi_device_read(ottf_console_t *console, size_t buf_size,
                                    uint8_t *const buf);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_SPI_H_
