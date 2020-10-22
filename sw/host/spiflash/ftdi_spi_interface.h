// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_HOST_SPIFLASH_FTDI_SPI_INTERFACE_H_
#define OPENTITAN_SW_HOST_SPIFLASH_FTDI_SPI_INTERFACE_H_

#include <memory>
#include <string>

#include "sw/host/spiflash/spi_interface.h"

namespace opentitan {
namespace spiflash {

// Forward declaration used to hide MPSSE context.
struct MpsseHandle;

/**
 * Implements SPI interface for an OpenTitan design connected via FTDI.
 * FTDI provides an USB interface called Multi-Protocol Synchronous Serial
 * Engine (MPSSE) which gives access to SPI, I2C and JTAG. This class uses
 * MPSSE to communicate with the SPI device IP in OpenTitan.
 * This class is not thread safe.
 */
class FtdiSpiInterface : public SpiInterface {
 public:
  /** FTDI SPI configuration options. */
  struct Options {
    /** USB device vendor ID. */
    int32_t device_vendor_id = 0;

    /** USB device product ID. */
    int32_t device_product_id = 0;

    /** USB device serial number. */
    std::string device_serial_number;

    /** Time to wait between attempts to check the hash in microseconds. */
    int32_t hash_read_delay_us = 10000;

    /** Time to wait between reading the hash over SPI and checking it in
     *  microseconds. */
    int32_t hash_check_delay_us = 10000;

    /** Time before giving up on looking for the correct hash in
     *  microseconds. */
    int32_t hash_read_timeout_us = 400000;

    /** FTDI Configuration. This can be made configurable later on if needed.
     * Frequency in Hz. Default value is 1MHz. */
    int32_t spi_frequency = 1000000;
  };

  explicit FtdiSpiInterface(Options options);
  ~FtdiSpiInterface() override;

  bool Init() final;
  bool TransmitFrame(const uint8_t *tx, size_t size) final;
  bool CheckHash(const uint8_t *tx, size_t size) final;

 private:
  Options options_;
  std::unique_ptr<MpsseHandle> spi_;
};

}  // namespace spiflash
}  // namespace opentitan

#endif  // OPENTITAN_SW_HOST_SPIFLASH_FTDI_SPI_INTERFACE_H_
