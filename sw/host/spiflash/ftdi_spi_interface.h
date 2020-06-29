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
    int32_t device_vendor_id;

    /** USB device product ID. */
    int32_t device_product_id;

    /** USB device serial number. */
    std::string device_serial_number;

    /** Time to wait between attempts to check the hash in nanoseconds. */
    int32_t hash_read_delay_ns = 10000;

    /** Time before giving up on looking for the correct hash. */
    int32_t hash_read_timeout_ns = 1000000;

    /** FTDI Configuration. This can be made configurable later on if needed.
     * Default value is 1MHz. */
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
