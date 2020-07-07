// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_HOST_SPIFLASH_VERILATOR_SPI_INTERFACE_H_
#define OPENTITAN_SW_HOST_SPIFLASH_VERILATOR_SPI_INTERFACE_H_

#include <string>

#include "sw/host/spiflash/spi_interface.h"

namespace opentitan {
namespace spiflash {

/**
 * Implements SPI interface for an OpenTitan instance running on Verilator.
 * The OpenTitan Verilator model provides a file handle for the SPI device
 * interface. This class sends ands recevies data to the device handle, and
 * adds synchronication delays between writes and reads.
 * This class is not thread safe.
 */
class VerilatorSpiInterface : public SpiInterface {
 public:
  /** Constructs instance pointing to the `spi_filename` file path. */
  explicit VerilatorSpiInterface(std::string spi_filename)
      : spi_filename_(spi_filename), fd_(-1) {}

  /**
   * Closes the internal file handle used to communicate with the SPI device.
   */
  ~VerilatorSpiInterface() override;

  bool Init() final;
  bool TransmitFrame(const uint8_t *tx, size_t size) final;
  bool CheckHash(const uint8_t *tx, size_t size) final;

 private:
  std::string spi_filename_;
  int fd_;
};

}  // namespace spiflash
}  // namespace opentitan

#endif  // OPENTITAN_SW_HOST_SPIFLASH_VERILATOR_SPI_INTERFACE_H_
