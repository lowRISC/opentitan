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

// Implements SPI interface for an OpenTitan design connected via FTDI.
// FTDI provides an USB interface called Multi-Protocol Synchronous Serial
// Engine (MPSSE) which gives access to SPI, I2C and JTAG. This class uses
// MPSSE to communicate with the SPI device IP in OpenTitan.
// This class is not thread safe.
class FtdiSpiInterface : public SpiInterface {
 public:
  FtdiSpiInterface();
  ~FtdiSpiInterface() override;

  // Initialize interface.
  bool Init() final;

  // Transmit bytes from |tx| buffer and read data back onto |rx| buffer. The
  // number of bytes are defined by |size|.
  bool TransmitFrame(const uint8_t *tx, uint8_t *rx, size_t size) final;

 private:
  std::unique_ptr<MpsseHandle> spi_;
};

}  // namespace spiflash
}  // namespace opentitan

#endif  // OPENTITAN_SW_HOST_SPIFLASH_FTDI_SPI_INTERFACE_H_
