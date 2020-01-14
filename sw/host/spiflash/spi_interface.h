// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_HOST_SPIFLASH_SPI_INTERFACE_H_
#define OPENTITAN_SW_HOST_SPIFLASH_SPI_INTERFACE_H_

#include <cstdint>
#include <cstring>

namespace opentitan {
namespace spiflash {

// This class defines the SPI interface used to communicate with an OpenTitan
// device.
class SpiInterface {
 public:
  SpiInterface() = default;
  virtual ~SpiInterface() = default;

  // Not copy or movable
  SpiInterface(const SpiInterface &) = delete;
  SpiInterface &operator=(const SpiInterface &) = delete;

  // Initialize SPI interface. Returns true on success.
  virtual bool Init() = 0;

  // Transmit bytes from |tx| buffer and read data back onto |rx| buffer. The
  // number of bytes transferred is defined by |size|.
  virtual bool TransmitFrame(const uint8_t *tx, uint8_t *rx, size_t size) = 0;
};

}  // namespace spiflash
}  // namespace opentitan

#endif  // OPENTITAN_SW_HOST_SPIFLASH_SPI_INTERFACE_H_
