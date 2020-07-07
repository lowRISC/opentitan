// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_HOST_SPIFLASH_SPI_INTERFACE_H_
#define OPENTITAN_SW_HOST_SPIFLASH_SPI_INTERFACE_H_

#include <cstdint>
#include <cstring>

namespace opentitan {
namespace spiflash {

/**
 * This class defines the SPI interface used to communicate with an OpenTitan
 * device.
 */
class SpiInterface {
 public:
  SpiInterface() = default;
  virtual ~SpiInterface() = default;

  // Not copy or movable
  SpiInterface(const SpiInterface &) = delete;
  SpiInterface &operator=(const SpiInterface &) = delete;

  /** Initialize SPI interface. Returns true on success. */
  virtual bool Init() = 0;

  /**
   * Transmit bytes from `tx` buffer. The number of bytes are defined by `size`.
   *
   * @param tx   transmit buffer.
   * @param size number of bytes to transmit.
   *
   * @return true on success, false otherwise.
   */
  virtual bool TransmitFrame(const uint8_t *tx, size_t size) = 0;

  /**
   * Checks hash response from SPI interface.
   *
   * Wait until the hash from the previously sent is able to be read. The
   * previous frame to check the hash for should be provided in `tx` and the
   * frame's length as `size`.
   *
   * @param tx   transmit buffer.
   * @param size number of bytes in `tx` buffer.
   *
   * @return true if hash matches
   */
  virtual bool CheckHash(const uint8_t *tx, size_t size) = 0;
};

}  // namespace spiflash
}  // namespace opentitan

#endif  // OPENTITAN_SW_HOST_SPIFLASH_SPI_INTERFACE_H_
