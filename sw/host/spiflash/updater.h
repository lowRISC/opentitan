// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_HOST_SPIFLASH_UPDATER_H_
#define OPENTITAN_SW_HOST_SPIFLASH_UPDATER_H_

#include <openssl/sha.h>

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <memory>
#include <string>
#include <vector>

#include "sw/host/spiflash/spi_interface.h"

namespace opentitan {
namespace spiflash {

/** Implements the bootstrap SPI frame message. */
struct Frame {
  /** Frame header definition. */
  struct {
    /** Hash of the `Frame` message starting at the `frame_num` offset. */
    uint8_t hash[32];

    /** Frame number. Starting at 0. */
    uint32_t frame_num;

    /** Flash target offset. */
    uint32_t offset;
  } hdr;

  /** Frame payload. */
  uint8_t data[2048 - sizeof(hdr)];

  /** Returns available the frame available payload size in bytes. */
  size_t PayloadSize() const { return 2048 - sizeof(hdr); }
};

/**
 * Implements SPI flash update protocol.
 *
 * The firmare image is split into frames, and then sent to the SPI device.
 * More details will be added on the ack protocol once implemented.
 * This class is not thread safe due to the spi driver dependency.
 */
class Updater {
 public:
  /** Updater configuration settings. */
  struct Options {
    /** Firmware image in binary format. */
    std::string code;
    /** Flash erase delay in microseconds. */
    int32_t flash_erase_delay_us = 100000;
  };

  /**
   * Constructs updater instance with given configuration `options` and `spi`
   * interface.
   *
   * @param options `Updater` options @see Updater::Options.
   * @param spi     SPI interface @see SpiInterface.
   */
  Updater(Options options, std::unique_ptr<SpiInterface> spi)
      : options_(options), spi_(std::move(spi)) {}
  virtual ~Updater() = default;

  // Not copy or movable
  Updater(const Updater &) = delete;
  Updater &operator=(const Updater &) = delete;

  /**
   * Runs update flow returning true on success.
   *
   * @return true on success, false otherwise.
   */
  bool Run();

  /**
   * Generates `frames` from `code` image.
   *
   * @param code   software image in binary format.
   * @param[out] frames output SPI frames.
   *
   * @return true on success, false otherwise.
   */
  static bool GenerateFrames(const std::string &code,
                             std::vector<Frame> *frames);

 private:
  Options options_;
  std::unique_ptr<SpiInterface> spi_;
};

}  // namespace spiflash
}  // namespace opentitan

#endif  // OPENTITAN_SW_HOST_SPIFLASH_UPDATER_H_
