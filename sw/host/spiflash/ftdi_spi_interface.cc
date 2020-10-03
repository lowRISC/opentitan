// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/host/spiflash/ftdi_spi_interface.h"

#include <assert.h>
#include <chrono>
#include <cstring>
#include <fcntl.h>
#include <iostream>
#include <openssl/sha.h>
#include <string>
#include <termios.h>
#include <unistd.h>
#include <vector>

// Include MPSSE SPI library
extern "C" {
#include "sw/host/vendor/mpsse/mpsse.h"
}

namespace opentitan {
namespace spiflash {
namespace {

/** FTDI MPSSE GPIO Mappings */
enum FtdiGpioMapping {
  /** SRST_N reset. */
  kGpioJtagSrstN = GPIOL1,

  /** JTAG SPI_N select signal. */
  kGpioJtagSpiN = GPIOL2,

  /** Bootstrap pin. */
  kBootstrapH = GPIOL3,
};

/**
 * Resets the target to go back to boot_rom. Assumes boot_rom will enter
 * bootstrap mode.
 */
void ResetTarget(struct mpsse_context *ctx) {
  // Set bootstrap pin high
  PinHigh(ctx, kBootstrapH);

  // Enable JTAG mode by setting GPIOL2 high and toggle reset (GPIOL1)
  PinHigh(ctx, kGpioJtagSpiN);
  PinLow(ctx, kGpioJtagSrstN);
  usleep(100000);
  PinHigh(ctx, kGpioJtagSrstN);

  // Switch from JTAG to SPI mode. The delay is needed to make sure we don't
  // drop any frames.
  usleep(100000);
  PinLow(ctx, kGpioJtagSpiN);
}
}  // namespace

/**
 * Wrapper struct used to hide mpsse_context since incomplete C struct
 * declarations don't play in forward declarations.
 */
struct MpsseHandle {
  struct mpsse_context *ctx;

  explicit MpsseHandle(struct mpsse_context *new_ctx) : ctx(new_ctx) {}
  ~MpsseHandle() {
    if (ctx != nullptr) {
      Close(ctx);
    }
  }
};

FtdiSpiInterface::FtdiSpiInterface(Options options)
    : options_(options), spi_(nullptr) {}

FtdiSpiInterface::~FtdiSpiInterface() {
  if (spi_ != nullptr) {
    // TODO: Add interface to toggle bootstrap pin.
    PinLow(spi_->ctx, kBootstrapH);
  }
}

bool FtdiSpiInterface::Init() {
  if (!options_.device_serial_number.empty() &&
      (options_.device_vendor_id == 0 || options_.device_product_id == 0)) {
    std::cerr << "FTDI device serial number requires the vendor_id and product "
                 "id to be set."
              << std::endl;
    return false;
  }

  struct mpsse_context *ctx = nullptr;
  if (options_.device_vendor_id == 0 || options_.device_product_id == 0) {
    ctx = MPSSE(/*mode=*/SPI0, options_.spi_frequency, /*endianess=*/MSB);
  } else {
    const char *serial_number = options_.device_serial_number.empty()
                                    ? nullptr
                                    : options_.device_serial_number.c_str();
    ctx = Open(options_.device_vendor_id, options_.device_product_id,
               /*mode=*/SPI0, options_.spi_frequency, /*endianess=*/MSB,
               /*interface=*/IFACE_A, /*description=*/nullptr, serial_number);
  }
  if (ctx == nullptr) {
    std::cerr << "Unable to open FTDI SPI interface." << std::endl;
    return false;
  }
  spi_ = std::make_unique<MpsseHandle>(ctx);
  ResetTarget(ctx);
  return true;
}

bool FtdiSpiInterface::TransmitFrame(const uint8_t *tx, size_t size) {
  assert(spi_ != nullptr);

  // The mpsse library is more permissive than the SpiInteface. Copying tx
  // to local buffer to handle issue internally.
  std::vector<uint8_t> tx_local(tx, tx + size);

  if (Start(spi_->ctx)) {
    std::cerr << "Unable to start spi transaction." << std::endl;
    return false;
  }

  uint8_t *tmp_rx = ::Transfer(spi_->ctx, tx_local.data(), size);
  // We're not using the result of this read, so free it right away.
  if (tmp_rx == nullptr) {
    free(tmp_rx);
  }

  if (Stop(spi_->ctx)) {
    std::cerr << "Unable to terminate spi transaction." << std::endl;
    return false;
  }
  return true;
}

bool FtdiSpiInterface::CheckHash(const uint8_t *tx, size_t size) {
  uint8_t hash[SHA256_DIGEST_LENGTH];
  SHA256_CTX sha256;
  SHA256_Init(&sha256);
  SHA256_Update(&sha256, tx, size);
  SHA256_Final(hash, &sha256);

  uint8_t *rx;

  int hash_index = 0;
  bool hash_correct = false;

  if (Start(spi_->ctx)) {
    std::cerr << "Unable to start spi transaction." << std::endl;
    return false;
  }

  auto begin = std::chrono::steady_clock::now();
  auto now = begin;
  while (!hash_correct &&
         std::chrono::duration_cast<std::chrono::microseconds>(now - begin)
                 .count() < options_.hash_read_timeout_us) {
    usleep(options_.hash_read_delay_us);
    rx = nullptr;
    rx = ::Read(spi_->ctx, size);
    if (!rx) {
      std::cerr << "Read failed, did not allocate buffer." << std::endl;
      break;
    }

    // It appears that the hash is always the first 32 bytes in practice, but in
    // testing I've seen the hash appear at random locations in the message.
    // Checking for the hash at any location or even split between messages may
    // not be necessary, but it is probably safer.
    usleep(options_.hash_check_delay_us);
    for (int i = 0; !hash_correct && i < SHA256_DIGEST_LENGTH; ++i) {
      if (rx[i] == hash[hash_index]) {
        ++hash_index;
        if (hash_index == SHA256_DIGEST_LENGTH) {
          hash_correct = true;
        }
      } else {
        hash_index = 0;
      }
    }
    free(rx);
    now = std::chrono::steady_clock::now();
  }

  if (Stop(spi_->ctx)) {
    std::cerr << "Unable to terminate spi transaction." << std::endl;
    return false;
  }

  if (!hash_correct) {
    std::cerr << "Didn't receive correct hash before timeout." << std::endl;
  }

  return hash_correct;
}
}  // namespace spiflash
}  // namespace opentitan
