// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/host/spiflash/ftdi_spi_interface.h"

#include <assert.h>
#include <fcntl.h>
#include <termios.h>
#include <unistd.h>

#include <cstring>
#include <iostream>
#include <string>
#include <vector>

// Include MPSSE SPI library
extern "C" {
#include "sw/host/vendor/mpsse/mpsse.h"
}

namespace opentitan {
namespace spiflash {
namespace {

// Required delay to synchronize transactions with FPGA environment.
// TODO: If transmission is not successful, adapt this by an argument.
constexpr int kTransmitDelay = 1000000;

// FTDI Configuration. This can be made configurable later on if needed.
constexpr int kFrequency = 1000000;  // 1MHz

enum FtdiGpioMapping {
  // SRST_N reset.
  kGpioJtagSrstN = GPIOL1,

  // JTAG SPI_N select signal.
  kGpioJtagSpiN = GPIOL2,

  // Bootstrap pin.
  kBootstrapH = GPIOL3,
};

// Resets the target to go back to boot_rom. Assumes boot_rom will enter
// bootstrap mode.
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

// Wrapper struct used to hide mpsse_context since incomplete C struct
// declarations don't play in forward declarations.
struct MpsseHandle {
  struct mpsse_context *ctx;

  explicit MpsseHandle(struct mpsse_context *new_ctx) : ctx(new_ctx) {}
  ~MpsseHandle() {
    if (ctx != nullptr) {
      Close(ctx);
    }
  }
};

FtdiSpiInterface::FtdiSpiInterface() : spi_(nullptr) {}

FtdiSpiInterface::~FtdiSpiInterface() {
  if (spi_ != nullptr) {
    // TODO: Add interface to toggle bootstrap pin.
    PinLow(spi_->ctx, kBootstrapH);
  }
}

bool FtdiSpiInterface::Init() {
  struct mpsse_context *ctx = MPSSE(SPI0, kFrequency, MSB);
  if (ctx == nullptr) {
    std::cerr << "Unable to open FTDI SPI interface." << std::endl;
    return false;
  }
  spi_ = std::make_unique<MpsseHandle>(ctx);
  ResetTarget(ctx);
  return true;
}

bool FtdiSpiInterface::TransmitFrame(const uint8_t *tx, uint8_t *rx,
                                     size_t size) {
  assert(spi_ != nullptr);

  // The mpsse library is more permissive than the SpiInteface. Copying tx
  // to local buffer to handle issue internally.
  std::vector<uint8_t> tx_local(tx, tx + size);

  if (Start(spi_->ctx)) {
    std::cerr << "Unable to start spi transaction." << std::endl;
    return false;
  }
  uint8_t *tmp_rx = ::Transfer(spi_->ctx, tx_local.data(), size);
  if (Stop(spi_->ctx)) {
    std::cerr << "Unable to terminate spi transaction." << std::endl;
    if (tmp_rx) {
      free(tmp_rx);
    }
    return false;
  }
  if (tmp_rx == nullptr) {
    std::cerr << "Unable to transfer data. Frame size: " << size << std::endl;
    return false;
  }
  usleep(kTransmitDelay);
  memcpy(rx, tmp_rx, size);
  free(tmp_rx);
  return true;
}
}  // namespace spiflash
}  // namespace opentitan
