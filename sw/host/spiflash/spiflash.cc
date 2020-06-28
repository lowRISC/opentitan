// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <fstream>
#include <getopt.h>
#include <memory>
#include <sstream>
#include <string>

#include "sw/host/spiflash/ftdi_spi_interface.h"
#include "sw/host/spiflash/spi_interface.h"
#include "sw/host/spiflash/updater.h"
#include "sw/host/spiflash/verilator_spi_interface.h"

namespace {

using opentitan::spiflash::FtdiSpiInterface;
using opentitan::spiflash::SpiInterface;
using opentitan::spiflash::Updater;
using opentitan::spiflash::VerilatorSpiInterface;

constexpr char kUsageString[] = R"R( usage options:
  --input=Input image in binary format.

FTDI Options:
  [--dev_id="vid:pid"] FTDI device ID.
    vid: Vendor ID in string hex format.
    pid: Product ID in string hex format.
  [--dev_sn=string] FTDI serial number. Requires --dev_id to be set.

Verilator Options:
  [--verilator=filehandle] Enables Verilator mode with SPI filehandle.)R";

// SPI flash configuration options.
struct SpiFlashOpts {
  // Input file in binary format.
  std::string input;

  // Target SPI device handle.
  std::string target;

  // Set to true to target Verilator environment.
  bool verilator = false;

  // FTDI configuration options.
  FtdiSpiInterface::Options ftdi_options;
};

// Get |filename| contents and store them in |contents|. Using std::string for
// |filename| because underlying open file call requires a C string.
bool GetFileContents(const std::string &filename, std::string *contents) {
  assert(contents);
  std::ifstream file_stream(filename, std::ios::in | std::ios::binary);
  if (!file_stream) {
    std::cerr << "Unable to open: " << filename << " errno: " << errno
              << std::endl;
    return false;
  }
  std::ostringstream in_stream;
  in_stream << file_stream.rdbuf();
  file_stream.close();
  *contents = in_stream.str();
  return true;
}

// Prints help menu.
static void PrintUsage(int argc, char *argv[]) {
  assert(argc >= 1);
  std::cerr << argv[0] << kUsageString << std::endl;
}

// Extracts the vendor and product ID from `device_id` and stores the values
// in `options`. Returns true on success.
// This function may throw exceptions.
bool ParseDeviceID(const std::string &device_id, SpiFlashOpts *options) {
  size_t token_pos = device_id.find(':');
  if (token_pos == std::string::npos) {
    std::cerr << "Unable to find device separator ':' in --device_id."
              << std::endl;
    return false;
  }

  std::string vendor_id = device_id.substr(/*pos=*/0, /*len=*/token_pos);
  options->ftdi_options.device_vendor_id =
      std::stoi(vendor_id, /*pos=*/0, /*base=*/16);

  std::string product_id =
      device_id.substr(/*pos=*/token_pos + 1, /*len=*/std::string::npos);
  options->ftdi_options.device_product_id =
      std::stoi(product_id, /*pos=*/0, /*base=*/16);

  return true;
}

// Parse command line arguments and store results in |options|.
bool ParseArgs(int argc, char **argv, SpiFlashOpts *options) {
  assert(options);
  const struct option long_options[] = {
      {"input", required_argument, nullptr, 'i'},
      {"dev_id", required_argument, nullptr, 'd'},
      {"dev_sn", required_argument, nullptr, 'n'},
      {"verilator", required_argument, nullptr, 's'},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, no_argument, nullptr, 0}};

  while (true) {
    int c = getopt_long(argc, argv, "i:d:n:s:h?", long_options, nullptr);
    if (c == -1) {
      return true;
    }

    switch (c) {
      case 0:
        break;
      case 'i':
        options->input = optarg;
        break;
      case 'd':
        if (!ParseDeviceID(std::string(optarg), options)) {
          return false;
        }
        break;
      case 'n':
        options->ftdi_options.device_serial_number = optarg;
        break;
      case 's':
        options->verilator = true;
        options->target = optarg;
        break;
      case '?':
      case 'h':
        PrintUsage(argc, argv);
      default:;
    }
  }
  return true;
}

}  // namespace

int main(int argc, char **argv) {
  SpiFlashOpts spi_flash_options;
  if (!ParseArgs(argc, argv, &spi_flash_options)) {
    std::cerr << "Failed to parse command line options." << std::endl;
    return 1;
  }

  std::unique_ptr<SpiInterface> spi;
  if (spi_flash_options.verilator) {
    spi = std::make_unique<VerilatorSpiInterface>(spi_flash_options.target);
  } else {
    spi = std::make_unique<FtdiSpiInterface>(spi_flash_options.ftdi_options);
  }
  if (!spi->Init()) {
    return 1;
  }

  Updater::Options options;
  if (!GetFileContents(spi_flash_options.input, &options.code)) {
    return 1;
  }
  Updater updater(options, std::move(spi));
  return updater.Run() ? 0 : 1;
}
