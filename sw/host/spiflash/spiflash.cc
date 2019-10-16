// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <getopt.h>

#include <fstream>
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
  [--verilator=filehandle] Enables Verilator mode with SPI filehandle.)R";

// SPI flash configuration options.
struct SpiFlashOpts {
  // Input file in binary format.
  std::string input;

  // Target SPI device handle.
  std::string target;

  // Set to true to target Verilator environment.
  bool verilator = false;
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

// Parse command line arguments and store results in |options|.
bool ParseArgs(int argc, char **argv, SpiFlashOpts *options) {
  assert(options);
  const struct option long_options[] = {
      {"input", required_argument, nullptr, 'i'},
      {"verilator", required_argument, nullptr, 's'},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, no_argument, nullptr, 0}};

  while (true) {
    int c = getopt_long(argc, argv, "i:s:h?", long_options, nullptr);
    if (c == -1) {
      return true;
    }

    switch (c) {
      case 0:
        break;
      case 'i':
        options->input = optarg;
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
    spi = std::make_unique<FtdiSpiInterface>();
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
