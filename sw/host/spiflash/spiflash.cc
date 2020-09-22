// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <assert.h>
#include <fstream>
#include <getopt.h>
#include <iterator>
#include <memory>
#include <sstream>
#include <string>

#include "sw/host/spiflash/ftdi_spi_interface.h"
#include "sw/host/spiflash/spi_interface.h"
#include "sw/host/spiflash/updater.h"
#include "sw/host/spiflash/verilator_spi_interface.h"

namespace {

using opentitan::spiflash::Frame;
using opentitan::spiflash::FtdiSpiInterface;
using opentitan::spiflash::SpiInterface;
using opentitan::spiflash::Updater;
using opentitan::spiflash::VerilatorSpiInterface;

constexpr char kUsageString[] = R"R( usage options:
  --input=Input image in binary format.

FTDI Options:
  [--dev-id="vid:pid"] FTDI device ID.
    vid: Vendor ID in string hex format.
    pid: Product ID in string hex format.
  [--dev-sn=string] FTDI serial number. Requires --dev-id to be set.

Verilator Options:
  [--verilator=filehandle] Enables Verilator mode with SPI filehandle.

DV Options:
  [--dump-frames=filehandle] Dump binary SPI flash frames in binary format.
)R";

/** SPI flash list of supported command actions. */
enum class SpiFlashAction {
  /** Invalid command action. */
  kInvalid = 0,

  /** Run SPI flash in FTDI mode. */
  kFtdi,

  /** Run SPI flash in Verilator mode. */
  kVerilator,

  /** Covert input binrary into frames. */
  kDumpFrames,

  /** Print usage information/help. */
  kPrintUsage,
};

/** SPI flash configuration options. */
struct SpiFlashOpts {
  /** Input file in binary format. */
  std::string input;

  /** Target SPI device handle. */
  std::string target;

  /** Output filename to dump SPI frames */
  std::string output_filename;

  /** Set to SPI flash  mode of operation */
  SpiFlashAction action = SpiFlashAction::kInvalid;

  /** FTDI configuration options. */
  FtdiSpiInterface::Options ftdi_options;
};

/**
 * Get `filename` contents and store them in `contents`. Using std::string for
 * `filename` because underlying open file call requires a C string.
 */
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

/**
 * Store the contetns of `code` formatted int SPI flash frame binary format
 * into `output_filename`
 */
bool DumpFramesToFile(const std::string &code,
                      const std::string &output_filename) {
  std::vector<Frame> frames;
  if (!Updater::GenerateFrames(code, &frames)) {
    return false;
  }
  std::ofstream out_stream;
  out_stream.open(output_filename, std::ofstream::out | std::ofstream::binary);
  if (!out_stream.good()) {
    std::cerr << "Unable to open file: " << output_filename << std::endl;
    return false;
  }
  for (const Frame &f : frames) {
    out_stream.write(reinterpret_cast<const char *>(&f), sizeof(Frame));
    if (!out_stream.good()) {
      std::cerr << "Detected write error. Output file may be corrupted."
                << std::endl;
      out_stream.close();
      return false;
    }
  }
  out_stream.close();
  return true;
}

/** Print help menu. */
static void PrintUsage(int argc, char *argv[]) {
  assert(argc >= 1);
  std::cerr << argv[0] << kUsageString << std::endl;
}

/*
 * Extract the vendor and product ID from `device_id` and store the values
 * in `options`.
 *
 * This function may throw exceptions.
 *
 * @return true on success.
 */
bool ParseDeviceID(const std::string &device_id, SpiFlashOpts *options) {
  size_t token_pos = device_id.find(':');
  if (token_pos == std::string::npos) {
    std::cerr << "Unable to find device separator ':' in --device-id."
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

/*
 * Parse command line arguments and store results in `options`.
 */
bool ParseArgs(int argc, char **argv, SpiFlashOpts *options) {
  assert(options);
  const struct option long_options[] = {
      {"input", required_argument, nullptr, 'i'},
      {"dev-id", required_argument, nullptr, 'd'},
      {"dev-sn", required_argument, nullptr, 'n'},
      {"dump-frames", required_argument, nullptr, 'x'},
      {"verilator", required_argument, nullptr, 's'},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, no_argument, nullptr, 0}};

  while (true) {
    int c = getopt_long(argc, argv, "i:d:n:s:x:h?", long_options, nullptr);
    if (c == -1) {
      // if only input file was given default to using FTDI
      if (!options->input.empty() &&
          options->action == SpiFlashAction::kInvalid) {
        options->action = SpiFlashAction::kFtdi;
      }
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
        options->action = SpiFlashAction::kFtdi;
        options->ftdi_options.device_serial_number = optarg;
        break;
      case 's':
        options->action = SpiFlashAction::kVerilator;
        options->target = optarg;
        break;
      case 'x':
        options->action = SpiFlashAction::kDumpFrames;
        options->output_filename = optarg;
        break;
      case '?':
      case 'h':
        options->action = SpiFlashAction::kPrintUsage;
        break;
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

  if (spi_flash_options.action == SpiFlashAction::kInvalid) {
    std::cerr << "Unable to detect valid command line arguments." << std::endl;
    PrintUsage(argc, argv);
    return 1;
  }

  if (spi_flash_options.action == SpiFlashAction::kPrintUsage) {
    PrintUsage(argc, argv);
    return 0;
  }

  std::string code;
  if (!GetFileContents(spi_flash_options.input, &code)) {
    return 1;
  }

  if (spi_flash_options.action == SpiFlashAction::kDumpFrames) {
    return DumpFramesToFile(code, spi_flash_options.output_filename) ? 0 : 1;
  }

  std::unique_ptr<SpiInterface> spi;
  if (spi_flash_options.action == SpiFlashAction::kVerilator) {
    spi = std::make_unique<VerilatorSpiInterface>(spi_flash_options.target);
  } else {
    spi = std::make_unique<FtdiSpiInterface>(spi_flash_options.ftdi_options);
  }
  if (!spi->Init()) {
    return 1;
  }

  Updater::Options options;
  options.code = code;

  Updater updater(options, std::move(spi));
  return updater.Run() ? 0 : 1;
}
