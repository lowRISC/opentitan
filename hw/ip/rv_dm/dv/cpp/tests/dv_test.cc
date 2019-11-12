// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "tests/dv_test.h"

#include <fstream>
#include <iostream>

DVTest::DVTest() {
  // Set config options to defaults
  reset_mode_ = kDVResetOnce;
  csr_mode_ = kDVCSRRandom;
  host_mode_ = kDVHostIdle;
  device_mode_ = kDVDeviceRandom;
}

bool DVTest::ReadTestConfig(std::string config_file) {
  // No test passed on cmd line -> use default values
  if (config_file == "") {
    return true;
  }
  // Open config file
  std::ifstream cfg;
  std::string line;
  cfg.open("tests/" + config_file + ".test");
  // Check config file exists
  if (!cfg) {
    std::cout << "ERRROR Test not found: tests/" << config_file << ".test"
              << std::endl;
    return false;
  }
  // Read config arguments from file
  while (getline(cfg, line)) {
    // Ignore comments
    if ((line.length() == 0) || (line.at(0) == '#')) {
      continue;
    }
    // Pull out config strings
    std::size_t split = line.find('=');
    std::string first = line.substr(0, split);
    std::string second = line.substr(split + 1, std::string::npos);
    // Parse all config options
    if (first == "reset_mode") {
      reset_mode_ = static_cast<DVTestResetMode>(std::stoi(second));
    }
    if (first == "csr_mode") {
      csr_mode_ = static_cast<DVCSRMode>(std::stoi(second));
    }
    if (first == "host_mode") {
      host_mode_ = static_cast<DVHostMode>(std::stoi(second));
    }
    if (first == "device_mode") {
      device_mode_ = static_cast<DVDeviceMode>(std::stoi(second));
    }
  }
  return true;
}

DVTestResetMode DVTest::GetResetMode() { return reset_mode_; }

DVCSRMode DVTest::GetCSRMode() { return csr_mode_; }

void DVTest::PrintConfig() {
  std::cout << "Test config:" << std::endl
            << "Reset mode:  " << StringResetMode() << std::endl
            << "CSR mode:    " << StringCSRMode() << std::endl
            << "Host mode:   " << StringHostMode() << std::endl
            << "Device mode: " << StringDeviceMode() << std::endl;
}

std::string DVTest::StringResetMode() {
  switch (reset_mode_) {
    case kDVResetOnce:
      return "Reset Once";
    case kDVResetOccasional:
      return "Reset Occasionally";
    case kDVResetStress:
      return "Reset Stress";
    default:
      return "WARNING: Unknown mode";
  }
}

std::string DVTest::StringCSRMode() {
  switch (csr_mode_) {
    case kDVCSRRandom:
      return "CSR Random";
    case kDVCSRStress:
      return "CSR Stress";
    case kDVCSRBusAccess:
      return "CSR Bus Access";
    case kDVCSRAbsCmd:
      return "CSR Abstract Command";
    default:
      return "WARNING: Unknown mode";
  }
}

std::string DVTest::StringHostMode() {
  switch (host_mode_) {
    case kDVHostIdle:
      return "Host Idle";
    case kDVHostRandom:
      return "Host Random";
    case kDVHostDelays:
      return "Host Delay";
    default:
      return "WARNING: Unknown mode";
  }
}

std::string DVTest::StringDeviceMode() {
  switch (device_mode_) {
    case kDVDeviceRandom:
      return "Device Random";
    case kDVDeviceDelays:
      return "Device Delay";
    default:
      return "WARNING: Unknown mode";
  }
}
