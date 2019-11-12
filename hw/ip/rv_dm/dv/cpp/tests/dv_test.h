// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef DV_TEST_H_
#define DV_TEST_H_

#include <string>

// Reset config:
// kDVResetOnce        - Apply reset once at start of test
// kDVResetOccasional  - Apply very occasional resets during test
// kDVResetStress      - Apply frequent resets
enum DVTestResetMode : int { kDVResetOnce, kDVResetOccasional, kDVResetStress };

// CSR access config
// - kDVCSRRandom    - Access all CSRs with equal probability
// - kDVCSRStress    - Repeatedly access the same CSRs
// - kDVCSRBusAccess - Focus CSR accesses on generating TLUL host activity
// - kDVCSRAbsCmd    - Focus CSR accesses on abstract command activity
enum DVCSRMode : int {
  kDVCSRRandom,
  kDVCSRStress,
  kDVCSRBusAccess,
  kDVCSRAbsCmd
};

// TLUL Host config
// - kDVHostIdle   - Do not initiate any TLUL host accesses
// - kDVHostRandom - Randomly initiate TLUL host accesses
// - kDVHostDelays - Apply long delays to host accesses
enum DVHostMode : int { kDVHostIdle, kDVHostRandom, kDVHostDelays };

// TLUL Device config
// - kDVDeviceRandom - Respond to TLUL device accesses randomly
// - kDVDeviceDelays - Apply long delays to device responses
enum DVDeviceMode : int { kDVDeviceRandom, kDVDeviceDelays };

class DVTest {
 public:
  /**
   * Constructor assigns default values for all config params
   */
  DVTest();

  /**
   * Read a config file and set params from it
   *
   * @param config_file Name of config file to parse
   *
   * return Success / Fail for parsing of test file
   */
  bool ReadTestConfig(std::string config_file);

  /**
   * Getter for reset_mode config
   */
  DVTestResetMode GetResetMode();

  /**
   * Getter for csr_mode config
   */
  DVCSRMode GetCSRMode();

  /**
   * Print all config options
   */
  void PrintConfig();

 private:
  /**
   * Pretty print helper functions
   */
  std::string StringResetMode();
  std::string StringCSRMode();
  std::string StringHostMode();
  std::string StringDeviceMode();

  DVTestResetMode reset_mode_;
  DVCSRMode csr_mode_;
  DVHostMode host_mode_;
  DVDeviceMode device_mode_;
};

#endif  // DV_TEST_H_
