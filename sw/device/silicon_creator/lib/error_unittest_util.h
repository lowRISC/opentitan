// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_ERROR_UNITTEST_UTIL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_ERROR_UNITTEST_UTIL_H_

#include <iostream>
#include <map>
#include <ostream>
#include <stdint.h>
#include <string>

#include "sw/device/silicon_creator/lib/error.h"

const inline std::map<std::string, uint32_t> &GetErrorMap() {
#define STRINGIFY(x) #x
#define ERROR_MAP_INIT(name, value) \
  { STRINGIFY(name), value }
  static std::map<std::string, uint32_t> errors = {
      DEFINE_ERRORS(ERROR_MAP_INIT),
  };
  return errors;
#undef ERROR_MAP_INIT
#undef STRINGIFY
}

const inline std::map<uint32_t, std::string> &GetErrorToStringMap() {
#define STRINGIFY(x) #x
#define ERROR_MAP_INIT(name, value) \
  { value, STRINGIFY(name) }
  static std::map<uint32_t, std::string> errors = {
      DEFINE_ERRORS(ERROR_MAP_INIT),
  };
  return errors;
#undef ERROR_MAP_INIT
#undef STRINGIFY
}

/**
 * A custom printer for `rom_error_t` in unit tests.
 */
void inline PrintTo(const rom_error_t &err, std::ostream *os) {
  const std::map<uint32_t, std::string> &error_to_string_map =
      GetErrorToStringMap();
  // Print the symbolic name if it is known.
  if (error_to_string_map.count(err)) {
    *os << error_to_string_map.at(err);
  } else {
    *os << "Unrecognized rom_error_t value";
  }
  *os << " (0x" << std::hex << err << ")";
}

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_ERROR_UNITTEST_UTIL_H_
