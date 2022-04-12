// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <numeric>
#include <sstream>
#include <string>
#include <vector>

#include <svdpi.h>

extern "C" {
extern unsigned long long mhpmcounter_get(int index);
}

#include "ibex_pcounts.h"

// see mhpmcounter_incr signals in rtl/ibex_cs_registers.sv for details

const std::vector<std::string> ibex_counter_names = {
    "Cycles",
    "NONE",
    "Instructions Retired",
    "LSU Busy",
    "Fetch Wait",
    "Loads",
    "Stores",
    "Jumps",
    "Conditional Branches",
    "Taken Conditional Branches",
    "Compressed Instructions",
    "Multiply Wait",
    "Divide Wait"};

std::string ibex_pcount_string(bool csv) {
  char seperator = csv ? ',' : ':';
  std::string::size_type longest_name_length;

  if (!csv) {
    longest_name_length = 0;
    for (const std::string &counter_name : ibex_counter_names) {
      longest_name_length = std::max(longest_name_length, counter_name.length());
    }

    // Add 1 to always get at least once space after the seperator
    longest_name_length++;
  }

  std::stringstream pcount_ss;

  for (int i = 0; i < ibex_counter_names.size(); ++i) {
    pcount_ss << ibex_counter_names[i] << seperator;

    if (!csv) {
      int padding = longest_name_length - ibex_counter_names[i].length();

      for (int j = 0; j < padding; ++j)
        pcount_ss << ' ';
    }

    pcount_ss << mhpmcounter_get(i) << std::endl;
  }

  return pcount_ss.str();
}
