// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <numeric>
#include <sstream>
#include <string>
#include <vector>

#include <svdpi.h>

extern "C" {
extern unsigned int mhpmcounter_num();
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

static bool has_hpm_counter(int index) {
  // The "cycles" and "instructions retired" counters are special and always
  // exist.
  if (index == 0 || index == 2)
    return true;

  // The "NONE" counter is a placeholder. The space reserves an index that was
  // once the "MTIME" CSR, but now is unused. Return false: there's no real HPM
  // counter at index 1.
  if (index == 1)
    return false;

  // Otherwise, a counter exists if the index is strictly less than
  // the MHPMCounterNum parameter that got passed to the
  // ibex_cs_registers module.
  return index < mhpmcounter_num();
}

std::string ibex_pcount_string(bool csv) {
  char separator = csv ? ',' : ':';
  std::string::size_type longest_name_length;

  if (!csv) {
    longest_name_length = 0;
    for (int i = 0; i < ibex_counter_names.size(); ++i) {
      if (has_hpm_counter(i)) {
        longest_name_length =
            std::max(longest_name_length, ibex_counter_names[i].length());
      }
    }

    // Add 1 to always get at least once space after the separator
    longest_name_length++;
  }

  std::stringstream pcount_ss;

  for (int i = 0; i < ibex_counter_names.size(); ++i) {
    if (!has_hpm_counter(i))
      continue;

    pcount_ss << ibex_counter_names[i] << separator;

    if (!csv) {
      int padding = longest_name_length - ibex_counter_names[i].length();

      for (int j = 0; j < padding; ++j)
        pcount_ss << ' ';
    }

    pcount_ss << mhpmcounter_get(i) << std::endl;
  }

  return pcount_ss.str();
}
