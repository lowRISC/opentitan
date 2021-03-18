// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_DV_VERILATOR_CPP_VERILATOR_MEMUTIL_H_
#define OPENTITAN_HW_DV_VERILATOR_CPP_VERILATOR_MEMUTIL_H_

//
// A wrapper class that converts a DpiMemutil into a SimCtrlExtension
//

#include <memory>

#include "dpi_memutil.h"
#include "sim_ctrl_extension.h"

class VerilatorMemUtil : public SimCtrlExtension {
 public:
  // No-argument constructor makes a VerilatorMemUtil. Single-argument
  // constructor wraps its mem_util argument (but does not take ownership).
  VerilatorMemUtil();
  explicit VerilatorMemUtil(DpiMemUtil *mem_util);

  // Declared in SimCtrlExtension
  bool ParseCLIArguments(int argc, char **argv, bool &exit_app) override;

  // Get underlying DpiMemUtil object
  DpiMemUtil *GetUnderlying() { return mem_util_; }

  // Pass-thru function to underlying object
  void RegisterMemoryArea(const std::string &name, uint32_t base,
                          const MemArea *mem_area) {
    return mem_util_->RegisterMemoryArea(name, base, mem_area);
  }

 private:
  DpiMemUtil *mem_util_;
  std::unique_ptr<DpiMemUtil> allocation_;
};

#endif  // OPENTITAN_HW_DV_VERILATOR_CPP_VERILATOR_MEMUTIL_H_
