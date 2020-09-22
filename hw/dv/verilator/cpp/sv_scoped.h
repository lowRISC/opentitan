// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_VERILATOR_CPP_SV_SCOPED_H_
#define OPENTITAN_HW_DV_VERILATOR_CPP_SV_SCOPED_H_

#include <vltstd/svdpi.h>

/**
 * Guard class for SV Scope
 *
 * This guard ensures that all functions in the context where it is instantiated
 * are executed in an SVScope. It will restore the previous scope at destruction
 * and thereby make sure that the previous scope will be restored for all paths
 * that exit the scope.
 */
class SVScoped {
 private:
  svScope prev_scope_ = 0;

 public:
  SVScoped(const std::string &scopeName) : SVScoped(scopeName.c_str()) {}
  SVScoped(const char *scopeName) : SVScoped(svGetScopeFromName(scopeName)) {}
  SVScoped(svScope scope) { prev_scope_ = svSetScope(scope); }

  ~SVScoped() { svSetScope(prev_scope_); }
};

#endif  // OPENTITAN_HW_DV_VERILATOR_CPP_SV_SCOPED_H_
