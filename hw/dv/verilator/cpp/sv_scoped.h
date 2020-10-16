// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_VERILATOR_CPP_SV_SCOPED_H_
#define OPENTITAN_HW_DV_VERILATOR_CPP_SV_SCOPED_H_

#include <stdexcept>
#include <string>
#include <svdpi.h>

/**
 * Wrapper and guard class for SV Scope
 *
 * Call the constructor with a string for the scope that should be used. If
 * this string starts with '.', it is taken to be a name relative to the
 * current scope. Multiple periods at the start of the string move up in the
 * tree (like Python imports).
 *
 * If the resolved scope cannot be found, the constructor leaves the current
 * scope unchanged and throws an SVScoped::Error detailing the non-existent
 * scope it tried to use.
 *
 * For example, if the current scope has name "TOP.foo.bar", then the string
 * ".baz" resolves to the scope with name "TOP.foo.bar.baz". The string "..baz"
 * resolves to the scope with name "TOP.foo.baz". The string "qux" resolves to
 * the scope with name "qux".
 *
 * This guard restores the previous scope at destruction.
 */
class SVScoped {
 public:
  SVScoped(const std::string &name);
  ~SVScoped() { svSetScope(prev_scope_); }

  class Error : public std::exception {
   public:
    Error(const std::string &scope_name);
    const char *what() const noexcept override { return msg_.c_str(); }

    std::string scope_name_;

   private:
    std::string msg_;
  };

 private:
  svScope prev_scope_;
};

#endif  // OPENTITAN_HW_DV_VERILATOR_CPP_SV_SCOPED_H_
