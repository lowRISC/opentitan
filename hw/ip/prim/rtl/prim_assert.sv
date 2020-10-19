// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

///////////////////
// Helper macros //
///////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

// ASSERT_ERROR logs an error message with either `uvm_error or with $error.
//
// This somewhat duplicates `DV_ERROR macro defined in hw/dv/sv/dv_utils/dv_macros.svh. The reason
// for redefining it here is to avoid creating a dependency.
`define ASSERT_ERROR(__name)                                                             \
`ifdef UVM                                                                               \
  uvm_pkg::uvm_report_error("ASSERT FAILED", `PRIM_STRINGIFY(__name), uvm_pkg::UVM_NONE, \
                            `__FILE__, `__LINE__, "", 1);                                \
`else                                                                                    \
  $error("%0t: (%0s:%0d) [%m] [ASSERT FAILED] %0s", $time, `__FILE__, `__LINE__,         \
         `PRIM_STRINGIFY(__name));                                                       \
`endif

// The basic helper macros are actually defined in "implementation headers". The macros should do
// the same thing in each case (except for the dummy flavour), but in a way that the respective
// tools support.
//
// If the tool supports assertions in some form, we also define INC_ASSERT (which can be used to
// hide signal definitions that are only used for assertions).
//
// The list of basic macros supported is:
//
//  ASSERT_I:     Immediate assertion. Note that immediate assertions are sensitive to simulation
//                glitches.
//
//  ASSERT_INIT:  Assertion in initial block. Can be used for things like parameter checking.
//
//  ASSERT_FINAL: Assertion in final block. Can be used for things like queues being empty at end of
//                sim, all credits returned at end of sim, state machines in idle at end of sim.
//
//  ASSERT:       Assert a concurrent property directly. It can be called as a module (or
//                interface) body item.
//
//                Note: We use (__rst !== '0) in the disable iff statements instead of (__rst ==
//                '1). This properly disables the assertion in cases when reset is X at the
//                beginning of a simulation. For that case, (reset == '1) does not disable the
//                assertion.
//
//  ASSERT_NEVER: Assert a concurrent property NEVER happens
//
//  ASSERT_KNOWN: Assert that signal has a known value (each bit is either '0' or '1') after reset.
//                It can be called as a module (or interface) body item.
//
//  COVER:        Cover a concurrent property
//
//  ASSUME:       Assume a concurrent property
//
//  ASSUME_I:     Assume an immediate property

`ifdef VERILATOR
 `include "prim_assert_dummy_macros.svh"
`elsif SYNTHESIS
 `include "prim_assert_dummy_macros.svh"
`elsif YOSYS
 `include "prim_assert_yosys_macros.svh"
 `define INC_ASSERT
`else
 `include "prim_assert_standard_macros.svh"
 `define INC_ASSERT
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)

// Assert that a property is true only when an enable signal is set.  It can be called as a module
// (or interface) body item.
`define ASSERT_IF(__name, __prop, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, (__enable) |-> (__prop), __clk, __rst)

// Assert that signal has a known value (each bit is either '0' or '1') after reset if enable is
// set.  It can be called as a module (or interface) body item.
`define ASSERT_KNOWN_IF(__name, __sig, __enable, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT_KNOWN(__name``KnownEnable, __enable, __clk, __rst)                                               \
  `ASSERT_IF(__name, !$isunknown(__sig), __enable, __clk, __rst)

//////////////////////////////////
// For formal verification only //
//////////////////////////////////

// Note that the existing set of ASSERT macros specified above shall be used for FPV,
// thereby ensuring that the assertions are evaluated during DV simulations as well.

// ASSUME_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                                \
   `ASSUME(__name, __prop, __clk, __rst)                                                     \
`endif

// ASSUME_I_FPV
// Assume a concurrent property during formal verification only.
`define ASSUME_I_FPV(__name, __prop) \
`ifdef FPV_ON                        \
   `ASSUME_I(__name, __prop)         \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV
