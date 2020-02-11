// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions

`ifndef PRIM_ASSERT_SV
`define PRIM_ASSERT_SV

`ifdef UVM
  // report assertion error with UVM if compiled
  package assert_rpt_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    function void assert_rpt(string msg);
      `uvm_error("ASSERT FAILED", msg)
    endfunction
  endpackage
`endif

///////////////////
// Helper macros //
///////////////////

// local helper macro to reduce code clutter. undefined at the end of this file
`ifndef VERILATOR
`ifndef SYNTHESIS
`define INC_ASSERT
`endif
`endif

// Converts an arbitrary block of code into a Verilog string
`define PRIM_STRINGIFY(__x) `"__x`"

  // ASSERT_RPT is available to change the reporting mechanism when an assert fails
`define ASSERT_RPT(__name, __msg)                                         \
`ifdef UVM                                                                \
  assert_rpt_pkg::assert_rpt($sformatf("[%m] %s: %s (%s:%0d)",            \
                             __name, __msg, `__FILE__, `__LINE__));       \
`else                                                                     \
  $error("[ASSERT FAILED] [%m] %s: %s", __name, __msg);                   \
`endif

///////////////////////////////////////
// Simple assertion and cover macros //
///////////////////////////////////////

// Default clk and reset signals used by assertion macros below.
`define ASSERT_DEFAULT_CLK clk_i
`define ASSERT_DEFAULT_RST !rst_ni

// Immediate assertion
// Note that immediate assertions are sensitive to simulation glitches.
`define ASSERT_I(__name, __prop)                                       \
`ifdef INC_ASSERT                                                      \
  __name: assert (__prop)                                              \
    else `ASSERT_RPT(`PRIM_STRINGIFY(__name), `PRIM_STRINGIFY(__prop)) \
`endif

// Assertion in initial block. Can be used for things like parameter checking.
`define ASSERT_INIT(__name, __prop)                                      \
`ifdef INC_ASSERT                                                        \
  initial                                                                \
    __name: assert (__prop)                                              \
      else `ASSERT_RPT(`PRIM_STRINGIFY(__name), `PRIM_STRINGIFY(__prop)) \
`endif

// Assertion in final block. Can be used for things like queues being empty
// at end of sim, all credits returned at end of sim, state machines in idle
// at end of sim.
`define ASSERT_FINAL(__name, __prop)                                         \
`ifdef INC_ASSERT                                                            \
  final                                                                      \
    __name: assert (__prop || $test$plusargs("disable_assert_final_checks")) \
      else `ASSERT_RPT(`PRIM_STRINGIFY(__name), `PRIM_STRINGIFY(__prop))     \
`endif

// Assert a concurrent property directly.
// It can be called as a module (or interface) body item.
`define ASSERT(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef INC_ASSERT                                                                        \
  __name: assert property (@(posedge __clk) disable iff (__rst !== '0) (__prop))         \
    else `ASSERT_RPT(`PRIM_STRINGIFY(__name), `PRIM_STRINGIFY(__prop))                   \
`endif
// Note: Above we use (__rst !== '0) in the disable iff statements instead of
// (__rst == '1).  This properly disables the assertion in cases when reset is X at
// the beginning of a simulation. For that case, (reset == '1) does not disable the
// assertion.

// Assert a concurrent property NEVER happens
`define ASSERT_NEVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef INC_ASSERT                                                                              \
  __name: assert property (@(posedge __clk) disable iff (__rst !== '0) not (__prop))           \
    else `ASSERT_RPT(`PRIM_STRINGIFY(__name), `PRIM_STRINGIFY(__prop))                         \
`endif

// Assert that signal has a known value (each bit is either '0' or '1') after reset.
// It can be called as a module (or interface) body item.
`define ASSERT_KNOWN(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef INC_ASSERT                                                                             \
  `ASSERT(__name, !$isunknown(__sig), __clk, __rst)                                           \
`endif

//  Cover a concurrent property
`define COVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef INC_ASSERT                                                                       \
  __name: cover property (@(posedge __clk) disable iff (__rst !== '0) (__prop));        \
`endif

//////////////////////////////
// Complex assertion macros //
//////////////////////////////

// Assert that signal is an active-high pulse with pulse length of 1 clock cycle
`define ASSERT_PULSE(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef INC_ASSERT                                                                             \
  `ASSERT(__name, $rose(__sig) |=> !(__sig), __clk, __rst)                                    \
`endif

// Assert that valid is known after reset and data is known when valid == 1
`define ASSERT_VALID_DATA(__name, __valid, __dat, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef INC_ASSERT                                                                                           \
  `ASSERT_KNOWN(__name``KnownValid, __valid, __clk, __rst)                                                  \
  `ASSERT_NEVER(__name``KnownData, (__valid) && $isunknown(__dat), __clk, __rst)                            \
`endif

// Same as ASSERT_VALID_DATA, but also assert that ready is known after reset
`define ASSERT_VALID_READY_DATA(__name, __valid, __ready, __dat, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef INC_ASSERT                                                                                                          \
  `ASSERT_KNOWN(__name``KnownValid, __valid, __clk, __rst)                                                                 \
  `ASSERT_KNOWN(__name``KnownReady, __ready, __clk, __rst)                                                                 \
  `ASSERT_NEVER(__name``KnownData, (__valid) && $isunknown(__dat), __clk, __rst)                                           \
`endif

///////////////////////
// Assumption macros //
///////////////////////

// Assume a concurrent property
`define ASSUME(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef INC_ASSERT                                                                        \
  __name: assume property (@(posedge __clk) disable iff (__rst !== '0) (__prop))         \
     else begin `ASSERT_RPT(`PRIM_STRINGIFY(__name), `PRIM_STRINGIFY(__prop)) end        \
`endif

// Assume an immediate property
`define ASSUME_I(__name, __prop)                                       \
`ifdef INC_ASSERT                                                      \
  __name: assume (__prop)                                              \
    else `ASSERT_RPT(`PRIM_STRINGIFY(__name), `PRIM_STRINGIFY(__prop)) \
`endif

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
`define ASSUME_I_FPV(__name, __prop)             \
`ifdef FPV_ON                                    \
   `ASSUME_I(__name, __prop)                     \
`endif

// COVER_FPV
// Cover a concurrent property during formal verification
`define COVER_FPV(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
`ifdef FPV_ON                                                                               \
   `COVER(__name, __prop, __clk, __rst)                                                     \
`endif

`endif // PRIM_ASSERT_SV
