// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for tools that support full SystemVerilog and SVA syntax.
// See prim_assert.sv for documentation for each of the macros.

// ASSERT_RPT is available to change the reporting mechanism when an assert fails
`define ASSERT_RPT(__name)                                                  \
`ifdef UVM                                                                  \
  assert_rpt_pkg::assert_rpt($sformatf("[%m] %s (%s:%0d)",                  \
                             __name, `__FILE__, `__LINE__));                \
`else                                                                       \
  $error("[ASSERT FAILED] [%m] %s (%s:%0d)", __name, `__FILE__, `__LINE__); \
`endif

`define ASSERT_I(__name, __prop)           \
  __name: assert (__prop)                  \
    else begin                             \
      `ASSERT_RPT(`PRIM_STRINGIFY(__name)) \
    end

`define ASSERT_INIT(__name, __prop)          \
  initial begin                              \
    __name: assert (__prop)                  \
      else begin                             \
        `ASSERT_RPT(`PRIM_STRINGIFY(__name)) \
      end                                    \
  end

`define ASSERT_FINAL(__name, __prop)                                         \
  final begin                                                                \
    __name: assert (__prop || $test$plusargs("disable_assert_final_checks")) \
      else begin                                                             \
        `ASSERT_RPT(`PRIM_STRINGIFY(__name))                                 \
      end                                                                    \
  end

`define ASSERT(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))       \
    else begin                                                                           \
      `ASSERT_RPT(`PRIM_STRINGIFY(__name))                                               \
    end

`define ASSERT_NEVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  __name: assert property (@(posedge __clk) disable iff ((__rst) !== '0) not (__prop))         \
    else begin                                                                                 \
      `ASSERT_RPT(`PRIM_STRINGIFY(__name))                                                     \
    end

`define ASSERT_KNOWN(__name, __sig, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  `ASSERT(__name, !$isunknown(__sig), __clk, __rst)

`define COVER(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  __name: cover property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop));

`define ASSUME(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST) \
  __name: assume property (@(posedge __clk) disable iff ((__rst) !== '0) (__prop))       \
    else begin                                                                           \
      `ASSERT_RPT(`PRIM_STRINGIFY(__name))                                               \
    end

`define ASSUME_I(__name, __prop)           \
  __name: assume (__prop)                  \
    else begin                             \
      `ASSERT_RPT(`PRIM_STRINGIFY(__name)) \
    end
