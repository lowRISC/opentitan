// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for formal verification with Yosys. See prim_assert.sv
// for documentation for each of the macros.

`define OCAH_OT_ASSERT_I(__name, __prop)    \
  always_comb begin : __name        \
    assert (__prop);                \
  end

`define OCAH_OT_ASSERT_INIT(__name, __prop)    \
  initial begin : __name               \
    assert (__prop);                   \
  end

`define OCAH_OT_ASSERT_INIT_NET(__name, __prop) \
  initial begin : __name                \
    #1ps assert (__prop);               \
  end

// This doesn't make much sense for a formal tool (we never get to the final block!)
`define OCAH_OT_ASSERT_FINAL(__name, __prop)

// This needs sampling just before reset assertion and thus requires an event scheduler, which Yosys
// may or may not implement, so we leave it blank for the time being.
`define OCAH_OT_ASSERT_AT_RESET(__name, __prop, __rst = `OCAH_OT_ASSERT_DEFAULT_RST)

`define OCAH_OT_ASSERT_AT_RESET_AND_FINAL(__name, __prop, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
  `OCAH_OT_ASSERT_AT_RESET(AtReset_``__name``, __prop, __rst)                          \
  `OCAH_OT_ASSERT_FINAL(Final_``__name``, __prop)

`define OCAH_OT_ASSERT(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin                                                       \
    if (! (__rst !== '0)) __name: assert (__prop);                                       \
  end

`define OCAH_OT_ASSERT_NEVER(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin                                                             \
    if (! (__rst !== '0)) __name: assert (! (__prop));                                         \
  end

// Yosys uses 2-state logic, so this doesn't make sense here
`define OCAH_OT_ASSERT_KNOWN(__name, __sig, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST)

`define OCAH_OT_COVER(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin : __name                                             \
    cover ((! (__rst !== '0)) && (__prop));                                             \
  end

`define OCAH_OT_ASSUME(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST) \
  always_ff @(posedge __clk) begin                                                       \
    if (! (__rst !== '0)) __name: assume (__prop);                                       \
  end

`define OCAH_OT_ASSUME_I(__name, __prop)              \
  always_comb begin : __name                  \
    assume (__prop);                          \
  end
