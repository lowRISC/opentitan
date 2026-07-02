// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macro bodies included by prim_assert.sv for tools that don't support assertions. See
// prim_assert.sv for documentation for each of the macros.

`define OCAH_OT_ASSERT_I(__name, __prop)
`define OCAH_OT_ASSERT_INIT(__name, __prop)
`define OCAH_OT_ASSERT_INIT_NET(__name, __prop)
`define OCAH_OT_ASSERT_FINAL(__name, __prop)
`define OCAH_OT_ASSERT_AT_RESET(__name, __prop, __rst = `OCAH_OT_ASSERT_DEFAULT_RST)
`define OCAH_OT_ASSERT_AT_RESET_AND_FINAL(__name, __prop, __rst = `OCAH_OT_ASSERT_DEFAULT_RST)
`define OCAH_OT_ASSERT(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST)
`define OCAH_OT_ASSERT_NEVER(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST)
`define OCAH_OT_ASSERT_KNOWN(__name, __sig, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST)
`define OCAH_OT_COVER(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST)
`define OCAH_OT_ASSUME(__name, __prop, __clk = `OCAH_OT_ASSERT_DEFAULT_CLK, __rst = `OCAH_OT_ASSERT_DEFAULT_RST)
`define OCAH_OT_ASSUME_I(__name, __prop)
