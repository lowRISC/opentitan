// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package reg_dpi;

  import "DPI-C"
  function void monitor_tick (
    input  string     name,
    input  bit        rst_n,
    input  bit        illegal_csr,
    input  bit        csr_access,
    input  bit [1:0]  csr_op,
    input  bit        csr_op_en,
    input  bit [11:0] csr_addr,
    input  bit [31:0] csr_wdata,
    input  bit [31:0] csr_rdata);

  import "DPI-C"
  function void driver_tick (
    input  string     name,
    output bit        csr_access,
    output bit [1:0]  csr_op,
    output bit        csr_op_en,
    output bit [11:0] csr_addr,
    output bit [31:0] csr_wdata);

endpackage

