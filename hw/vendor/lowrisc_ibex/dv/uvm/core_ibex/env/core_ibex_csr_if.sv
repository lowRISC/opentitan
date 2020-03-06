// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to probe CSR accesses
interface core_ibex_csr_if(input logic clk);
  logic                     csr_access;
  ibex_pkg::csr_num_e       csr_addr;
  logic [31:0]              csr_wdata;
  logic [31:0]              csr_rdata;
  ibex_pkg::csr_op_e        csr_op;
endinterface
