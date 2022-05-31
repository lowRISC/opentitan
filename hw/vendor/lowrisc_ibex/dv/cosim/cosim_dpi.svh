// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// DPI interface to co-simulation model, see `cosim.h` for the interface description.

// Implemented as a header file as VCS needs `import` declarations included in each verilog file
// that uses them.

`ifndef COSIM_DPI_SVH
`define COSIM_DPI_SVH

import "DPI-C" function int riscv_cosim_step(chandle cosim_handle, bit [4:0] write_reg,
  bit [31:0] write_reg_data, bit [31:0] pc, bit sync_trap);
import "DPI-C" function void riscv_cosim_set_mip(chandle cosim_handle, bit [31:0] mip);
import "DPI-C" function void riscv_cosim_set_nmi(chandle cosim_handle, bit nmi);
import "DPI-C" function void riscv_cosim_set_debug_req(chandle cosim_handle, bit debug_req);
import "DPI-C" function void riscv_cosim_set_mcycle(chandle cosim_handle, bit [63:0] mcycle);
import "DPI-C" function void riscv_cosim_notify_dside_access(chandle cosim_handle, bit store,
  bit [31:0] addr, bit [31:0] data, bit [3:0] be, bit error, bit misaligned_first,
  bit misaligned_second);
import "DPI-C" function int riscv_cosim_set_iside_error(chandle cosim_handle, bit [31:0] addr);
import "DPI-C" function int riscv_cosim_get_num_errors(chandle cosim_handle);
import "DPI-C" function string riscv_cosim_get_error(chandle cosim_handle, int index);
import "DPI-C" function void riscv_cosim_clear_errors(chandle cosim_handle);
import "DPI-C" function void riscv_cosim_write_mem_byte(chandle cosim_handle, bit [31:0] addr,
  bit [7:0] d);
import "DPI-C" function int riscv_cosim_get_insn_cnt(chandle cosim_handle);

`endif
