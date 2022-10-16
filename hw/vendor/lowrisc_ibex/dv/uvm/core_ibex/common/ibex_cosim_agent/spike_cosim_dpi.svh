// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef SPIKE_COSIM_DPI_SVH
`define SPIKE_COSIM_DPI_SVH

import "DPI-C" function
  chandle spike_cosim_init(string isa_string,
                           bit [31:0] start_pc,
                           bit [31:0] start_mtvec,
                           string     log_file_path,
                           bit [31:0] pmp_num_regions,
                           bit [31:0] pmp_granularity,
                           bit [31:0] mhpm_counter_num,
                           bit        secure_ibex,
                           bit        icache);

import "DPI-C" function void spike_cosim_release(chandle cosim_handle);

`endif
