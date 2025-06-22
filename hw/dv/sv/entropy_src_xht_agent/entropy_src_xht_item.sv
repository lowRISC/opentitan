// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_xht_item extends uvm_sequence_item;

  localparam int RngBusWidth = `RNG_BUS_WIDTH;
  localparam int RngBusBitSelWidth = prim_util_pkg::vbits(RngBusWidth);

  logic                            entropy_valid;
  logic [RngBusWidth-1:0]          entropy_bits;
  logic [RngBusBitSelWidth-1:0]    entropy_bit_sel;
  logic [16+RngBusBitSelWidth-1:0] health_test_window;

  entropy_src_xht_meta_req_t req;
  entropy_src_xht_meta_rsp_t rsp;

  `uvm_object_utils(entropy_src_xht_item)
  `uvm_object_new

endclass
