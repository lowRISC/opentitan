// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_seq_agent_cfg extends dv_base_agent_cfg;

  // indicate if these fifo and ports exist or not
  bit         has_req_fifo = 1'b0;
  bit         has_rsp_fifo = 1'b0;

  // use for phase_ready_to_end to add additional delay after ok_to_end is set
  int ok_to_end_delay_ns = 1000;

  `uvm_object_utils_begin(dv_seq_agent_cfg)
    `uvm_field_int (has_req_fifo,         UVM_DEFAULT)
    `uvm_field_int (has_rsp_fifo,         UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
