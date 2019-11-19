// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_agent_cov extends dv_base_agent_cov #(uart_agent_cfg);
  `uvm_component_utils(uart_agent_cov)

  covergroup uart_cg with function sample(uart_dir_e dir, uart_item item);
    cp_dir:        coverpoint dir;
    cp_data:       coverpoint item.data;
    cp_en_parity:  coverpoint cfg.en_parity;
    cp_odd_parity: coverpoint cfg.odd_parity;
    cp_baud_rate:  coverpoint cfg.baud_rate;
    cross cp_dir, cp_data, cp_en_parity, cp_odd_parity, cp_baud_rate;
  endgroup

  // sample reset at every bit location in both direction
  covergroup uart_reset_cg with function sample(uart_dir_e dir, int bit_position);
    cp_dir:        coverpoint dir;
    cp_rst_pos:    coverpoint bit_position {
      // including parity, totally NUM_BIT_START_DATA_STOP+1 bits
      bins values[]  = {[0:NUM_UART_XFER_BITS_WO_PARITY]};
    }
    cross cp_dir, cp_rst_pos;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    uart_cg       = new();
    uart_reset_cg = new();
  endfunction : new

endclass
