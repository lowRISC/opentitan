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

  function new(string name, uvm_component parent);
    super.new(name, parent);
    uart_cg = new();
  endfunction : new

endclass
