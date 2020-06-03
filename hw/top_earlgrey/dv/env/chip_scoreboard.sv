// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_scoreboard extends cip_base_scoreboard #(
    .CFG_T(chip_env_cfg),
    .RAL_T(chip_reg_block),
    .COV_T(chip_env_cov)
  );
  `uvm_component_utils(chip_scoreboard)

  // local variables

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(uart_item) uart_tx_fifo;
  uvm_tlm_analysis_fifo #(uart_item) uart_rx_fifo;
  uvm_tlm_analysis_fifo #(jtag_item) jtag_fifo;

  // local queues to hold incoming packets pending comparison
  uart_item uart_tx_q[$];
  uart_item uart_rx_q[$];
  jtag_item jtag_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    uart_tx_fifo = new("uart_tx_fifo", this);
    uart_rx_fifo = new("uart_rx_fifo", this);
    jtag_fifo = new("jtag_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_jtag_fifo();
    join_none
  endtask

  virtual task process_jtag_fifo();
    jtag_item item;
    forever begin
      jtag_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received jtag item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  // TODO, may add some checking later
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    return;
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
