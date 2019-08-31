// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_scoreboard extends dv_base_scoreboard #(
    .CFG_T(rv_dm_env_cfg),
    .RAL_T(rv_dm_reg_block),
    .COV_T(rv_dm_env_cov)
  );
  `uvm_component_utils(rv_dm_scoreboard)

  // local variables

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(jtag_item) jtag_fifo;

  uvm_tlm_analysis_fifo #(tl_seq_item)  tl_host_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item)  tl_host_d_chan_fifo;

  uvm_tlm_analysis_fifo #(tl_seq_item)  tl_device_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item)  tl_device_d_chan_fifo;

  // local queues to hold incoming packets pending comparison
  jtag_item     jtag_q[$];
  tl_seq_item   tl_host_q[$];
  tl_seq_item   tl_device_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    jtag_fifo = new("jtag_fifo", this);
    tl_host_a_chan_fifo = new("tl_host_a_chan_fifo", this);
    tl_host_d_chan_fifo = new("tl_host_d_chan_fifo", this);
    tl_device_a_chan_fifo = new("tl_device_a_chan_fifo", this);
    tl_device_d_chan_fifo = new("tl_device_d_chan_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_jtag_fifo();
      process_tl_host_a_chan_fifo();
      process_tl_host_d_chan_fifo();
      process_tl_device_a_chan_fifo();
      process_tl_device_d_chan_fifo();
    join_none
  endtask

  virtual task process_jtag_fifo();
    jtag_item item;
    forever begin
      jtag_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received jtag item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  virtual task process_tl_host_a_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_host_a_chan_fifo.get(item);
      process_tl_host_access(item, AddrChannel);
    end
  endtask

  virtual task process_tl_host_d_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_host_d_chan_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received tl host d_chan item:\n%0s", item.sprint()), UVM_HIGH)
      // check tl packet integrity
      void'(item.is_ok());
      process_tl_host_access(item, DataChannel);
    end
  endtask

  virtual task process_tl_device_a_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_device_a_chan_fifo.get(item);
      process_tl_device_access(item, AddrChannel);
    end
  endtask

  virtual task process_tl_device_d_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_device_d_chan_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received tl device d_chan item:\n%0s", item.sprint()), UVM_HIGH)
      // check tl packet integrity
      void'(item.is_ok());
      process_tl_device_access(item, DataChannel);
    end
  endtask

  // task to process tl access
  virtual task process_tl_host_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask

  // task to process tl access
  virtual task process_tl_device_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask

  virtual function void reset(string kind = "HARD");
    tl_host_a_chan_fifo.flush();
    tl_host_d_chan_fifo.flush();
    tl_device_a_chan_fifo.flush();
    tl_device_d_chan_fifo.flush();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
