// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_scoreboard extends cip_base_scoreboard #(
  .CFG_T(dma_env_cfg),
  .RAL_T(dma_reg_block),
  .COV_T(dma_env_cov)
);
  `uvm_component_utils(dma_scoreboard)

  uvm_tlm_analysis_fifo #(tl_seq_item) dma_host_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) dma_xbar_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) csr_fifo;

  `uvm_component_new

  tl_seq_item   host_queue[$];
  tl_seq_item   xbar_queue[$];
  tl_seq_item   csr_queue[$];


  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    dma_host_fifo  = new("dma_host_fifo", this);
    dma_xbar_fifo  = new("dma_xbar_fifo", this);
    csr_fifo       = new("csr_fifo", this);
  endfunction: build_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      process_host_fifo();
      process_xbar_fifo();
      process_csr_fifo();
      //process_tl_access();
    join
  endtask

  virtual task process_host_fifo();
  endtask

  virtual task process_xbar_fifo();
  endtask

  virtual task process_csr_fifo();
  endtask

  // called by cip_base::process_tl_fifo
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  endtask

endclass
