// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_scoreboard extends cip_base_scoreboard #(
  .CFG_T(dma_env_cfg),
  .RAL_T(dma_reg_block),
  .COV_T(dma_env_cov)
);
  `uvm_component_utils(dma_scoreboard)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create a_channel analysis fifo
    foreach (cfg.dma_a_fifo[key]) begin
      tl_a_chan_fifos[cfg.dma_a_fifo[key]] = new(cfg.dma_a_fifo[key], this);
    end
    foreach (cfg.dma_d_fifo[key]) begin
      tl_d_chan_fifos[cfg.dma_d_fifo[key]] = new(cfg.dma_d_fifo[key], this);
    end
    foreach (cfg.dma_dir_fifo[key]) begin
      tl_dir_fifos[cfg.dma_dir_fifo[key]] = new(cfg.dma_dir_fifo[key], this);
    end

  endfunction: build_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    fork
      process_host_fifo();
      process_ctn_fifo();
      process_csr_fifo();
      //process_tl_access();
    join
  endtask

  virtual task process_host_fifo();
  endtask

  virtual task process_ctn_fifo();
  endtask

  virtual task process_csr_fifo();
  endtask

  // called by cip_base::process_tl_fifo
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  endtask

endclass
