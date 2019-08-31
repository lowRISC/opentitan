// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_scoreboard #(type RAL_T = dv_base_reg_block,
                            type CFG_T = cip_base_env_cfg,
                            type COV_T = cip_base_env_cov)
                            extends dv_base_scoreboard #(RAL_T, CFG_T, COV_T);
  `uvm_component_param_utils(cip_base_scoreboard #(RAL_T, CFG_T, COV_T))

  // TLM fifos to pick up the packets
  uvm_tlm_analysis_fifo #(tl_seq_item)  tl_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item)  tl_d_chan_fifo;

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    tl_a_chan_fifo = new("tl_a_chan_fifo", this);
    tl_d_chan_fifo = new("tl_d_chan_fifo", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_tl_a_chan_fifo();
      process_tl_d_chan_fifo();
    join_none
  endtask

  virtual task process_tl_a_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_a_chan_fifo.get(item);
      // do nothing; we are using d_chan_fifo items for completed transactions
      process_tl_access(item, AddrChannel);
    end
  endtask

  virtual task process_tl_d_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_d_chan_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received tl d_chan item:\n%0s", item.sprint()), UVM_HIGH)
      // check tl packet integrity
      void'(item.is_ok());
      process_tl_access(item, DataChannel);
    end
  endtask

  // task to process tl access
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask

  virtual function void reset(string kind = "HARD");
    tl_a_chan_fifo.flush();
    tl_d_chan_fifo.flush();
  endfunction

  virtual function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, tl_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, tl_d_chan_fifo)
  endfunction

endclass
