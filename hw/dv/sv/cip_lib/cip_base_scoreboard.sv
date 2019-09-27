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

  // predict tl error at address phase, and compare it at data phase
  bit is_tl_err_exp, is_tl_unmapped_addr;

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
    if (channel == AddrChannel) begin
      predict_tl_err(item);
    end else begin
      `DV_CHECK_EQ(item.d_error, is_tl_err_exp)
    end
  endtask

  // check if there is any error cases and set is_tl_err_exp and is_tl_unmapped_addr
  // case1: memory/register write isn't word-aligned
  // case2: memory write isn't full word
  // case3: access unmapped address
  // case4: register write size is less than actual register width
  virtual function void predict_tl_err(tl_seq_item item);
    bit            is_mem_addr;
    dv_base_reg    csr;
    uvm_reg_addr_t addr = item.a_addr % cfg.csr_addr_map_size;

    is_tl_err_exp       = 0;
    is_tl_unmapped_addr = 0;
    // case1: register write isn't word-aligned
    if (item.is_write() && addr[1:0] != 0) begin
      is_tl_err_exp = 1;
      return;
    end

    // check if it's reg or mem
    foreach (cfg.mem_addrs[i]) begin
      if (addr inside {[cfg.mem_addrs[i].start_addr : cfg.mem_addrs[i].end_addr]}) begin
        is_mem_addr = 1;
        break;
      end
    end

    if (is_mem_addr) begin // memory
      // case2: memory write isn't full word
      if (item.a_size != 2 || item.a_mask != '1) is_tl_err_exp = 1;
    end else begin // register
      // case3: access unmapped address
      if (!({addr[TL_AW-1:2], 2'b00} inside {cfg.csr_addrs})) begin
        is_tl_unmapped_addr = 1;
        if (cfg.en_devmode == 0 || cfg.devmode_vif.sample()) is_tl_err_exp = 1;
        return;
      end

      // case4: register write size is less than actual register width
      `DV_CHECK_FATAL($cast(csr, ral.default_map.get_reg_by_offset({addr[TL_AW-1:2], 2'b00})))
      if (item.is_write()) begin
        if (csr.get_msb_pos >= 24 && item.a_mask[3:0] != 'b1111 ||
            csr.get_msb_pos >= 16 && item.a_mask[2:0] != 'b111  ||
            csr.get_msb_pos >= 8  && item.a_mask[1:0] != 'b11   ||
            item.a_mask[0] != 'b1) begin
          is_tl_err_exp = 1;
        end
      end // item.is_write
    end // register
  endfunction

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
