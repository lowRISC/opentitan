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
    // if en_scb is off at the beginning, below processes aren't enabled
    // but monitor_reset in super.run_phase is always running
    wait(cfg.en_scb);
    fork
      process_tl_a_chan_fifo();
      process_tl_d_chan_fifo();
    join_none
  endtask

  virtual task process_tl_a_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_a_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      if (predict_tl_err(item, AddrChannel)) continue;
      process_tl_access(item, AddrChannel);
    end
  endtask

  virtual task process_tl_d_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_d_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf("received tl d_chan item:\n%0s", item.sprint()), UVM_HIGH)
      // check tl packet integrity
      void'(item.is_ok());
      if (predict_tl_err(item, DataChannel)) continue;
      process_tl_access(item, DataChannel);
    end
  endtask

  // task to process tl access
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endtask

  // only lsb addr is used, the other can be ignored, use this function to normalize the addr to
  // the format that RAL uses
  virtual function uvm_reg_addr_t get_normalized_addr(uvm_reg_addr_t addr);
    return ({addr[TL_AW-1:2], 2'b00} & (cfg.csr_addr_map_size - 1)) + cfg.csr_base_addr;
  endfunction

  // check if it's mem addr
  virtual function bit is_mem_addr(tl_seq_item item);
    uvm_reg_addr_t addr = get_normalized_addr(item.a_addr) - cfg.csr_base_addr;
    foreach (cfg.mem_ranges[i]) begin
      if (addr inside {[cfg.mem_ranges[i].start_addr : cfg.mem_ranges[i].end_addr]}) begin
        return 1;
      end
    end
  endfunction

  // check if there is any tl error, return 1 in case of error or if it is an unmapped addr
  // if it is data channel, will check if d_error is set correctly
  //  - access unmapped address
  //  - memory/register write addr isn't word-aligned
  //  - memory write isn't full word
  //  - register write size is less than actual register width
  //  - TL protocol violation
  virtual function bit predict_tl_err(tl_seq_item item, tl_channels_e channel);
    bit is_tl_unmapped_addr, is_tl_err;

    if (!is_tl_access_mapped_addr(item)) begin
      is_tl_unmapped_addr = 1;
      // if devmode is enabled, d_error won't be set
      if (cfg.en_devmode == 0 || cfg.devmode_vif.sample()) begin
        is_tl_err = 1;
      end
    end

    if (!is_tl_err && (!is_tl_mem_access_allowed(item) ||
        !is_tl_csr_write_addr_word_aligned(item)       ||
        !is_tl_csr_write_size_gte_csr_width(item)      ||
        item.get_exp_d_error())) begin
      is_tl_err = 1;
    end
    if ((is_tl_err || is_tl_unmapped_addr) && channel == DataChannel) begin
      `DV_CHECK_EQ(item.d_error, is_tl_err)
    end
    return (is_tl_unmapped_addr || is_tl_err);
  endfunction

  // check if address is mapped
  virtual function bit is_tl_access_mapped_addr(tl_seq_item item);
    uvm_reg_addr_t addr = get_normalized_addr(item.a_addr);
    // check if it's mem addr or reg addr
    if (is_mem_addr(item) || addr inside {cfg.csr_addrs}) return 1;
    else                                                  return 0;
  endfunction

  // check if tl mem access will trigger error or not
  virtual function bit is_tl_mem_access_allowed(tl_seq_item item);
    if (is_mem_addr(item)) begin
      // check if write isn't full word for mem that doesn't allow byte access
      if (!cfg.en_mem_byte_write && (item.a_size != 2 || item.a_mask != '1) &&
           item.a_opcode inside {tlul_pkg::PutFullData, tlul_pkg::PutPartialData}) begin
        return 0;
      end
      // check if mem read happens while mem doesn't allow read
      if (!cfg.en_mem_read && (item.a_opcode == tlul_pkg::Get)) return 0;
    end
    return 1;
  endfunction

  // check if csr write word-aligned
  virtual function bit is_tl_csr_write_addr_word_aligned(tl_seq_item item);
    if (item.is_write() && item.a_addr[1:0] != 0 && !is_mem_addr(item)) return 0;
    else                                                                return 1;
  endfunction

  // check if csr write size greater or equal to csr width
  virtual function bit is_tl_csr_write_size_gte_csr_width(tl_seq_item item);
    if (!is_tl_access_mapped_addr(item) || is_mem_addr(item)) return 1;
    if (item.is_write()) begin
      dv_base_reg    csr;
      uvm_reg_addr_t addr = get_normalized_addr(item.a_addr);
      `DV_CHECK_FATAL($cast(csr,
                            ral.default_map.get_reg_by_offset(addr)))
      if (csr.get_msb_pos >= 24 && item.a_mask[3:0] != 'b1111 ||
          csr.get_msb_pos >= 16 && item.a_mask[2:0] != 'b111  ||
          csr.get_msb_pos >= 8  && item.a_mask[1:0] != 'b11   ||
          item.a_mask[0] != 'b1) begin
        return 0;
      end
    end
    return 1;
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
