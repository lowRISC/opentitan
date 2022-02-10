// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_scoreboard #(
  type CFG_T = flash_ctrl_env_cfg
) extends cip_base_scoreboard #(
  .CFG_T(CFG_T),
  .RAL_T(flash_ctrl_core_reg_block),
  .COV_T(flash_ctrl_env_cov)
);
  `uvm_component_param_utils(flash_ctrl_scoreboard#(CFG_T))

  `uvm_component_new

  tl_seq_item eflash_addr_phase_queue[$];

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item) eflash_tl_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) eflash_tl_d_chan_fifo;

  // utility function to word-align an input TL address
  function bit [TL_AW-1:0] word_align_addr(bit [TL_AW-1:0] addr);
    return {addr[TL_AW-1:2], 2'b00};
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    eflash_tl_a_chan_fifo = new("eflash_tl_a_chan_fifo", this);
    eflash_tl_d_chan_fifo = new("eflash_tl_d_chan_fifo", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_eflash_tl_a_chan_fifo();
      process_eflash_tl_d_chan_fifo();
    join_none
  endtask

  // Task for receiving addr trans and storing them for later usage
  virtual task process_eflash_tl_a_chan_fifo();
    tl_seq_item item;

    forever begin
      eflash_tl_a_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf(
                "Received eflash_tl a_chan item:\n%0s", item.sprint(uvm_default_line_printer)),
                UVM_HIGH)
      // write the item into the addr queue
      eflash_addr_phase_queue.push_back(item);
      `uvm_info({`gfn, "::process_eflash_tl_a_chan_fifo()"}, $sformatf(
                "Put ADDR_PHASE transaction into eflash_item_q: %0p", item), UVM_HIGH)
    end
  endtask

  // Task for receiving data trans and checking if they matched with address trans
  virtual task process_eflash_tl_d_chan_fifo();
    tl_seq_item item;
    tl_seq_item addr_item;

    bit addr_trans_available = 0;

    forever begin
      eflash_tl_d_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf(
                "Received eflash_tl d_chan item:\n%0s", item.sprint(uvm_default_line_printer)),
                UVM_HIGH)
      // check tl packet integrity
      void'(item.is_ok());

      // check that address phase for this read is done
      `DV_CHECK_GT_FATAL(eflash_addr_phase_queue.size(), 0)
      addr_item = eflash_addr_phase_queue.pop_front();

      `DV_CHECK_EQ(word_align_addr(item.a_addr), word_align_addr(addr_item.a_addr))
      `DV_CHECK_EQ(item.a_source, addr_item.a_source)
      if (cfg.block_host_rd) begin  // blocking reads are checked with backdoor reads
        check_trans(item);
      end else begin  // non blocking reads are pushed to the queue and in test checked
        cfg.flash_rd_data.push_back(item.d_data);
      end
    end
  endtask

  // the TLUL response data are compared to the backdoor-read data using the bit-mask.
  virtual function void check_trans(ref tl_seq_item trans);
    flash_op_t             flash_read;
    logic      [TL_DW-1:0] exp_data   [$];
    // Flash read trans

    flash_read.partition  = FlashPartData;
    flash_read.erase_type = FlashErasePage;
    flash_read.op         = flash_ctrl_pkg::FlashOpRead;
    flash_read.num_words  = 1;
    flash_read.addr       = trans.a_addr;

    //comparing backdoor read data and direct read data
    cfg.flash_mem_bkdr_read(flash_read, exp_data);
    `DV_CHECK_EQ(exp_data[0], trans.d_data)
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else if (is_mem_addr(item, ral_name)) begin
      // TODO: check if rd_fifo and prog_fifo can be implemented as CSRs rather than windows.
      return;
    end

    // if incoming access is a write to a valid csr, then make updates right away.
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // Skip read check on intr_state CSR, since it is WO.
        do_read_check = 1'b0;
      end

      "intr_enable": begin
      end

      "intr_test": begin
      end

      "op_status", "status", "erase_suspend": begin
        // TODO: FIXME
        do_read_check = 1'b0;
      end

      default: begin
        // TODO: uncomment when all CSRs are specified
        // `uvm_fatal(`gfn, $sformatf("CSR access not processed: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf(
                     "reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    eflash_tl_a_chan_fifo.flush();
    eflash_tl_d_chan_fifo.flush();
  endfunction

  virtual function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, eflash_tl_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, eflash_tl_d_chan_fifo)
    `DV_CHECK_EQ(eflash_addr_phase_queue.size, 0)
  endfunction

endclass
