// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(flash_ctrl_env_cfg),
    .RAL_T(flash_ctrl_reg_block),
    .COV_T(flash_ctrl_env_cov)
  );
  `uvm_component_utils(flash_ctrl_scoreboard)

  // local variables

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item)  eflash_tl_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item)  eflash_tl_d_chan_fifo;

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    eflash_tl_a_chan_fifo = new("eflash_tl_a_chan_fifo", this);
    eflash_tl_d_chan_fifo = new("eflash_tl_d_chan_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_eflash_tl_a_chan_fifo();
      process_eflash_tl_d_chan_fifo();
    join_none
  endtask

  virtual task process_eflash_tl_a_chan_fifo();
    tl_seq_item item;
    forever begin
      eflash_tl_a_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
    end
  endtask

  virtual task process_eflash_tl_d_chan_fifo();
    tl_seq_item item;
    forever begin
      eflash_tl_d_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf("Received eflash_tl d_chan item:\n%0s", item.sprint()), UVM_HIGH)
      // check tl packet integrity
      void'(item.is_ok());
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else if (is_mem_addr(item)) begin
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

      "op_status", "status": begin
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
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
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

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, eflash_tl_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, eflash_tl_d_chan_fifo)
  endfunction

endclass
