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

  typedef struct {
    // TLUL address for read operation
    bit [TL_AW-1:0] addr;

    // Read response data
    bit [TL_DW-1:0] data;

    // Source
    bit [TL_AIW-1:0] source;

  } flash_trans_t;

  // mailbox for addr and data phase
  mailbox #(flash_trans_t) addr_phase_mbox;
  mailbox #(flash_trans_t) data_phase_mbox;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item) eflash_tl_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) eflash_tl_d_chan_fifo;

  // utility function to word-align an input TL address
  function bit [TL_AW-1:0] word_align_addr(bit [TL_AW-1:0] addr);
    return {addr[TL_AW-1:2], 2'b00};
  endfunction

  // function for comparing addr and data transaction
  function bit eq_trans(flash_trans_t t1, flash_trans_t t2);
    bit equal = (t1.addr == t2.addr) && (t1.source == t2.source);
    `uvm_info(`gfn, $sformatf("Comparing 2 transactions:\nt1: %0p\nt2: %0p", t1, t2), UVM_HIGH)
    return equal;
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    eflash_tl_a_chan_fifo = new("eflash_tl_a_chan_fifo", this);
    eflash_tl_d_chan_fifo = new("eflash_tl_d_chan_fifo", this);
    addr_phase_mbox = new();
    data_phase_mbox = new();
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_eflash_tl_a_chan_fifo();
      process_eflash_tl_d_chan_fifo();
      process_completed_trans();
    join_none
  endtask

  // Task for receiving addr trans and storing them for later usage
  virtual task process_eflash_tl_a_chan_fifo();
    tl_seq_item   item;
    flash_trans_t addr_trans;

    forever begin
      eflash_tl_a_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf("Received eflash_tl a_chan item:\n%0s", item.sprint()), UVM_HIGH)
      addr_trans.addr   = word_align_addr(item.a_addr);
      addr_trans.source = item.a_source;
      // write the addr_trans into the mailbox
      addr_phase_mbox.put(addr_trans);
      `uvm_info({`gfn, "::process_eflash_tl_a_chan_fifo()"}, $sformatf(
                "Put ADDR_PHASE transaction into addr_phase_mbox: %0p", addr_trans), UVM_HIGH)
    end
  endtask

  // Task for receiving data trans and checking if they matched with address trans
  virtual task process_eflash_tl_d_chan_fifo();
    tl_seq_item item;
    flash_trans_t addr_trans;
    flash_trans_t data_trans;

    bit addr_trans_available = 0;

    forever begin
      eflash_tl_d_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf("Received eflash_tl d_chan item:\n%0s", item.sprint()), UVM_HIGH)
      // check tl packet integrity
      void'(item.is_ok());
      // check that address phase for this read is done
      addr_trans_available = (addr_phase_mbox.try_get(addr_trans) > 0);
      `DV_CHECK_NE(addr_trans_available, 0,
                   "AddrPhase transaction not available in addr_phase_mbox")
      data_trans.addr   = word_align_addr(item.a_addr);
      data_trans.source = item.d_source;
      `DV_CHECK_EQ(eq_trans(addr_trans, data_trans), 1)
      data_trans.data = item.d_data;
      // write data_trans into the mailbox which will be later checked with bcd
      data_phase_mbox.put(data_trans);
      `uvm_info({`gfn, "::process_eflash_tl_d_chan_fifo()"}, $sformatf(
                "Put DATA_PHASE transaction into data_phase_mbox: %0p", data_trans), UVM_HIGH)
    end
  endtask

  // compare received DATA transactionts with backdoor read transactions
  virtual task process_completed_trans();
    flash_trans_t trans;

    forever begin
      data_phase_mbox.get(trans);
      `uvm_info({`gfn, "::process_completed_trans()"}, $sformatf(
                "Checking Flash read transaction: %0p", trans), UVM_MEDIUM)
      if (cfg.scb_scramble_en == 0) begin  //backdoor reads used only without scrambling
        check_trans(trans);
      end else begin  //sw reads are used only with scrambling
        cfg.flash_rd_data.push_back(trans.data);
      end
    end
  endtask

  // the TLUL response data are compared to the backdoor-read data using the bit-mask.
  virtual function void check_trans(flash_trans_t rd_trans);
    bit                  [ TL_AW-1:0] addr;
    bit                  [ TL_DW-1:0] data;
    bit                  [TL_AIW-1:0] source;
    flash_op_t                        flash_read;
    logic                [ TL_DW-1:0] exp_data                          [$];
    flash_mem_addr_attrs              addr_attrs = new(flash_read.addr);

    // Flash read trans
    flash_read.partition = FlashPartData;
    flash_read.op        = flash_ctrl_pkg::FlashOpRead;
    flash_read.num_words = 1;
    flash_read.addr      = rd_trans.addr;

    //comparing backdoor read data and direct read data
    cfg.flash_mem_bkdr_read(flash_read, exp_data);
    if (exp_data[0] != rd_trans.data) begin
      `uvm_error(`gfn, $sformatf("exp_data: 0x%0h != rd_trans: 0x%0h", exp_data[0], rd_trans.data))
    end
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

    // check addr_phase_mbox
    while (addr_phase_mbox.num() != 0) begin
      flash_trans_t t;
      void'(addr_phase_mbox.try_get(t));
      `uvm_error(`gfn, $sformatf("addr_phase_mbox item uncompared:\n%0p", t))
    end

    // check data_phase_mbox
    while (data_phase_mbox.num() != 0) begin
      flash_trans_t t;
      void'(data_phase_mbox.try_get(t));
      `uvm_error(`gfn, $sformatf("data_phase_mbox item uncompared:\n%0p", t))
    end
  endfunction

endclass
