// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(sram_ctrl_env_cfg),
    .RAL_T(sram_ctrl_reg_block),
    .COV_T(sram_ctrl_env_cov)
  );
  `uvm_component_utils(sram_ctrl_scoreboard)
  `uvm_component_new

  // local variables

  typedef struct {
    // 1 for writes, 0 for reads
    bit we;

    // TLUL address
    bit [TL_AW-1:0] addr;

    // Contains either the requested write data
    // or the read response data
    bit [TL_DW-1:0] data;

    // only writes are masked, all reads are full-word
    bit [TL_DBW-1:0] mask;

    // Tag the memory transaction with the appropriate key and nonce,
    // so that we can keep track even if a new key is requested
    otp_ctrl_pkg::sram_key_t key;
    otp_ctrl_pkg::sram_nonce_t nonce;

  } sram_trans_t;

  // TLM agent fifos for the tl_agent connected to the SRAM memory itself
  uvm_tlm_analysis_fifo #(tl_seq_item) sram_tl_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) sram_tl_d_chan_fifo;

  uvm_tlm_analysis_fifo #(push_pull_item#(.DeviceDataWidth(KDI_DATA_SIZE))) kdi_fifo;

  // local queues to hold incoming packets pending comparison

  // mailbox to send a sram_trans_t struct to the data phase collection,
  // where read addresses can be collected.
  mailbox #(sram_trans_t) data_phase_mbox;

  // mailbox that all completed sram_trans_t structs will be pushed into for processing.
  mailbox #(sram_trans_t) completed_trans_mbox;

  otp_ctrl_pkg::sram_key_t key     = sram_ctrl_pkg::RndCnstSramKeyDefault;
  otp_ctrl_pkg::sram_nonce_t nonce = sram_ctrl_pkg::RndCnstSramNonceDefault;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    sram_tl_a_chan_fifo = new("sram_tl_a_chan_fifo", this);
    sram_tl_d_chan_fifo = new("sram_tl_d_chan_fifo", this);

    kdi_fifo = new("kdi_fifo", this);

    data_phase_mbox = new();
    completed_trans_mbox = new();
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_sram_tl_a_chan_fifo();
      process_sram_tl_d_chan_fifo();
      process_kdi_fifo();
      process_sram_trans();
    join_none
  endtask

  virtual task process_sram_tl_a_chan_fifo();
    tl_seq_item item;
    sram_trans_t addr_trans;
    forever begin
      sram_tl_a_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf("Received sram_tl_a_chan item:\n%0s", item.sprint()), UVM_HIGH)

      // TODO: need to ensure that we don't process TLUL errors

      addr_trans.we = item.is_write();
      addr_trans.addr = item.a_addr;
      addr_trans.mask = item.a_mask;

      addr_trans.key = key;
      addr_trans.nonce = nonce;

      // Only set data in address phase if a write is detected
      if (item.is_write()) begin
        addr_trans.data = item.a_data;
        // write the completed transaction to be processed
        completed_trans_mbox.put(addr_trans);
        `uvm_info({`gfn, "::process_sram_tl_a_chan_fifo()"},
                  $sformatf("Put COMPLETED_WRITE transaction into completed_trans_mbox: %0p", addr_trans),
                  UVM_HIGH)
      end else begin
        // on a read transaction, set the address and then send the incomplete transaction item
        // to be completed in the data phase
        data_phase_mbox.put(addr_trans);
        `uvm_info({`gfn, "::process_sram_tl_a_chan_fifo()"},
                  $sformatf("Put INCOMPLETE_READ transaction into data_phase_mbox: %0p", addr_trans),
                  UVM_HIGH)
      end
    end
  endtask

  virtual task process_sram_tl_d_chan_fifo();
    tl_seq_item item;
    sram_trans_t data_trans;
    forever begin
      sram_tl_d_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf("Received sram_tl_d_chan item:\n%0s", item.sprint()), UVM_HIGH)

      // TODO: need to ensure that we don't process TLUL errors

      // check packet integrity
      void'(item.is_ok());

      // here we only want to process read responses
      //
      // TODO: for now...
      if (item.d_opcode == tlul_pkg::AccessAckData) begin
        // if data channel has a read response, then there is an incomplete transaction
        // waiting in the data_phase_mbox
        data_phase_mbox.get(data_trans);
        `uvm_info({`gfn, "::process_sram_tl_d_chan_fifo()"},
                  $sformatf("Got INCOMPLETE_READ transaction from data_phase_mbox: %0p", data_trans),
                  UVM_HIGH)
        // set the read response data
        data_trans.data = item.d_data;
        completed_trans_mbox.put(data_trans);
        `uvm_info({`gfn, "::process_sram_tl_d_chan_fifo()"},
                  $sformatf("Put COMPLETED_READ transaction into completed_trans_mbox: %0p", data_trans),
                  UVM_HIGH)
      end
    end
  endtask

  // This task polls the kdi_fifo for completed key request transactions
  virtual task process_kdi_fifo();
    bit seed_valid;
    push_pull_item #(.DeviceDataWidth(KDI_DATA_SIZE)) item;
    forever begin
      kdi_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received transaction from kdi_fifo:\n%0s", item.convert2string()), UVM_HIGH)

      // When KDI item is seen, update key, nonce
      //
      // TODO: update STATUS.scr_key_seed_valid
      {key, nonce, seed_valid} = item.d_data;

      `uvm_info(`gfn, $sformatf("Updated key: 0x%0x", key), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("Updated nonce: 0x%0x", nonce), UVM_HIGH)
    end
  endtask

  // This task continuously pulls items from the completed_trans_mbox
  // and checks them for correctness by using the mem_bkdr_if.
  virtual task process_sram_trans();
    sram_trans_t trans;
    forever begin
      completed_trans_mbox.get(trans);

      // SRAM writes take 2 cycles to execute, while reads return data in the TLUL response.
      if (trans.we) begin
        cfg.clk_rst_vif.wait_clks(2);
      end

      `uvm_info({`gfn, "::process_sram_trans()"},
                $sformatf("Received COMPLETED transaction from completed_trans_mbox: %0p", trans),
                UVM_HIGH)
      check_mem_trans(trans);
    end
  endtask

  // Given a complete memory transaction item as input,
  // this function compares against the SRAM for correctness
  // using the mem_bkdr_if.
  //
  // TLUL allows partial reads and writes, so we first need to construct a bit-mask
  // based off of the TLUL mask field.
  // We then read from the memory using the backdoor interface, and can then directly compare
  // the TLUL response data to the backdoor-read data using the bit-mask.
  virtual function void check_mem_trans(sram_trans_t t);
    bit [TL_AW-1:0] word_addr;
    bit [TL_DW-1:0] bit_mask;

    // data read from SRAM through backdoor
    bit [TL_DW-1:0] exp_data;
    bit [TL_DW-1:0] exp_masked_data;
    bit [TL_DW-1:0] act_masked_data;

    `uvm_info(`gfn, $sformatf("Checking SRAM memory transaction: %0p", t), UVM_HIGH)

    // Word align the request address
    word_addr = {t.addr[TL_AW-1:2], 2'b00};
    `uvm_info(`gfn, $sformatf("word_addr: 0x%0x", word_addr), UVM_HIGH)

    // Expand the byte-oriented mask into a full bit mask
    for (int i = 0; i < TL_DBW; i++) begin
      bit_mask[i*8 +: 8] = {8{t.mask[i]}};
    end

    // backdoor read the mem
    exp_data = cfg.mem_bkdr_vif.sram_encrypt_read32(word_addr, t.key, t.nonce);

    exp_masked_data = exp_data & bit_mask;
    act_masked_data = t.data & bit_mask;

    `uvm_info(`gfn, $sformatf("exp_masked_data: 0x%0x", exp_masked_data), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("act_masked_data: 0x%0x", act_masked_data), UVM_HIGH)

    `DV_CHECK_EQ_FATAL(exp_masked_data, act_masked_data)
  endfunction

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
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // FIXME
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      "exec_regwen": begin
        // do nothing
      end
      "exec": begin
      end
      "status": begin
        // TODO
        do_read_check = 1'b0;
      end
      "ctrl_regwen": begin
        // do nothing
      end
      "ctrl": begin
        // do nothing if 0 is written
        if (addr_phase_write && item.a_data) begin
        end
      end
      "error_address": begin
        // TODO
        do_read_check = 1'b0;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
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
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
