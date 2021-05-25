// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(rom_ctrl_env_cfg),
    .RAL_T(rom_ctrl_regs_reg_block),
    .COV_T(rom_ctrl_env_cov)
  );
  `uvm_component_utils(rom_ctrl_scoreboard)

  // local variables
  bit [kmac_pkg::AppDigestW-1:0] expected_digest;
  bit [kmac_pkg::AppDigestW-1:0] kmac_digest;
  bit                            rom_check_complete;
  bit                            digest_good;
  bit                            pwrmgr_complete;
  bit                            keymgr_complete;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(kmac_app_item) kmac_req_fifo;
  uvm_tlm_analysis_fifo #(kmac_app_item) kmac_rsp_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item)   rom_tl_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item)   rom_tl_d_chan_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    kmac_req_fifo = new("kmac_req_fifo", this);
    kmac_rsp_fifo = new("kmac_rsp_fifo", this);
    rom_tl_a_chan_fifo = new("rom_tl_a_chan_fifo", this);
    rom_tl_d_chan_fifo = new("rom_tl_d_chan_fifo", this);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_kmac_req_fifo();
      process_kmac_rsp_fifo();
      monitor_rom_ctrl_if();
      process_rom_tl_a_chan_fifo();
      process_rom_tl_d_chan_fifo();
    join
  endtask

  virtual task process_kmac_req_fifo();
    kmac_app_item kmac_req;
    forever begin
      kmac_req_fifo.get(kmac_req);
      `uvm_info(`gfn, $sformatf("Detected a KMAC req:\n%0s", kmac_req.sprint()), UVM_HIGH)
      // We shouldn't see any further requests one the check has completed
      `DV_CHECK_EQ(rom_check_complete, 1'b0, "Spurious ROM request received")
      // Check the data is valid
      check_kmac_data(kmac_req.byte_data_q);
    end
  endtask

  // Read data sent to the kmac block and check it against memory data
  virtual function void check_kmac_data(const ref byte byte_data_q[$]);
    int dword = 0;
    int addr = 0;
    // Check that we received the expected amount of data
    `DV_CHECK_EQ(byte_data_q.size(), KMAC_DATA_SIZE, "Unexpected kmac data size")
    // Read out the data 8 bytes at a time
    while (dword < byte_data_q.size()) begin
      bit [kmac_pkg::MsgWidth-1:0] exp, act;
      bit [ROM_MEM_W-1:0]          mem_data;
      mem_data = cfg.mem_bkdr_vif.rom_encrypt_read32(
          addr, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE, 1'b0);
      exp = {{kmac_pkg::MsgWidth-ROM_MEM_W{1'b0}}, mem_data};
      for (int i = 0; i < kmac_pkg::MsgWidth / 8; i++) begin
        act[i*8+:8] = byte_data_q[dword+i];
      end
      // Check the data matches
      `DV_CHECK_EQ(act, exp, $sformatf("Unexpected data at addr: %0x", addr))
      // Check the address is within range
      `DV_CHECK_LT(addr, MAX_CHECK_ADDR,
          $sformatf("Check address out of range: %0x", addr))
      addr  += (TL_DW / 8);
      dword += (kmac_pkg::MsgWidth / 8);
    end
  endfunction

  virtual task process_kmac_rsp_fifo();
    kmac_app_item kmac_rsp;
    forever begin
      kmac_rsp_fifo.get(kmac_rsp);
      `uvm_info(`gfn, $sformatf("Detected a KMAC response:\n%0s", kmac_rsp.sprint()), UVM_HIGH)
      // We shouldn't see any further responses one the check has completed
      `DV_CHECK_EQ(rom_check_complete, 1'b0, "Spurious ROM response received")
      kmac_digest = kmac_rsp.rsp_digest_share0 ^ kmac_rsp.rsp_digest_share1;
      get_expected_digest();
      update_ral_digests();
      digest_good = (kmac_digest == expected_digest);
      rom_check_complete = 1'b1;
    end
  endtask

  // Pull the expected digest value from the top of rom
  virtual function void get_expected_digest();
    bit [kmac_pkg::AppDigestW-1:0]    digest;
    bit [rom_ctrl_reg_pkg::RomAw-1:0] dig_addr;
    // Get the digest from rom
    // The digest is the top 8 words in memory (unscrambled)
    dig_addr = MAX_CHECK_ADDR;
    for (int i = 0; i < kmac_pkg::AppDigestW / TL_DW; i++) begin
      bit [ROM_MEM_W-1:0] mem_data = cfg.mem_bkdr_vif.rom_encrypt_read32(
          dig_addr, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE, 1'b0);
      digest[i*TL_DW+:TL_DW] = mem_data[TL_DW-1:0];
      dig_addr += (TL_DW / 8);
    end
    expected_digest = digest;
  endfunction

  // Update the RAL model with expected values for the digest registers
  virtual function void update_ral_digests();
    for (int i = 0; i < kmac_pkg::AppDigestW / TL_DW; i++) begin
      string digest_name = $sformatf("digest_%0d", i);
      uvm_reg csr = ral.get_reg_by_name(digest_name);
      void'(csr.predict(.value(kmac_digest[i*TL_DW+:TL_DW]), .kind(UVM_PREDICT_READ)));
    end
    for (int i = 0; i < kmac_pkg::AppDigestW / TL_DW; i++) begin
      string digest_name = $sformatf("exp_digest_%0d", i);
      uvm_reg csr = ral.get_reg_by_name(digest_name);
      void'(csr.predict(.value(expected_digest[i*TL_DW+:TL_DW]), .kind(UVM_PREDICT_READ)));
    end
  endfunction

  // Montitor and check outputs sent to pwrmgr and keymgr
  virtual task monitor_rom_ctrl_if();
    forever begin
      @(cfg.rom_ctrl_vif.pwrmgr_data or cfg.rom_ctrl_vif.keymgr_data or cfg.under_reset);
      if (cfg.under_reset) continue;
      // Check data sent to pwrmgr
      if (cfg.rom_ctrl_vif.pwrmgr_data.done) begin
        `DV_CHECK_EQ(pwrmgr_complete, 1'b0, "Spurious pwrmgr signal")
        `DV_CHECK_EQ(cfg.rom_ctrl_vif.pwrmgr_data.good, digest_good, "Incorrect pwrmgr result")
        pwrmgr_complete = 1'b1;
      end
      // Check data sent to keymgr
      if (cfg.rom_ctrl_vif.keymgr_data.valid) begin
        `DV_CHECK_EQ(keymgr_complete, 1'b0, "Spurious keymgr signal")
        `DV_CHECK_EQ(cfg.rom_ctrl_vif.keymgr_data.data, kmac_digest, "Incorrect keymgr digest")
        keymgr_complete = 1'b1;
      end
    end
  endtask

  virtual task process_rom_tl_a_chan_fifo();
    tl_seq_item item;
    forever begin
      rom_tl_a_chan_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Rcvd rom_tl_a_chan item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  virtual task process_rom_tl_d_chan_fifo();
    tl_seq_item item;
    forever begin
      rom_tl_d_chan_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Rcvd rom_tl_d_chan item:\n%0s", item.sprint()), UVM_HIGH)
      // check packet integrity
      void'(item.is_ok());
      if (item.is_write()) begin
        `DV_CHECK_EQ(item.d_error, 1'b1, "Attempted write did not return error")
      end else begin
        check_mem_read(item);
      end
    end
  endtask

  virtual function void check_mem_read(tl_seq_item item);
    bit [ROM_MEM_W-1:0] exp_data;

    exp_data = cfg.mem_bkdr_vif.rom_encrypt_read32(
        item.a_addr, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE, 1'b1);

    `DV_CHECK_EQ(item.d_error, item.get_exp_d_error(), "TLUL ROM read error incorrect")
    for (int i = 0; i < TL_DW / 8; i++) begin
      if (item.a_mask[i]) begin
        `DV_CHECK_EQ(item.d_data[i*8+:8], exp_data[i*8+:8], "TLUL ROM read data incorrect")
      end
    end
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs[ral_name]}) begin
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
      "alert_test": begin
        // do_nothing
      end
      "fatal_alert_cause": begin
        // do_nothing
      end
      "digest_0", "digest_1", "digest_2", "digest_3", "digest_4", "digest_5", "digest_6",
          "digest_7", "exp_digest_0", "exp_digest_1", "exp_digest_2", "exp_digest_3",
          "exp_digest_4", "exp_digest_5", "exp_digest_6", "exp_digest_7": begin
        if (!rom_check_complete) begin
          do_read_check = 1'b0;
        end
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
    rom_check_complete = 1'b0;
    pwrmgr_complete = 1'b0;
    keymgr_complete = 1'b0;
    rom_tl_a_chan_fifo.flush();
    rom_tl_d_chan_fifo.flush();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    `DV_CHECK_EQ(rom_check_complete, 1'b1, "rom check didn't finish")
    `DV_CHECK_EQ(pwrmgr_complete, 1'b1, "pwrmgr signals never checked")
    `DV_CHECK_EQ(keymgr_complete, 1'b1, "keymgr signals never checked")
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, rom_tl_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, rom_tl_d_chan_fifo)
  endfunction

endclass
