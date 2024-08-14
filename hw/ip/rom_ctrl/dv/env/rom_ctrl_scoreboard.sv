// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(rom_ctrl_env_cfg),
    .RAL_T(rom_ctrl_regs_reg_block),
    .COV_T(rom_ctrl_env_cov)
  );
  `uvm_component_utils(rom_ctrl_scoreboard)

  // local variables
  bit [DIGEST_SIZE-1:0]          expected_digest;
  bit [kmac_pkg::AppDigestW-1:0] kmac_digest;
  bit                            rom_check_complete;
  prim_mubi_pkg::mubi4_t         digest_good;
  bit                            pwrmgr_complete;
  bit                            keymgr_complete;
  bit                            disable_rom_acc_chk;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(kmac_app_item) kmac_req_fifo;
  uvm_tlm_analysis_fifo #(kmac_app_item) kmac_rsp_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    kmac_req_fifo = new("kmac_req_fifo", this);
    kmac_rsp_fifo = new("kmac_rsp_fifo", this);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_kmac_req_fifo();
      process_kmac_rsp_fifo();
      monitor_rom_ctrl_if();
    join
  endtask

  virtual task process_kmac_req_fifo();
    kmac_app_item kmac_req;
    forever begin
      kmac_req_fifo.get(kmac_req);
      if (!cfg.en_scb) continue;

      `uvm_info(`gfn, $sformatf("Detected a KMAC req:\n%0s", kmac_req.sprint()), UVM_HIGH)
      // We shouldn't see any further requests one the check has completed
      `DV_CHECK_EQ(rom_check_complete, 1'b0, "Spurious ROM request received")
      // Check the data is valid
      check_kmac_data(kmac_req.byte_data_q);
    end
  endtask

  // Read data sent to the kmac block and check it against memory data
  virtual function void check_kmac_data(const ref byte byte_data_q[$]);
    int word = 0;
    int addr = 0;
    // Check that we received the expected amount of data
    `DV_CHECK_EQ(byte_data_q.size(), KMAC_DATA_SIZE, "Unexpected kmac data size")
    // Read out the data 5 bytes at a time (one word is 39bit packed into 5 byte)
    while (word < byte_data_q.size()) begin
      bit [KMAC_DATA_WORD_SIZE*8-1:0] exp, act;
      bit [ROM_MEM_W-1:0]             mem_data;
      mem_data = cfg.mem_bkdr_util_h.rom_encrypt_read32(
          addr, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE, 1'b0);
      exp = {{KMAC_DATA_WORD_SIZE*8-ROM_MEM_W{1'b0}}, mem_data};
      for (int i = 0; i < KMAC_DATA_WORD_SIZE; i++) begin
        act[i*8+:8] = byte_data_q[word+i];
      end
      // Check the data matches
      `DV_CHECK_EQ(act, exp, $sformatf("Unexpected data at addr: %0x", addr))
      // Check the address is within range
      `DV_CHECK_LT(addr, MAX_CHECK_ADDR,
          $sformatf("Check address out of range: %0x", addr))
      addr += (TL_DW / 8);
      word += KMAC_DATA_WORD_SIZE;
    end
  endfunction

  virtual task process_kmac_rsp_fifo();
    kmac_app_item kmac_rsp;
    forever begin
      kmac_rsp_fifo.get(kmac_rsp);
      if (!cfg.en_scb) continue;

      `uvm_info(`gfn, $sformatf("Detected a KMAC response:\n%0s", kmac_rsp.sprint()), UVM_HIGH)
      // We shouldn't see any further responses one the check has completed
      `DV_CHECK_EQ(rom_check_complete, 1'b0, "Spurious ROM response received")
      kmac_digest = kmac_rsp.rsp_digest_share0 ^ kmac_rsp.rsp_digest_share1;
      get_expected_digest();
      update_ral_digests();
      digest_good = prim_mubi_pkg::mubi4_bool_to_mubi(
                    kmac_digest[DIGEST_SIZE-1:0] == expected_digest);
      rom_check_complete = 1'b1;
    end
  endtask

  // Pull the expected digest value from the top of rom
  virtual function void get_expected_digest();
    bit [DIGEST_SIZE-1:0]    digest;
    bit [`ROM_BYTE_ADDR_WIDTH-1:0] dig_addr;
    // Get the digest from rom
    // The digest is the top 8 words in memory (unscrambled)
    dig_addr = MAX_CHECK_ADDR;
    for (int i = 0; i < DIGEST_SIZE / TL_DW; i++) begin
      bit [ROM_MEM_W-1:0] mem_data = cfg.mem_bkdr_util_h.rom_encrypt_read32(
          dig_addr, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE, 1'b0);
      digest[i*TL_DW+:TL_DW] = mem_data[TL_DW-1:0];
      dig_addr += (TL_DW / 8);
    end
    expected_digest = digest;
  endfunction

  // Update the RAL model with expected values for the digest registers
  //
  // This works by using the predict function with UVM_PREDICT_READ. This tells the register model
  // that we've just read the given value from the registers. We do this rather than using
  // UVM_PREDICT_DIRECT (the default) because it avoids UVM thinking that there might be a race
  // against CSR operations that are already in flight.
  virtual function void update_ral_digests();
    for (int i = 0; i < DIGEST_SIZE / TL_DW; i++) begin
      `DV_CHECK(ral.digest[i].predict(.value(kmac_digest[i*TL_DW+:TL_DW]),
                                      .kind(UVM_PREDICT_READ)))
      `DV_CHECK(ral.exp_digest[i].predict(.value(expected_digest[i*TL_DW+:TL_DW]),
                                          .kind(UVM_PREDICT_READ)))
    end
  endfunction

  // Montitor and check outputs sent to pwrmgr and keymgr
  virtual task monitor_rom_ctrl_if();
    if (!cfg.en_scb) return;
    forever begin
      @(cfg.rom_ctrl_vif.pwrmgr_data or cfg.rom_ctrl_vif.keymgr_data or cfg.under_reset);
      if (cfg.under_reset) continue;
      // Check data sent to pwrmgr
      if (prim_mubi_pkg::mubi4_test_true_strict(cfg.rom_ctrl_vif.pwrmgr_data.done)) begin
        `DV_CHECK_EQ(pwrmgr_complete, 1'b0, "Spurious pwrmgr signal")
        `DV_CHECK_EQ(cfg.rom_ctrl_vif.pwrmgr_data.good, digest_good, "Incorrect pwrmgr result")
        pwrmgr_complete = 1'b1;
      end
      // Check data sent to keymgr
      if (cfg.rom_ctrl_vif.keymgr_data.valid) begin
        `DV_CHECK_EQ(keymgr_complete, 1'b0, "Spurious keymgr signal")
        `DV_CHECK_EQ(cfg.rom_ctrl_vif.keymgr_data.data, kmac_digest[DIGEST_SIZE-1:0], "Incorrect keymgr digest")
        keymgr_complete = 1'b1;
      end
    end
  endtask

  virtual function void check_rom_access(tl_seq_item item);
    bit [ROM_MEM_W-1:0] exp_data;

    if (item.is_write()) begin
      `DV_CHECK_EQ(item.d_error, 1'b1, "Attempted write did not return error")
    end
    `DV_CHECK_EQ(item.d_error, item.get_exp_d_error(), "TLUL ROM read error incorrect")

    exp_data = cfg.mem_bkdr_util_h.rom_encrypt_read32(
        item.a_addr, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE, 1'b1);

    for (int i = 0; i < TL_DW / 8; i++) begin
      if (item.a_mask[i]) begin
        `DV_CHECK_EQ(item.d_data[i*8+:8], exp_data[i*8+:8], "TLUL ROM read data incorrect")
      end
    end
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    dv_base_reg_block ral_model = cfg.ral_models[ral_name];
    uvm_reg_addr_t    csr_addr = ral_model.get_word_aligned_addr(item.a_addr);
    uvm_reg           csr = ral_model.default_map.get_reg_by_offset(csr_addr);

    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    if (ral_name == "rom_ctrl_prim_reg_block") begin
      if (channel == DataChannel && !disable_rom_acc_chk) begin
        check_rom_access(item);
      end
      return;
    end

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // If we get here, then the access was on the register channel. If it was to an invalid CSR,
    // there's nothing more to do. The base classes should already predict an error response.
    if (csr == null)
      return;

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
        if (addr_phase_write && item.a_data[0]) set_exp_alert("fatal", .is_fatal(0));
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
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    if (cfg.en_scb) begin
      `DV_CHECK_EQ(rom_check_complete, 1'b1, "rom check didn't finish")
      `DV_CHECK_EQ(pwrmgr_complete, 1'b1, "pwrmgr signals never checked")
      `DV_CHECK_EQ(keymgr_complete, 1'b1, "keymgr signals never checked")

      // We normally expect pwrmgr_complete to be true, which means that we have sent MuBi4True to
      // the power manager to say that the rom check has finished. It won't be true if we saw a
      // reset before the ROM check finished. In that case, the vseq should have finished before we
      // came out of reset, so we will be in reset now.
      //
      // The other thing that can happen is an injected error that puts the FSM in rom_ctrl_fsm into
      // the Invalid state. This is a terminal state, so we won't have told the power manager that
      // the check has finished.
      if (!pwrmgr_complete) begin
        if (cfg.clk_rst_vif.rst_n) begin
          string      fsm_state_path = "tb.dut.gen_fsm_scramble_enabled.u_checker_fsm.state_q";
          logic [9:0] fsm_state;

          `DV_CHECK(uvm_hdl_read(fsm_state_path, fsm_state));
          `DV_CHECK_EQ(fsm_state, rom_ctrl_pkg::Invalid)
        end
      end
    end
  endfunction

endclass
