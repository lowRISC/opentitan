// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(rom_ctrl_env_cfg),
    .RAL_T(rom_ctrl_regs_reg_block),
    .COV_T(rom_ctrl_env_cov)
  );
  `uvm_component_utils(rom_ctrl_scoreboard)

  // The digest of ROM contents that has been returned from KMAC. This is valid if
  // rom_check_complete is true.
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

  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);

  // Follow requests sent to KMAC. One of these is sent when rom_ctrl has finished the contents of
  // ROM. This task checks that rom_ctrl doesn't send more than one request to KMAC after a reset
  // and uses check_kmac_data to check the request itself looks right.
  extern task process_kmac_req_fifo();

  // Check the data in a KMAC request. This is what rom_ctrl sent to KMAC and it should be a copy of
  // the contents of ROM, which we can read through a memory backdoor. This checks that rom_ctrl has
  // successfully read the contents of ROM.
  extern function void check_kmac_data(const ref byte byte_data_q[$]);

  // Follow responses sent from KMAC. There will be one after each reset and it will be a response
  // to a request that was seen in process_kmac_req_fifo.
  //
  // This function updates the model of the digest that came from KMAC (used for the contents of the
  // DIGEST registers and also for a check on the digest sent to keymgr later). It also updates the
  // model of the EXP_DIGEST registers. Finally, it updates the model of whether the two digests
  // agree (to check the GOOD field of the signal that will be sent to pwrmgr).
  extern task process_kmac_rsp_fifo();

  // Return the top words of the ROM image, which give an expected digest value
  extern function bit [DIGEST_SIZE-1:0] get_expected_digest();

  // Update the RAL model for the contents of the DIGEST and EXP_DIGEST registers.
  extern function void update_ral_digests(bit [DIGEST_SIZE-1:0] kmac_digest,
                                          bit [DIGEST_SIZE-1:0] expected_digest);

  // Monitor values sent to pwrmgr and keymgr.
  //
  // The pwrmgr_data done and the keymgr_data valid flags should each pulse for a single cycle. This
  // task checks that they don't go high more than once and checks that the pwrmgr_data.good and
  // keymgr_data.data signals match what we expect (based on the response from KMAC).
  extern task monitor_rom_ctrl_if();

  // Check a TL item thac corresponds to a ROM access, making sure that invalid requests return
  // errors and any other operation returns the correct ROM data.
  extern function void check_rom_access(tl_seq_item item);

  // Check a TL item that corresponds to a register access on the given channel
  extern function void check_reg_access(tl_seq_item item, tl_channels_e channel);

  // Check a TL item seen on the given channel for the given RAL interface. This overrides a task
  // from cip_base_scoreboard.
  extern virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);

  extern virtual function void reset(string kind = "HARD");
  extern function void check_phase(uvm_phase phase);
  extern virtual function void phase_ready_to_end(uvm_phase phase);

endclass

function void rom_ctrl_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  kmac_req_fifo = new("kmac_req_fifo", this);
  kmac_rsp_fifo = new("kmac_rsp_fifo", this);
endfunction

task rom_ctrl_scoreboard::run_phase(uvm_phase phase);
  super.run_phase(phase);
  fork
    process_kmac_req_fifo();
    process_kmac_rsp_fifo();
    monitor_rom_ctrl_if();
  join
endtask

task rom_ctrl_scoreboard::process_kmac_req_fifo();
  kmac_app_item kmac_req;
  forever begin
    kmac_req_fifo.get(kmac_req);
    if (!cfg.en_scb) continue;

    `uvm_info(`gfn, $sformatf("Detected a KMAC req:\n%0s", kmac_req.sprint()), UVM_HIGH)
    // We shouldn't see any further requests once the check has completed
    `DV_CHECK(!rom_check_complete, "KMAC request sent after ROM check had already completed.")
    // Check the data is valid
    check_kmac_data(kmac_req.byte_data_q);
  end
endtask

// Read data sent to the kmac block and check it against memory data
function void rom_ctrl_scoreboard::check_kmac_data(const ref byte byte_data_q[$]);
  int word = 0;
  int addr = 0;
  // Check that we received the expected amount of data
  `DV_CHECK_EQ(byte_data_q.size(), KMAC_DATA_SIZE, "Unexpected kmac data size")
  // Read out the data 5 bytes at a time (one word is 39bit packed into 5 byte)
  while (word < byte_data_q.size()) begin
    bit [KMAC_DATA_WORD_SIZE*8-1:0] exp, act;
    bit [ROM_MEM_W-1:0]             mem_data;
    mem_data = cfg.rom_ctrl_bkdr_util_h.rom_encrypt_read32(
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

task rom_ctrl_scoreboard::process_kmac_rsp_fifo();
  bit [DIGEST_SIZE-1:0] expected_digest;
  kmac_app_item kmac_rsp;

  forever begin
    kmac_rsp_fifo.get(kmac_rsp);
    if (!cfg.en_scb) continue;

    `uvm_info(`gfn, $sformatf("Detected a KMAC response:\n%0s", kmac_rsp.sprint()), UVM_HIGH)

    // Check that we haven't seen one of these responses already since the last reset. If we have,
    // it's a DV bug: we should already have failed when the KMAC request was sent a few cycles ago.
    `DV_CHECK_FATAL(!rom_check_complete, "Extra KMAC response seen.")

    kmac_digest = kmac_rsp.rsp_digest_share0 ^ kmac_rsp.rsp_digest_share1;
    expected_digest = get_expected_digest();
    update_ral_digests(kmac_digest, expected_digest);
    digest_good = prim_mubi_pkg::mubi4_bool_to_mubi(
                  kmac_digest[DIGEST_SIZE-1:0] == expected_digest);
    rom_check_complete = 1'b1;
  end
endtask

function bit [DIGEST_SIZE-1:0] rom_ctrl_scoreboard::get_expected_digest();
  bit [DIGEST_SIZE-1:0]    digest;
  bit [`ROM_BYTE_ADDR_WIDTH-1:0] dig_addr;
  // Get the digest from rom
  // The digest is the top 8 words in memory (unscrambled)
  dig_addr = MAX_CHECK_ADDR;
  for (int i = 0; i < DIGEST_SIZE / TL_DW; i++) begin
    bit [ROM_MEM_W-1:0] mem_data = cfg.rom_ctrl_bkdr_util_h.rom_encrypt_read32(
        dig_addr, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE, 1'b0);
    digest[i*TL_DW+:TL_DW] = mem_data[TL_DW-1:0];
    dig_addr += (TL_DW / 8);
  end
  return digest;
endfunction

function void rom_ctrl_scoreboard::update_ral_digests(bit [DIGEST_SIZE-1:0] kmac_digest,
                                                      bit [DIGEST_SIZE-1:0] expected_digest);
  // The prediction works with kind UVM_PREDICT_READ. This tells the register model that we've just
  // read the given value from the registers. We do this rather than using UVM_PREDICT_DIRECT (the
  // default) because it avoids UVM thinking that there might be a race against CSR operations that
  // are already in flight.
  for (int i = 0; i < DIGEST_SIZE / TL_DW; i++) begin
    `DV_CHECK(ral.digest[i].predict(.value(kmac_digest[i*TL_DW+:TL_DW]),
                                    .kind(UVM_PREDICT_READ)))
    `DV_CHECK(ral.exp_digest[i].predict(.value(expected_digest[i*TL_DW+:TL_DW]),
                                        .kind(UVM_PREDICT_READ)))
  end
endfunction

task rom_ctrl_scoreboard::monitor_rom_ctrl_if();
  if (!cfg.en_scb) return;
  forever begin
    // Wait until a change to pwrmgr_data or keymgr_data (dropping out early on reset)
    fork begin : isolation_fork
      fork
        @(cfg.rom_ctrl_vif.cb.pwrmgr_data);
        @(cfg.rom_ctrl_vif.cb.keymgr_data);
        wait(cfg.under_reset);
      join_any
      disable fork;
    end join

    if (cfg.under_reset) begin
      wait(!cfg.under_reset);
      continue;
    end

    // Check data sent to pwrmgr
    if (prim_mubi_pkg::mubi4_test_true_strict(cfg.rom_ctrl_vif.cb.pwrmgr_data.done)) begin
      `DV_CHECK(!pwrmgr_complete, "Spurious pwrmgr signal")
      `DV_CHECK_EQ(cfg.rom_ctrl_vif.cb.pwrmgr_data.good, digest_good, "Incorrect pwrmgr result")
      pwrmgr_complete = 1'b1;
    end
    // Check data sent to keymgr
    if (cfg.rom_ctrl_vif.cb.keymgr_data.valid) begin
      `DV_CHECK(!keymgr_complete, "Spurious keymgr signal")
      `DV_CHECK_EQ(cfg.rom_ctrl_vif.cb.keymgr_data.data, kmac_digest[DIGEST_SIZE-1:0],
                   "Incorrect keymgr digest")
      keymgr_complete = 1'b1;
    end
  end
endtask

function void rom_ctrl_scoreboard::check_rom_access(tl_seq_item item);
  bit [ROM_MEM_W-1:0] exp_data;

  if (item.is_write()) begin
    `DV_CHECK(item.d_error, "Writes to ROM should return an error.")
  end
  `DV_CHECK_EQ(item.d_error, item.get_exp_d_error(), "TLUL ROM read error incorrect")

  exp_data = cfg.rom_ctrl_bkdr_util_h.rom_encrypt_read32(
      item.a_addr, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE, 1'b1);

  for (int i = 0; i < TL_DW / 8; i++) begin
    if (item.a_mask[i]) begin
      `DV_CHECK_EQ(item.d_data[i*8+:8], exp_data[i*8+:8], "TLUL ROM read data incorrect")
    end
  end
endfunction

function void rom_ctrl_scoreboard::check_reg_access(tl_seq_item item, tl_channels_e channel);
  dv_base_reg_block ral_model = cfg.ral_models["rom_ctrl_regs_reg_block"];
  uvm_reg_addr_t    csr_addr = ral_model.get_word_aligned_addr(item.a_addr);
  uvm_reg           csr = ral_model.default_map.get_reg_by_offset(csr_addr);

  bit     do_read_check   = 1'b1;
  bit     write           = item.is_write();

  bit addr_phase_read   = (!write && channel == AddrChannel);
  bit addr_phase_write  = (write && channel == AddrChannel);
  bit data_phase_read   = (!write && channel == DataChannel);
  bit data_phase_write  = (write && channel == DataChannel);

  // If this is an access to an address that doesn't correspond to a CSR, there is nothing to check:
  // the base classes should already predict an error response.
  if (csr == null) begin
    return;
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
endfunction

task rom_ctrl_scoreboard::process_tl_access(tl_seq_item item,
                                            tl_channels_e channel,
                                            string ral_name);
  if (ral_name == "rom_ctrl_prim_reg_block") begin
    if (channel == DataChannel && !disable_rom_acc_chk) begin
      check_rom_access(item);
    end
  end else if (ral_name == "rom_ctrl_regs_reg_block") begin
    check_reg_access(item, channel);
  end else begin
    `uvm_fatal(`gfn, $sformatf("Access through unknown ral_name: %s", ral_name))
  end
endtask

function void rom_ctrl_scoreboard::reset(string kind = "HARD");
  super.reset(kind);
  // reset local fifos queues and variables
  rom_check_complete = 1'b0;
  pwrmgr_complete = 1'b0;
  keymgr_complete = 1'b0;
endfunction

function void rom_ctrl_scoreboard::check_phase(uvm_phase phase);
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

function void rom_ctrl_scoreboard::phase_ready_to_end(uvm_phase phase);
  if (phase.get_name() != "run") return;

    // Raising an objection and waiting for the pwrmgr_complete to set. This will add an extra
    // delay after the test finishes and rom_ctrl_fsm would be in a done state which will set
    // pwrmgr_data_o.done.
    phase.raise_objection(this, {`gfn, " objection raised"});
    fork
      begin
        if (cfg.en_scb)
          wait (pwrmgr_complete);
        phase.drop_objection(this, {`gfn, " objection dropped"});
      end
    join_none
endfunction
