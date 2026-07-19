// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`uvm_analysis_imp_decl(_kmac_req)
`uvm_analysis_imp_decl(_kmac_txn)

class rom_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(rom_ctrl_env_cfg),
    .RAL_T(rom_ctrl_regs_reg_block),
    .COV_T(rom_ctrl_env_cov)
  );
  `uvm_component_utils(rom_ctrl_scoreboard)

  // The digest of ROM contents that has been returned from KMAC. This is valid if
  // rom_check_complete is true. It is sized to be DIGEST_SIZE bits long: this might be shorter than
  // the interface width from KMAC, but rom_ctrl will only look at the bottom bits.
  bit [DIGEST_SIZE-1:0]  kmac_digest;

  bit                    m_kmac_req_sent;
  bit                    rom_check_complete;
  prim_mubi_pkg::mubi4_t digest_good;
  bit                    pwrmgr_complete;
  bit                    keymgr_complete;
  bit                    disable_rom_acc_chk;

  // An import for request packets sent to KMAC
  uvm_analysis_imp_kmac_req #(kmac_app_req_packet_item, rom_ctrl_scoreboard) m_kmac_req_imp;

  // An import for complete transactions between rom_ctrl and KMAC
  uvm_analysis_imp_kmac_txn #(kmac_app_mon_item, rom_ctrl_scoreboard)        m_kmac_txn_imp;

  `uvm_component_new

  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);

  // React to a request packet sent to KMAC. One of these is sent when rom_ctrl has finished the
  // contents of ROM.
  //
  // Only one such request should be sent per reset (tracked with m_kmac_req_sent). For the request
  // that is sent, we then check that the data being sent matches the contents of ROM, which we can
  // read through a memory backdoor. This checks that rom_ctrl has successfully read the contents of
  // ROM.
  extern function void write_kmac_req(kmac_app_req_packet_item packet);

  // Follow responses sent from KMAC. There will be one after each reset and it will be a response
  // to a request that was seen in process_kmac_req_fifo.
  //
  // This function updates the model of the digest that came from KMAC (used for the contents of the
  // DIGEST registers and also for a check on the digest sent to keymgr later). It also updates the
  // model of the EXP_DIGEST registers. Finally, it updates the model of whether the two digests
  // agree (to check the GOOD field of the signal that will be sent to pwrmgr).
  extern function void write_kmac_txn(kmac_app_mon_item txn);

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
  m_kmac_req_imp = new("m_kmac_req_imp", this);
  m_kmac_txn_imp = new("m_kmac_txn_imp", this);
endfunction

task rom_ctrl_scoreboard::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    monitor_rom_ctrl_if();
  join
endtask

function void rom_ctrl_scoreboard::write_kmac_req(kmac_app_req_packet_item packet);
  byte unsigned req_bytes[$];
  int unsigned  nonzero_share1_indices[$];
  // The length (in words) of the byte queue that matches with a prefix of the ROM.
  int unsigned  matching_pfx_len;
  // The index of the first word in ROM that we expect to match the tail of ROM data (based on the
  // number of observed KMAC requests and KMAC_DATA_SIZE)
  int unsigned  start_tail_idx;

  if (!cfg.en_scb) return;

  // Check that we haven't already sent a packet
  if (m_kmac_req_sent) begin
    `uvm_error(get_full_name(), "Unexpected extra packet sent to KMAC.")
  end
  m_kmac_req_sent = 1;

  packet.get_share_byte_queue(0, req_bytes);
  if (packet.get_reqs_with_nonzero_share(1, nonzero_share1_indices)) begin
    `uvm_error(get_full_name(),
               $sformatf("Packet had %0d requests with a nonzero share1 (indices: %0p).",
                         nonzero_share1_indices.size(), nonzero_share1_indices))
  end

  // Check the amount of data sent. We might have forced the hardware to skip over the middle
  // portion, but it definitely shouldn't have sent more than KMAC_DATA_SIZE. It should also have
  // sent a multiple of 5 bytes (because it sends 5-byte packets).
  if (req_bytes.size() > KMAC_DATA_SIZE) begin
    `uvm_error("data_size_check",
               $sformatf("rom_ctrl sent %0d bytes to KMAC, but KMAC_DATA_SIZE is just %0d.",
                         req_bytes.size(), KMAC_DATA_SIZE))
  end
  if (req_bytes.size() % 5) begin
    `uvm_error("data_size_check",
               $sformatf("rom_ctrl sent %0d bytes to KMAC, but this isn't a multiple of 5.",
                         req_bytes.size()))
  end

  // Read ROM through a backdoor in 5-byte words, comparing the values with items in req_bytes. Stop
  // when we get to the end of the request or end of ROM.
  for (matching_pfx_len = 0; matching_pfx_len < KMAC_DATA_SIZE / 5; matching_pfx_len++) begin
    bit [ROM_MEM_W-1:0] mem_data;
    bit [39:0]          seen_word;

    // If we have got to the end of req_bytes it looks like rom_ctrl just sent some prefix of the
    // ROM and then stopped.
    if (req_bytes.size() < 5 * (1 + matching_pfx_len)) begin
      `uvm_error("just_sent_prefix",
                 $sformatf({"The first %0d bytes that rom_ctrl sent to KMAC ",
                            "match the contents of ROM but a total of only %0d ",
                            "bytes were sent and KMAC_DATA_SIZE = %0d."},
                           5 * matching_pfx_len, req_bytes.size(), KMAC_DATA_SIZE))
      return;
    end

    mem_data = cfg.rom_ctrl_bkdr_util_h.rom_encrypt_read32(4 * matching_pfx_len,
                                                           RND_CNST_SCR_KEY,
                                                           RND_CNST_SCR_NONCE,
                                                           1'b0);

    seen_word = {req_bytes[matching_pfx_len * 5 + 4],
                 req_bytes[matching_pfx_len * 5 + 3],
                 req_bytes[matching_pfx_len * 5 + 2],
                 req_bytes[matching_pfx_len * 5 + 1],
                 req_bytes[matching_pfx_len * 5]};

    if (seen_word != mem_data) begin
      // This is the first word of ROM that doesn't match with something we saw being sent to KMAC.
      // That's possibly fine: we might have forced rom_ctrl to skip over an internal section. Break
      // from this loop and we'll check the "tail" next.
      `uvm_info("end_of_prefix",
                $sformatf({"Saw a mismatch between ROM and KMAC request on word %0d ",
                           "(possibly because of an injected skip)."},
                          matching_pfx_len),
                UVM_HIGH)
      break;
    end
  end

  // Check the tail of the observed request bytes matches the equivalent-length tail of ROM data.
  // Each word in the ROM causes rom_ctrl to send 5 bytes to KMAC. As such, the total number of
  // words sent to KMAC is req_bytes.size()/5 and there are matching_pfx_len words less than that in
  // the tail that we check.
  //
  // There are a total of KMAC_DATA_NUM_WORDS words that will be sent to KMAC. Subtracting the
  // length of the tail from that count gives the word index in ROM of the start of the tail.
  start_tail_idx = KMAC_DATA_NUM_WORDS - (req_bytes.size() / 5 - matching_pfx_len);

  for (int unsigned word_idx = 0; word_idx + start_tail_idx < KMAC_DATA_NUM_WORDS; word_idx++) begin
    bit [ROM_MEM_W-1:0] mem_data;
    bit [39:0]          seen_word;
    // The byte index of the word in req_bytes.
    int unsigned        idx_in_req_bytes;

    mem_data = cfg.rom_ctrl_bkdr_util_h.rom_encrypt_read32(4 * (start_tail_idx + word_idx),
                                                           RND_CNST_SCR_KEY,
                                                           RND_CNST_SCR_NONCE,
                                                           1'b0);

    idx_in_req_bytes = 5 * (matching_pfx_len + word_idx);

    // Look up the word in req_bytes. We know the bytes exist because the highest we'll access is
    // 5*idx_in_req_bytes + 4, which is 5*(matching_pfx_len + word_idx) + 4. The loop bound on
    // word_idx means that this is strictly less than
    //
    //    5*(matching_pfx_len + KMAC_DATA_SIZE/5 - start_tail_idx) + 4 =
    //
    // Expanding the definition of start_tail_idx and cancelling the KMAC_DATA_SIZE/5 and
    // matching_pfx_len terms, this is equal to req_bytes.size().
    seen_word = {req_bytes[idx_in_req_bytes + 4],
                 req_bytes[idx_in_req_bytes + 3],
                 req_bytes[idx_in_req_bytes + 2],
                 req_bytes[idx_in_req_bytes + 1],
                 req_bytes[idx_in_req_bytes]};

    if (seen_word != mem_data) begin
      `uvm_error("rom_data_mismatch",
                 $sformatf({"Bytes %0d..%0d that rom_ctrl sent to KMAC don't match the ROM. ",
                            "Observed data: 0x%0h. Expected data: 0x%0h. ",
                            "Because the first %0d bytes matched (of the %0d bytes sent), ",
                            "we expect byte %0d to correspond to ROM data at ",
                            "byte offset 0x%0h (word offset 0x%0h)."},
                           idx_in_req_bytes,
                           idx_in_req_bytes+4,
                           seen_word, mem_data,
                           5 * matching_pfx_len,
                           req_bytes.size(),
                           idx_in_req_bytes,
                           4 * (start_tail_idx + word_idx),
                           start_tail_idx + word_idx))
    end
  end
endfunction

function void rom_ctrl_scoreboard::write_kmac_txn(kmac_app_mon_item txn);
  bit [DIGEST_SIZE-1:0] expected_digest;

  if (!cfg.en_scb) return;

  kmac_digest = DIGEST_SIZE'(txn.m_rsp.m_digest_s0 ^ txn.m_rsp.m_digest_s1);
  expected_digest = get_expected_digest();

  update_ral_digests(kmac_digest, expected_digest);
  digest_good = prim_mubi_pkg::mubi4_bool_to_mubi(kmac_digest == expected_digest);

  rom_check_complete = 1;
endfunction

function bit [DIGEST_SIZE-1:0] rom_ctrl_scoreboard::get_expected_digest();
  bit [DIGEST_SIZE-1:0]    digest;
  bit [ROM_BYTE_ADDR_WIDTH-1:0] dig_addr;
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
      `DV_CHECK_EQ(cfg.rom_ctrl_vif.cb.keymgr_data.data, kmac_digest, "Incorrect keymgr digest")
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
  // for read, update prediction at address phase and compare at data phase
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
  m_kmac_req_sent = 1'b0;
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
