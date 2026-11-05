// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_scoreboard extends cip_base_scoreboard #(
  .CFG_T(rram_ctrl_env_cfg),
  .RAL_T(rram_ctrl_core_reg_block),
  .COV_T(rram_ctrl_env_cov)
);
  `uvm_component_utils(rram_ctrl_scoreboard)

  // Auto-predicts the core RAL model from bus traffic. m_tl_core_reg_adapter mirrors
  // cip_base_env's own (private) frontdoor adapter config. m_tl_core_reg_predictor_filter
  // drops d_error'd items before the predictor sees them (see rram_ctrl_reg_predictor_filter.sv
  // for why). rram_ctrl_env connects the core TL monitor to m_tl_core_reg_predictor_filter,
  // since only it has access to the TL agents.
  uvm_reg_predictor#(tl_seq_item) m_tl_core_reg_predictor;
  tl_reg_adapter#(tl_seq_item)    m_tl_core_reg_adapter;
  rram_ctrl_reg_predictor_filter  m_tl_core_reg_predictor_filter;

  // Completed OTP macro transactions, from the OTP macro agent's monitor.
  uvm_tlm_analysis_fifo #(otp_macro_item) m_otp_macro_fifo;

  // Model of the OTP contents: every OTP word, keyed by OTP word address. It is loaded from the
  // RRAM through the backdoor when the DUT answers Init, then updated by every command.
  bit [otp_ctrl_macro_pkg::OtpWidth-1:0] m_otp_mem[int unsigned];

  // Model of the integrity page: the integrity byte stored for each 64-bit chunk of OTP data
  // (OtpWordsPerChunk words), keyed by chunk index. Write and Zeroize recompute it from the data.
  // WriteRaw leaves it alone, so a Read after a WriteRaw can see a mismatch.
  bit [7:0] m_otp_intg[int unsigned];

  // Set once the DUT has answered Init since the last reset.
  bit m_otp_init_done;

  // Number of OTP words covered by one integrity byte.
  localparam int unsigned OtpWordsPerChunk =
      rram_ctrl_pkg::OtpIntgDataWidth / otp_ctrl_macro_pkg::OtpWidth;

  // Standard SV/UVM methods
  extern function new(string name = "", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);

  // Class specific methods
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  extern task process_tl_core_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
                                     tl_phase_e tl_phase);
  extern function void on_reg_access(tl_seq_item item, tl_phase_e tl_phase, uvm_reg csr);
  extern function void on_mem_access(tl_seq_item item, tl_phase_e tl_phase, uvm_mem memory);
  extern task process_tl_prim_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
                                     tl_phase_e tl_phase);
  extern function void configure_csr_check_exclusions();

  // Checks each completed OTP macro transaction against the OTP model and keeps the model up to
  // date.
  extern task process_otp_macro_fifo();
  extern function void check_otp_macro_item(otp_macro_item item);

  // Loads m_otp_mem and m_otp_intg from the RRAM through the backdoor.
  extern function void load_otp_model();

  // Returns the 64 bits of OTP data in chunk `chunk` from m_otp_mem.
  extern function bit [rram_ctrl_pkg::OtpIntgDataWidth-1:0] get_otp_chunk(int unsigned chunk);

  // Returns the integrity byte the RTL computes for the data in chunk `chunk`.
  extern function bit [7:0] calc_otp_intg(int unsigned chunk);

  // Checks that the RRAM holds what the OTP model says for the words that `item` touched, and
  // the integrity byte of their chunk.
  extern function void check_otp_bkdr(otp_macro_item item);
  extern function void reset(string kind = "HARD");
endclass : rram_ctrl_scoreboard


function rram_ctrl_scoreboard::new(string name = "", uvm_component parent = null);
  super.new(name, parent);
endfunction : new

function void rram_ctrl_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // TODO(#31288): remove once support alert checking
  do_alert_check = 0;

  m_tl_core_reg_predictor = uvm_reg_predictor#(tl_seq_item)::type_id::create(
      "m_tl_core_reg_predictor", this);
  m_tl_core_reg_adapter = tl_reg_adapter#(tl_seq_item)::type_id::create("m_tl_core_reg_adapter");
  m_tl_core_reg_adapter.cfg = cfg.m_tl_agent_cfgs[ral.get_name()];
  m_tl_core_reg_predictor_filter = rram_ctrl_reg_predictor_filter::type_id::create(
      "m_tl_core_reg_predictor_filter", this);
  m_otp_macro_fifo = new("m_otp_macro_fifo", this);
endfunction : build_phase

function void rram_ctrl_scoreboard::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  m_tl_core_reg_predictor.map     = ral.default_map;
  m_tl_core_reg_predictor.adapter = m_tl_core_reg_adapter;
  m_tl_core_reg_predictor_filter.ap.connect(m_tl_core_reg_predictor.bus_in);
  configure_csr_check_exclusions();
endfunction : connect_phase

task rram_ctrl_scoreboard::run_phase(uvm_phase phase);
  super.run_phase(phase);
  fork
    process_otp_macro_fifo();
  join_none
endtask : run_phase

task rram_ctrl_scoreboard::process_otp_macro_fifo();
  forever begin
    otp_macro_item item;
    m_otp_macro_fifo.get(item);
    `uvm_info(`gfn, $sformatf("OTP macro transaction:\n%0s", item.sprint()), UVM_HIGH)
    check_otp_macro_item(item);
  end
endtask : process_otp_macro_fifo

function void rram_ctrl_scoreboard::check_otp_macro_item(otp_macro_item item);
  int unsigned chunk = item.addr / OtpWordsPerChunk;
  bit          clears_bit;

  if (item.cmd == otp_ctrl_macro_pkg::Init) begin
    `DV_CHECK(!m_otp_init_done, "OTP Init answered twice since reset")
    `DV_CHECK_EQ(item.err, otp_ctrl_macro_pkg::NoError)
    m_otp_init_done = 1'b1;
    // No other OTP command can have run since reset, so this is the moment to take a snapshot of
    // what is stored. OTP is non-volatile, so it may still hold data written before the reset.
    load_otp_model();
    return;
  end
  `DV_CHECK(m_otp_init_done, $sformatf("OTP %0s answered before Init", item.cmd.name()))
  if (cfg.en_cov) cov.otp_cmd_cg.sample(item);

  // Every transfer is aligned to its size, so it stays within one integrity chunk.
  `DV_CHECK_EQ_FATAL((item.addr + item.size) / OtpWordsPerChunk, chunk,
                     "OTP transfer crosses an integrity chunk")

  // Would this write try to clear a bit that is already set?
  for (int unsigned k = 0; k <= item.size; k++) begin
    if ((m_otp_mem[item.addr + k] & ~item.get_wdata_word(k)) != '0) clears_bit = 1'b1;
  end

  case (item.cmd)
    otp_ctrl_macro_pkg::Read, otp_ctrl_macro_pkg::ReadRaw: begin
      // Read checks the stored integrity byte against the data, ReadRaw does not.
      bit intg_bad = (item.cmd == otp_ctrl_macro_pkg::Read) &&
                     (calc_otp_intg(chunk) != m_otp_intg[chunk]);
      `DV_CHECK_EQ(item.err, intg_bad ? otp_ctrl_macro_pkg::MacroEccUncorrError :
                                        otp_ctrl_macro_pkg::NoError,
                   $sformatf("%0s error at OTP word 0x%0h", item.cmd.name(), item.addr))
      if (item.err == otp_ctrl_macro_pkg::NoError) begin
        for (int unsigned k = 0; k <= item.size; k++) begin
          `DV_CHECK_EQ(item.get_rdata_word(k), m_otp_mem[item.addr + k],
                       $sformatf("%0s data mismatch at OTP word 0x%0h", item.cmd.name(),
                                 item.addr + k))
        end
      end
      // Words beyond the requested size are not part of the response.
      for (int unsigned k = item.size + 1; k < OtpMacroMaxWords; k++) begin
        `DV_CHECK_EQ(item.get_rdata_word(k), '0,
                     $sformatf("%0s returned data in unused word %0d", item.cmd.name(), k))
      end
    end
    otp_ctrl_macro_pkg::Write, otp_ctrl_macro_pkg::WriteRaw: begin
      // OTP bits can only be set. Trying to clear one is reported, but the set bits are still
      // written.
      `DV_CHECK_EQ(item.err, clears_bit ? otp_ctrl_macro_pkg::MacroWriteBlankError :
                                          otp_ctrl_macro_pkg::NoError,
                   $sformatf("%0s error at OTP word 0x%0h", item.cmd.name(), item.addr))
      for (int unsigned k = 0; k <= item.size; k++) begin
        m_otp_mem[item.addr + k] |= item.get_wdata_word(k);
      end
      if (item.cmd == otp_ctrl_macro_pkg::Write) m_otp_intg[chunk] = calc_otp_intg(chunk);
      check_otp_bkdr(item);
    end
    otp_ctrl_macro_pkg::Zeroize: begin
      `DV_CHECK_EQ(item.err, otp_ctrl_macro_pkg::NoError)
      for (int unsigned k = 0; k <= item.size; k++) begin
        m_otp_mem[item.addr + k] = '1;
        // Zeroize returns the zeroized words.
        `DV_CHECK_EQ(item.get_rdata_word(k), '1,
                     $sformatf("Zeroize returned wrong data for OTP word 0x%0h", item.addr + k))
      end
      m_otp_intg[chunk] = calc_otp_intg(chunk);
      check_otp_bkdr(item);
    end
    default: `uvm_error(`gfn, $sformatf("Unexpected OTP command %0s", item.cmd.name()))
  endcase
endfunction : check_otp_macro_item

function void rram_ctrl_scoreboard::load_otp_model();
  for (int unsigned addr = 0; addr < otp_ctrl_macro_pkg::OtpDepth; addr++) begin
    m_otp_mem[addr] = cfg.m_otp_bkdr.read16(addr * 2);
  end
  for (int unsigned chunk = 0; chunk < otp_ctrl_macro_pkg::OtpDepth / OtpWordsPerChunk;
       chunk++) begin
    m_otp_intg[chunk] = cfg.m_otp_bkdr.read_intg(chunk * OtpWordsPerChunk * 2);
  end
endfunction : load_otp_model

function bit [rram_ctrl_pkg::OtpIntgDataWidth-1:0] rram_ctrl_scoreboard::get_otp_chunk(
    int unsigned chunk);
  bit [rram_ctrl_pkg::OtpIntgDataWidth-1:0] data;
  for (int unsigned k = 0; k < OtpWordsPerChunk; k++) begin
    data[k * otp_ctrl_macro_pkg::OtpWidth +: otp_ctrl_macro_pkg::OtpWidth] =
        m_otp_mem[chunk * OtpWordsPerChunk + k];
  end
  return data;
endfunction : get_otp_chunk

function bit [7:0] rram_ctrl_scoreboard::calc_otp_intg(int unsigned chunk);
  bit [71:0] enc = prim_secded_pkg::prim_secded_hamming_72_64_enc(get_otp_chunk(chunk));
  return enc[71:64];
endfunction : calc_otp_intg

function void rram_ctrl_scoreboard::check_otp_bkdr(otp_macro_item item);
  int unsigned chunk = item.addr / OtpWordsPerChunk;
  for (int unsigned k = 0; k <= item.size; k++) begin
    int unsigned addr = item.addr + k;
    `DV_CHECK_EQ(cfg.m_otp_bkdr.read16(addr * 2), m_otp_mem[addr],
                 $sformatf("RRAM holds the wrong data for OTP word 0x%0h", addr))
  end
  `DV_CHECK_EQ(cfg.m_otp_bkdr.read_intg(item.addr * 2), m_otp_intg[chunk],
               $sformatf("RRAM holds the wrong integrity byte for OTP chunk %0d", chunk))
endfunction : check_otp_bkdr

function void rram_ctrl_scoreboard::configure_csr_check_exclusions();
  uvm_reg regs[$];

  // uvm_reg_predictor::write() checks read data against the mirror before do_predict()
  // overwrites it, so this catches real mismatches unlike a scoreboard-side check. Suppress
  // the compare wherever a CsrExclCheck exclusion applies (fields the RAL can never predict).
  ral.default_map.set_check_on_read(1);
  ral.get_registers(regs);
  foreach (regs[i]) begin
    uvm_reg_field flds[$];
    csr_excl_item reg_excl = csr_utils_pkg::get_excl_item(regs[i]);
    bit reg_excluded = (reg_excl != null) && reg_excl.is_excl(regs[i], CsrExclCheck,
                                                               CsrAllTests);
    regs[i].get_fields(flds);
    foreach (flds[j]) begin
      csr_excl_item fld_excl = csr_utils_pkg::get_excl_item(flds[j]);
      bit fld_excluded = reg_excluded || ((fld_excl != null) &&
          fld_excl.is_excl(flds[j], CsrExclCheck, CsrAllTests));
      if (fld_excluded) flds[j].set_compare(UVM_NO_CHECK);
    end
  end
endfunction : configure_csr_check_exclusions

task rram_ctrl_scoreboard::process_tl_access(tl_seq_item item, tl_channels_e channel,
                                             string ral_name);
  bit            write = item.is_write();
  uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
  tl_phase_e     tl_phase;

  if (!write && channel == AddrChannel) begin
    tl_phase = AddrRead;
  end
  if (write && channel == AddrChannel) begin
    tl_phase = AddrWrite;
  end
  if (!write && channel == DataChannel) begin
    tl_phase = DataRead;
  end
  if (write && channel == DataChannel) begin
    tl_phase = DataWrite;
  end

  if (ral_name == ral.get_name()) begin
    process_tl_core_access(item, csr_addr, tl_phase);
  end else if (ral_name == cfg.prim_ral_name) begin
    process_tl_prim_access(item, csr_addr, tl_phase);
  end else if (ral_name == cfg.host_ral_name) begin
    // TODO(#31289): predict tl errors based on mp configuration.
  end else begin
    `uvm_fatal(`gfn, $sformatf("Specified RAL name %0s doesn't exist!", ral_name))
  end
endtask : process_tl_access

task rram_ctrl_scoreboard::process_tl_core_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
                                                  tl_phase_e tl_phase);
  if (is_mem_addr(item.a_addr, ral)) begin
    on_mem_access(item, tl_phase, ral.default_map.get_mem_by_offset(csr_addr));
  end else begin
    uvm_reg csr = ral.default_map.get_reg_by_offset(csr_addr);
    if (csr != null) begin
      on_reg_access(item, tl_phase, csr);
    end else begin
      // predict_tl_err() already checks unmapped accesses and returns early before
      // process_tl_access is even called, so this should be unreachable: a scoreboard bug,
      // not an RTL one.
      `uvm_fatal(`gfn, $sformatf("Unreachable: access to unmapped addr 0x%0h", csr_addr))
    end
  end
endtask : process_tl_core_access

function void rram_ctrl_scoreboard::on_reg_access(tl_seq_item item, tl_phase_e tl_phase,
                                                  uvm_reg csr);
  // Prediction and the read-value check both happen automatically via
  // m_tl_core_reg_predictor (see configure_csr_check_exclusions()). Fields excluded from that
  // check (tagged CsrExclCheck, e.g. PHY_STATUS.init_done) get no check at all today.
  // TODO(#31290): add targeted checks here for those excluded fields.
endfunction : on_reg_access

function void rram_ctrl_scoreboard::on_mem_access(tl_seq_item item, tl_phase_e tl_phase,
                                                  uvm_mem memory);
  // TODO(#31291): track wr_fifo/rd_fifo occupancy and cross-check against fifo_lvl/curr_fifo_lvl.
endfunction : on_mem_access

task rram_ctrl_scoreboard::process_tl_prim_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
                                                  tl_phase_e tl_phase);
  // TODO(#31292): generate traffic for this tlul interface and test it here.
endtask : process_tl_prim_access

function void rram_ctrl_scoreboard::reset(string kind = "HARD");
  super.reset(kind);
  // Reset local fifos queues and variables
  m_otp_macro_fifo.flush();
  // OTP is non-volatile, so its contents survive the reset. load_otp_model() takes a fresh
  // snapshot when the DUT answers the next Init, which also catches a write that the reset
  // interrupted.
  m_otp_init_done = 1'b0;
endfunction : reset

function void rram_ctrl_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
  // Post test checks: ensure that all local fifos and queues are empty
  `DV_CHECK_EQ(m_otp_macro_fifo.used(), 0, "OTP macro transactions were left unchecked")
endfunction : check_phase
