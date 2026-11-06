// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`uvm_analysis_imp_decl(_key_txn)
`uvm_analysis_imp_decl(_reg_item)

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

  // An implementation port that tracks keys sent from otp_ctrl
  uvm_analysis_imp_key_txn #(otp_key_rsp_seq_item, rram_ctrl_scoreboard) m_otp_key_txn_imp;

  // An implementation port that will subscribe to m_tl_core_reg_predictor. This receives items on
  // any read or write accessing a register if the access does not give an error response.
  //
  // Error responses and memory accesses are handled separately (see functions called by
  // process_tl_access).
  uvm_analysis_imp_reg_item #(uvm_reg_item, rram_ctrl_scoreboard) m_reg_item_imp;

  // A count of the number of keys that have been read from otp_ctrl since the last reset. We expect
  // this to count up to two (and no further) and to get to two before init_done is asserted.
  int unsigned m_otp_key_count;

  // True if we have read the STATUS register with init_done=1 since the last reset
  bit          m_seen_init_done;

  // Standard SV/UVM methods
  extern function new(string name = "", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
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
  extern function void reset(string kind = "HARD");

  // The write function for m_otp_key_txn_imp. This is called every time the monitor sees a complete
  // key transaction passing a key back from otp_ctrl.
  extern function void write_key_txn(otp_key_rsp_seq_item item);

  // The write function for m_reg_item_imp. This is called after every read or write that accesses a
  // register and doesn't give an error response (so the underlying register transaction actually
  // happened).
  extern function void write_reg_item(uvm_reg_item item);
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

  m_otp_key_txn_imp = new("m_otp_key_txn_imp", this);
  m_reg_item_imp = new("m_reg_item_imp", this);
endfunction : build_phase

function void rram_ctrl_scoreboard::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  m_tl_core_reg_predictor.map     = ral.default_map;
  m_tl_core_reg_predictor.adapter = m_tl_core_reg_adapter;
  m_tl_core_reg_predictor_filter.ap.connect(m_tl_core_reg_predictor.bus_in);

  m_tl_core_reg_predictor.reg_ap.connect(m_reg_item_imp);

  configure_csr_check_exclusions();
endfunction : connect_phase

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

  m_otp_key_count = 0;
  m_seen_init_done = 0;
endfunction : reset

function void rram_ctrl_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
  // Post test checks: ensure that all local fifos and queues are empty
endfunction : check_phase

function void rram_ctrl_scoreboard::write_key_txn(otp_key_rsp_seq_item item);
  // Check that we haven't already seen two otp keys since the last reset. That would mean that
  // rram_ctrl had requested a third.
  if (m_otp_key_count >= 2) begin
    `uvm_error("extra_otp_key",
               $sformatf("Seen an extra OTP key transaction (now seen %0d)", m_otp_key_count + 1))
  end

  m_otp_key_count++;
endfunction

function void rram_ctrl_scoreboard::write_reg_item(uvm_reg_item item);
  import prim_mubi_pkg::MuBi4False;

  if (item.kind == UVM_READ) begin
    // This is a read of a register. For many registers, m_tl_core_reg_predictor will check that the
    // rdata matches the prediction. This has been disabled for fields that won't match the register
    // model by calling configure_csr_check_exclusions. Make checks for some of those fields here.
    case (item.element.get_name())
      "status": begin
        // The init_done and keys_valid fields of the STATUS register are updated by the hardware.
        // The predictions are updated in the register model when they are read, but there is no
        // automatic check.
        //
        // Checks that we can make:
        //
        //   1. keys_valid is only set after there has been some key data from OTP (so
        //      m_otp_key_count > 0).
        //
        //   2. init_done will only be set when we've seen two key transactions (with the data
        //      and addr keys).
        //
        //   3. init_done is "one way": It won't initially be set, but it never gets cleared without
        //      a reset.
        //
        //   4. keys_valid is set before init_done. As such, we'd normally expect it to be true if
        //      init_done is true. The only way this can not be true is if rram_ctrl is disabled
        //      (either by an LC escalation or a write that sets the DIS.SW_DIS field).
        //
        bit keys_valid = (item.value[0] >> ral.status.keys_valid.get_lsb_pos()) & 1;
        bit init_done  = (item.value[0] >> ral.status.init_done.get_lsb_pos()) & 1;

        // Item 1 above
        if (keys_valid && m_otp_key_count == 0) begin
          `uvm_error("keys_valid_early", "Read STATUS.keys_valid=1 before any key sent from OTP.")
        end

        // Item 2 above
        if (init_done && m_otp_key_count < 2) begin
          `uvm_error("init_done_early",
                     $sformatf("Read STATUS.init_done=1 but the number of OTP keys seen is %0d.",
                               m_otp_key_count))
        end

        // Item 3 above
        if (m_seen_init_done && !init_done) begin
          `uvm_error("init_done_clear", "Read STATUS.init_done=0 after seeing it set.")
        end
        m_seen_init_done |= init_done;

        // Item 4 above
        if (init_done) begin
          bit exp_keys_valid = 1;

          // If DIS.SW_DIS has been set, then keys_valid should be false.
          if (ral.dis.sw_dis.get_mirrored_value() != MuBi4False) exp_keys_valid = 0;

          // If there has been an LC escalation, keys_valid should be false.
          //
          // TODO(#32226): lc_ctrl inputs to rram_ctrl are not yet tracked in the testbench.

          if (keys_valid != exp_keys_valid) begin
            `uvm_error("keys_valid_wrong",
                       $sformatf("Read STATUS.keys_valid=%0d, but we expected it to be %0d.",
                                 keys_valid, exp_keys_valid))
          end
        end
      end
    endcase
  end
endfunction
