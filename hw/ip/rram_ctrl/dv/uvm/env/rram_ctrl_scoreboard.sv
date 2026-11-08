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
  uvm_analysis_imp_key_txn #(nvm_otp_key_rsp_seq_item, rram_ctrl_scoreboard) m_otp_key_txn_imp;

  // An implementation port that will subscribe to m_tl_core_reg_predictor. This receives items on
  // any read or write accessing a register if the access does not give an error response.
  //
  // Error responses and memory accesses are handled separately (see functions called by
  // process_tl_access).
  uvm_analysis_imp_reg_item #(uvm_reg_item, rram_ctrl_scoreboard) m_reg_item_imp;

  // Has a data / addr key been read from otp_ctrl since the last reset?
  local bit m_seen_otp_data_key, m_seen_otp_addr_key;

  // True if we have read the STATUS register with init_done=1 since the last reset
  local bit m_seen_init_done;

  // True if we have seen a local escalation since the last reset.
  local bit m_seen_local_esc;

  // True if we have seen DIS.SW_DIS written with a value other than MuBi4False.
  local bit m_seen_sw_dis;

  // A window of time (counting register accesses) that counts down from when DIS.SW_DIS is first
  // predicted not to be MuBi4False.
  //
  // Waiting for this window avoids a potential problem where disabling RRAM races with the next
  // access. Since we don't want to specify the precise timing of when the disable takes effect,
  // this window allows the scoreboard to represent a "might be disabled" period.
  local int unsigned m_dis_sw_window_counter;

  // A reg callbacks object that we register with particular register model fields, causing the
  // scoreboard to know about reads/writes/predictions
  rram_ctrl_reg_cbs m_cbs;

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
  extern function void reset(string kind = "HARD");

  // The write function for m_otp_key_txn_imp. This is called every time the monitor sees a complete
  // key transaction passing a key back from otp_ctrl.
  extern function void write_key_txn(nvm_otp_key_rsp_seq_item item);

  // The write function for m_reg_item_imp. This is called after every read or write that accesses a
  // register and doesn't give an error response (so the underlying register transaction actually
  // happened).
  extern function void write_reg_item(uvm_reg_item item);

  // Called on every write to the DIS register
  //
  // This tracks when DIS.SW_DIS is written with a value other than MuBi4False for the first time
  // (causing RRAM to be disabled).
  extern local function void on_dis_write(uvm_reg_data_t wdata);

  // Register each field of the given register with m_cbs
  //
  // One side effect is that m_cbs will implement the "read data check" that uvm_reg_predictor
  // normally does. This means that it can use m_cbs's more up-to-date prediction of the field
  // value. As such, we also disable the check in uvm_reg_predictor that we have superseded.
  extern local function void add_cbs_for_reg(uvm_reg register);

  // Called on a read of the STATUS register
  //
  // This function performs a set of consistency checks about the read data:
  //
  //   1. keys_valid and init_done are only set after there has been some key data from OTP
  //      (so m_seen_otp_data_key and m_seen_otp_addr_key are true).
  //
  //   2. init_done is "one way": It won't initially be set, but it never gets cleared without
  //      a reset.
  //
  //   3. keys_valid is set before init_done. As such, we'd normally expect it to be true if
  //      init_done is true. The only way this can not be true is if rram_ctrl is disabled.
  //      Ways this can happen:
  //
  //        - An LC RMA transition / global escalation
  //        - A local escalation (visible in FAULT_STATUS / STD_FAULT_STATUS)
  //        - A write that sets the DIS.SW_DIS field)
  extern local function void on_status_read(uvm_reg_data_t rdata);

  // Check that a particular field of STATUS is only true after a particular OTP key has been seen.
  //
  // This should be called (by on_status_read) when observing a register transaction from reading
  // STATUS.
  //
  // Arguments:
  //
  //    - status_fld_value: The value that has just been read
  //    - status_fld_name:  The name of the field in STATUS
  //    - otp_key_flag:     A flag showing whether an OTP key has been seen.
  //    - otp_key_desc:     A description of that OTP key
  extern local function void check_status_fld_needs_key(bit    status_fld_value,
                                                        string status_fld_name,
                                                        bit    otp_key_flag,
                                                        string otp_key_desc);
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

  m_cbs = rram_ctrl_reg_cbs::type_id::create("m_cbs");

  m_reg_item_imp = new("m_reg_item_imp", this);
endfunction : build_phase

function void rram_ctrl_scoreboard::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  m_tl_core_reg_predictor.map     = ral.default_map;
  m_tl_core_reg_predictor.adapter = m_tl_core_reg_adapter;
  m_tl_core_reg_predictor_filter.ap.connect(m_tl_core_reg_predictor.bus_in);

  m_tl_core_reg_predictor.reg_ap.connect(m_reg_item_imp);

  configure_csr_check_exclusions();

  // Connect m_cbs to all the register fields it's tracking. These are:
  //
  //  - Fields that might be written by the hardware, where we might want to update a prediction at
  //    a time when the field's register is busy.
  //
  //  - Fields that have an effect that needs tracking in the scoreboard when they change (so the
  //    callback needs to call a callback function inside the scoreboard).
  add_cbs_for_reg(ral.ctrl_regwen);
  add_cbs_for_reg(ral.control);
  add_cbs_for_reg(ral.op_status);
  add_cbs_for_reg(ral.status);
  add_cbs_for_reg(ral.err_code);
  add_cbs_for_reg(ral.std_fault_status);
  add_cbs_for_reg(ral.fault_status);
  add_cbs_for_reg(ral.err_addr);
  add_cbs_for_reg(ral.corr1_err_cnt);
  add_cbs_for_reg(ral.corr2_err_cnt);
  add_cbs_for_reg(ral.corr1_err_loc);
  add_cbs_for_reg(ral.corr2_err_loc);
  add_cbs_for_reg(ral.phy_status);
  add_cbs_for_reg(ral.curr_fifo_lvl);
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

  m_cbs.on_reset();

  m_seen_otp_data_key = 0;
  m_seen_otp_addr_key = 0;
  m_seen_init_done = 0;
  m_seen_local_esc = 0;
  m_seen_sw_dis = 0;
  m_dis_sw_window_counter = 0;
endfunction : reset

task rram_ctrl_scoreboard::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    m_cbs.clean_write_queue();
  join_none
endtask

function void rram_ctrl_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
  // Post test checks: ensure that all local fifos and queues are empty
endfunction : check_phase

function void rram_ctrl_scoreboard::write_key_txn(nvm_otp_key_rsp_seq_item item);
  // Check that the returned key hasn't already been seen since the last reset (rram_ctrl should
  // only request each once)
  if (item.m_req.m_is_data_req ? m_seen_otp_data_key : m_seen_otp_addr_key) begin
    `uvm_error("extra_otp_key",
               $sformatf("Have already seen an OTP transaction for the %0s key.",
                         item.m_req.m_is_data_req ? "data" : "addr"))
  end

  if (item.m_req.m_is_data_req) m_seen_otp_data_key = 1;
  else                          m_seen_otp_addr_key = 1;
endfunction

function void rram_ctrl_scoreboard::write_reg_item(uvm_reg_item item);
  case (item.kind)
    UVM_READ: begin
      // This is a read of a register. For many registers, m_tl_core_reg_predictor will check that
      // the rdata matches the prediction. This has been disabled for fields that won't match the
      // register model by calling configure_csr_check_exclusions. Make checks for some of those
      // fields here.

      if (item.element == ral.status) on_status_read(item.value[0]);
    end

    UVM_WRITE: begin
      // This is a write to a register.

      if (item.element == ral.dis) on_dis_write(item.value[0]);
    end
  endcase

  // Update m_dis_sw_window_counter to reflect the register transaction that we've just seen
  if (m_dis_sw_window_counter > 0) m_dis_sw_window_counter -= 1;
endfunction

function void rram_ctrl_scoreboard::on_dis_write(uvm_reg_data_t wdata);
  import prim_mubi_pkg::MuBi4False;

  bit [3:0] sw_dis_wdata = (wdata >> ral.dis.sw_dis.get_lsb_pos());

  // If this is a value other than MuBi4False then this is disabling RRAM. If this is the first time
  // it has happened, set a timer (which allows other transactions to be sure about whether RRAM was
  // disabled when they started).
  if (sw_dis_wdata != MuBi4False && !m_seen_sw_dis) begin
    // Set the window counter to 1, so the next call to write_reg_item will be considered part of
    // the window.
    m_dis_sw_window_counter = 1;
    m_seen_sw_dis = 1;
  end
endfunction

function void rram_ctrl_scoreboard::add_cbs_for_reg(uvm_reg register);
  uvm_reg_field fields[$];
  register.get_fields(fields);
  foreach (fields[i]) begin
    uvm_reg_field_cb::add(fields[i], m_cbs);

    // Tell uvm_reg_predictor not to check the value of the field on reads. m_cbs will do the
    // check instead.
    if (fields[i].get_compare() == UVM_CHECK) begin
      m_cbs.enable_field_rdata_check(fields[i]);
      fields[i].set_compare(UVM_NO_CHECK);
    end
  end
endfunction

function void rram_ctrl_scoreboard::on_status_read(uvm_reg_data_t rdata);
  import prim_mubi_pkg::MuBi4False;

  bit keys_valid = (rdata >> ral.status.keys_valid.get_lsb_pos()) & 1;
  bit init_done  = (rdata >> ral.status.init_done.get_lsb_pos()) & 1;

  // Item 1 in the list of checks above the function declaration
  check_status_fld_needs_key(keys_valid, "keys_valid", m_seen_otp_addr_key, "an addr key");
  check_status_fld_needs_key(keys_valid, "keys_valid", m_seen_otp_data_key, "a data key");
  check_status_fld_needs_key(init_done, "init_done", m_seen_otp_addr_key, "an addr key");
  check_status_fld_needs_key(init_done, "init_done", m_seen_otp_data_key, "a data key");

  // Item 2 above function declaration
  if (m_seen_init_done && !init_done) begin
    `uvm_error("init_done_clear", "Read STATUS.init_done=0 after seeing it set.")
  end
  m_seen_init_done |= init_done;

  // Item 3 above function declaration
  if (init_done) begin
    bit exp_keys_valid = 1;
    bit keys_valid_pred_unsure = 0;

    // If there has been an LC escalation, keys_valid should be false.
    //
    // TODO(#32226): lc_ctrl inputs to rram_ctrl are not yet tracked in the testbench.

    // A local escalation would disable RRAM, which also causes keys_valid to be false.
    if (m_seen_local_esc) begin
      exp_keys_valid = 0;
    end

    // If DIS.SW_DIS isn't MuBi4False (true as soon as we have seen a write of any other value),
    // then keys_valid should be false.
    //
    // If m_sw_dis_window_counter is nonzero then DIS.SW_DIS has just been set. If exp_keys_valid is
    // currently true (because no LC signal or local escalation has cleared it) but DIS.SW_DIS is
    // set to disable RRAM then we are in a tiny window that races against the disable. Set
    // keys_valid_pred_unsure, which will mean we don't test the value.
    if (m_seen_sw_dis) begin
      if (m_dis_sw_window_counter && exp_keys_valid) keys_valid_pred_unsure = 1;
      exp_keys_valid = 0;
    end

    if (keys_valid != exp_keys_valid && !keys_valid_pred_unsure) begin
      `uvm_error("keys_valid_wrong",
                 $sformatf("Read STATUS.keys_valid=%0d, but we expected it to be %0d.",
                           keys_valid, exp_keys_valid))
    end
  end
endfunction

function void rram_ctrl_scoreboard::check_status_fld_needs_key(bit    status_fld_value,
                                                               string status_fld_name,
                                                               bit    otp_key_flag,
                                                               string otp_key_desc);
  if (status_fld_value && !otp_key_flag) begin
    `uvm_error("status_early",
               $sformatf("Read STATUS.%0s = 1 but have not seen %0s.",
                         status_fld_name, otp_key_desc))
  end
endfunction
