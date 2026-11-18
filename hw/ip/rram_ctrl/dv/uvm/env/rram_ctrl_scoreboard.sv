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

  // The data / addr key itself (valid if m_seen_otp_data_key / m_seen_otp_addr_key is true)
  local bit [NvmKeyWidth-1:0] m_otp_data_key, m_otp_addr_key;

  // True if we have read the STATUS register with init_done=1 since the last reset
  local bit m_seen_init_done;

  // True if we have seen a local escalation since the last reset.
  local bit m_seen_local_esc;

  // True if we have seen DIS.SW_DIS written with a value other than MuBi4False.
  local bit m_seen_sw_dis;

  // An associative array that tracks which registers need special handling in on_reg_access. This
  // array is populated in build_phase by make_reg_access_tracks_reg() and is used in on_reg_access.
  //
  // Having an explicit array like this allows on_reg_access to fail with an error if there is an
  // access to a register that the DV team forgot to model in the scoreboard.
  local bit m_explicitly_track_reg[uvm_reg];

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

  // Backdoor utilities for the data and info partitions. Set these with set_backdoors().
  local rram_ctrl_bkdr_util m_data_bkdr_util;
  local rram_ctrl_bkdr_util m_info_bkdr_util;

  // True if we have taken memory snapshots through both backdoor utilities
  local bit m_have_bkdr_snapshot;

  // A model of the data partition in RRAM
  local rram_partition_model m_data_partition;

  // A model of the info partition in RRAM
  local rram_partition_model m_info_partition;

  // An associative array of generations in m_data_partition that have been taken at the start of
  // host_tl read operations. These are keyed by the TL sequence item's a_source value, which can be
  // used to look up the generation when the response comes back.
  local int unsigned m_host_start_gens[int unsigned];

  // Standard SV/UVM methods
  extern function new(string name = "", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);

  // Provide backdoor utilities for the two different partitions. This should be called before
  // build_phase.
  extern function void set_backdoors(rram_ctrl_bkdr_util data_bkdr,
                                     rram_ctrl_bkdr_util info_bkdr);

  // Check whether a memory access is allowed, or whether it should trigger a TL error.
  //
  // This extends cip_base_scoreboard::is_tl_mem_access_allowed, teaching it about disallowed
  // host_tl accesses.
  extern protected virtual
  function bit is_tl_mem_access_allowed(tl_seq_item       item,
                                        dv_base_reg_block block,
                                        output bit        mem_byte_access_err,
                                        output bit        mem_wo_err,
                                        output bit        mem_ro_err,
                                        output bit        custom_err);

  // Other class-specific methods
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  extern task process_tl_core_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
                                     tl_phase_e tl_phase);

  // A call-back run by process_tl_core_access when it sees a read to or write from a register.
  //
  // This function checks rdata for reads from registers and reacts to writes to control registers.
  //
  // * The rdata check:
  //
  //     For most registers, prediction and the read-value check are run by m_tl_core_reg_predictor.
  //     Some fields are excluded for that check (see configure_csr_check_exclusions()) because
  //     their value can be changed by the hardware.
  //
  //     Reads of those fields get checked in this function.
  //
  // * Writes to control registers:
  //
  //     This function also reacts to writes to registers that cause the block to take a specific
  //     action. For example, writing to the CONTROL register (to configure or start on operation).
  extern local function void on_reg_access(tl_seq_item item, tl_phase_e tl_phase, uvm_reg csr);

  extern function void on_mem_access(tl_seq_item item, tl_phase_e tl_phase, uvm_mem memory);
  extern task process_tl_prim_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
                                     tl_phase_e tl_phase);

  // Called when monitor sees an A- or D-channel item on the host_tl interface which wasn't expected
  // to cause d_error=1 in the D-channel response.
  extern local function void on_allowed_host_item(cip_tl_seq_item item, tl_channels_e channel);

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

  // Return true if the given page is in a region that is enabled
  //
  // If so, writes the index of the first enabled region containing the page to the region_idx
  // output variable.
  extern local function bit page_in_enabled_region(int unsigned        page_idx,
                                                   output int unsigned region_idx);

  // Return true if the given RRAM word in the data partition is scrambled (either by an enabled
  // region or by default_region).
  extern local function bit data_word_scrambled(int unsigned word_idx);

  // Return the modelled value of the given word in the data partition, unscrambling if
  // data_word_scrambled() is true.
  extern local function bit [DataWidth-1:0] get_data_value(int unsigned word_idx);

  // Populate the m_explicitly_track_reg associative array, which on_reg_access will use to track
  // whether it needs to directly reason about access to a given register.
  extern local function void make_explicitly_track_reg();
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

  m_data_partition = rram_partition_model::type_id::create("m_data_partition", this);
  m_data_partition.set_size_words(NumDataPages * WordsPerPage);

  m_info_partition = rram_partition_model::type_id::create("m_info_partition", this);
  m_info_partition.set_size_words(NumInfoPages * WordsPerPage);

  make_explicitly_track_reg();
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

task rram_ctrl_scoreboard::run_phase(uvm_phase phase);
  // Check that we really have got backdoor utilities. Although the utilities must exist now, we
  // won't actually snapshot the contents of the memory until the end of reset. This avoids a race
  // between the snapshot and randomisation that happens at the start of rram_ctrl_base_test.
  if (m_data_bkdr_util == null || m_info_bkdr_util == null) begin
    `uvm_fatal("missing_bkdr",
               {"The data and info backdoors have not both been set. ",
                "Call set_backdoors before start of run_phase."})
  end

  fork
    super.run_phase(phase);
    m_cbs.clean_write_queue();
  join_none
endtask

function void rram_ctrl_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
  // Post test checks: ensure that all local fifos and queues are empty
endfunction : check_phase

function void rram_ctrl_scoreboard::set_backdoors(rram_ctrl_bkdr_util data_bkdr,
                                                  rram_ctrl_bkdr_util info_bkdr);
  m_data_bkdr_util = data_bkdr;
  m_info_bkdr_util = info_bkdr;
endfunction

function bit rram_ctrl_scoreboard::is_tl_mem_access_allowed(tl_seq_item       item,
                                                            dv_base_reg_block block,
                                                            output bit        mem_byte_access_err,
                                                            output bit        mem_wo_err,
                                                            output bit        mem_ro_err,
                                                            output bit        custom_err);
  bit allowed;
  cip_tl_seq_item cip_item;

  allowed = super.is_tl_mem_access_allowed(item, block,
                                           mem_byte_access_err, mem_wo_err, mem_ro_err, custom_err);

  if (!$cast(cip_item, item)) begin
    `uvm_fatal("not_cip_item", "Sequence item can't be cast to a cip_tl_seq_item")
  end

  if (block == cfg.ral_models[cfg.host_ral_name]) begin
    // This memory access is on the host_tl interface.

    string error_reasons[$];

    if (item.is_write()) begin
      // Writes should always be rejected with an error.
      error_reasons.push_back("write to tl_host interface");
    end else begin
      // Reasons that a read might be blocked:
      //
      //  - The page touched by the read might be in the OTP region
      //
      //  - The page touched by the read is included in one or more enabled regions and the first
      //    one of those regions has rd_en != MuBi4True.
      //
      //  - The page touched by the read is not included in any enabled region and the default
      //    region has rd_en != MuBi4True
      //
      //  - TODO: Emulated info pages
      //
      //  - The instr_type field is MuBi4True but the EXEC register isn't ExecEn
      //
      //  - TileLink protocol problem (integrity, alignment), but this has already been checked by
      //  the base class version of this function.
      uvm_reg_map host_map = cfg.ral_models[cfg.host_ral_name].get_default_map();
      uvm_reg_addr_t host_base_addr = host_map.get_base_addr();
      int unsigned page_idx = (item.a_addr - host_base_addr) / rram_ctrl_reg_pkg::BytesPerPage;
      int unsigned region_idx;

      if (page_idx >= OtpStartPage) begin
        error_reasons.push_back("addressed page in OTP region");
      end

      if (page_in_enabled_region(page_idx, region_idx)) begin
        // The first enabled region in the data partition that includes page is the one at position
        // region_idx. The read will be blocked if that region's rd_en is not MuBi4True.
        if (ral.mp_region_cfg[region_idx].rd_en.get_mirrored_value() != MuBi4True) begin
          error_reasons.push_back($sformatf("region %0d has rd_en != MuBi4True", region_idx));
        end
      end else begin
        // There is no enabled region in the data that includes page. The read will be blocked if
        // default_region.rd_en is not MuBi4True.
        if (ral.default_region.rd_en.get_mirrored_value() != MuBi4True) begin
          error_reasons.push_back("default_region has rd_en != MuBi4True");
        end
      end

      if (cip_item.get_instr_type() == MuBi4True &&
          ral.exec.get_mirrored_value() != rram_ctrl_reg_pkg::ExecEn) begin
        error_reasons.push_back("fetch and EXEC is not ExecEn");
      end
    end

    if (error_reasons.size()) begin
      // There is at least one reason that the access should have been blocked. Set custom_err=1
      // and allowed=0.
      //
      // As a debugging aid, print the list of error reasons at UVM_HIGH (the same verbosity as an
      // equivalent print in cip_base_scoreboard::is_tl_mem_access_allowed).
      custom_err = 1;
      allowed = 0;

      `uvm_info("host_tl_pred_err",
                $sformatf("Predicted d_error for host_tl access. Reasons: %0p.", error_reasons),
                UVM_HIGH)
    end
  end

  return allowed;
endfunction

task rram_ctrl_scoreboard::process_tl_access(tl_seq_item item, tl_channels_e channel,
                                             string ral_name);
  bit             write = item.is_write();
  uvm_reg_addr_t  csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
  tl_phase_e      tl_phase;
  cip_tl_seq_item cip_item;

  if (!$cast(cip_item, item)) begin
    `uvm_fatal("not_cip_item", "Sequence item can't be cast to a cip_tl_seq_item")
  end

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
    on_allowed_host_item(cip_item, channel);
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
  // Figure out whether this register is known to be tracked outside fully by
  // m_tl_core_reg_predictor (see comments in make_explicitly_track_reg for careful reasoning about
  // the different registers' values in m_explicitly_track_reg).
  if (!m_explicitly_track_reg.exists(csr)) begin
    `uvm_fatal("unknown_reg",
               $sformatf({"Access to register %0s, which is known to the register model but was ",
                          "not added to m_explicitly_track_reg by make_explicitly_track_reg."},
                         csr.get_name()))
  end
  if (!m_explicitly_track_reg[csr]) begin
    // This register is known to be tracked appropriately by standard register prediction and rdata
    // checks in m_tl_core_reg_predictor. Nothing to do here.
    return;
  end

  if (csr == ral.init) begin
    // TODO(#31290): The action of writing to INIT.VAL is not currently modelled in the scoreboard.
  end else if (csr == ral.ctrl_regwen) begin
    // TODO(#31290): rdata is not currently predicted for CTRL_REGWEN.
  end else if (csr == ral.control) begin
    // TODO(#31290): The action of writing to CONTROL is not currently modelled in the scoreboard.
  end else if (csr == ral.op_status) begin
    // TODO(#31290): rdata is not currently predicted for OP_STATUS.
  end else if (csr == ral.status) begin
    // TODO(#31290): rdata is not currently predicted for STATUS.
  end else if (csr == ral.err_code) begin
    // TODO(#31290): rdata is not currently predicted for ERR_CODE.
  end else if (csr == ral.std_fault_status) begin
    // TODO(#31290): rdata is not currently predicted for STD_FAULT_STATUS.
  end else if (csr == ral.fault_status) begin
    // TODO(#31290): rdata is not currently predicted for FAULT_STATUS.
  end else if (csr == ral.err_addr) begin
    // TODO(#31290): rdata is not currently predicted for ERR_ADDR.
  end else if (csr == ral.corr1_err_cnt) begin
    // TODO(#31290): rdata is not currently predicted for CORR1_ERR_CNT.
  end else if (csr == ral.corr2_err_cnt) begin
    // TODO(#31290): rdata is not currently predicted for CORR2_ERR_CNT.
  end else if (csr == ral.corr1_err_loc) begin
    // TODO(#31290): rdata is not currently predicted for CORR1_ERR_LOC.
  end else if (csr == ral.corr2_err_loc) begin
    // TODO(#31290): rdata is not currently predicted for CORR2_ERR_LOC.
  end else if (csr == ral.phy_status) begin
    // TODO(#31290): rdata is not currently predicted for PHY_STATUS.
  end else if (csr == ral.fifo_lvl) begin
    // TODO(#31290): rdata is not currently predicted for FIFO_LVL.
  end else if (csr == ral.fifo_clr) begin
    // TODO(#31290): Side effects of writing FIFO_CLR are not currently modelled.
  end else if (csr == ral.curr_fifo_lvl) begin
    // TODO(#31290): rdata is not currently predicted for CURR_FIFO_LVL.
  end else begin
    // If we get here then a register has been added to the m_explicitly_track_reg array with a
    // value of 1, but was not added to this function. Oops...
    `uvm_fatal("unknown_reg",
               $sformatf({"m_explicitly_track_reg[%0s] = 1 but the register ",
                          "is not known to on_reg_access."},
                         csr.get_name()))
  end
endfunction : on_reg_access

function void rram_ctrl_scoreboard::on_mem_access(tl_seq_item item, tl_phase_e tl_phase,
                                                  uvm_mem memory);
  // TODO(#31291): track wr_fifo/rd_fifo occupancy and cross-check against fifo_lvl/curr_fifo_lvl.
endfunction : on_mem_access

task rram_ctrl_scoreboard::process_tl_prim_access(tl_seq_item item, uvm_reg_addr_t csr_addr,
                                                  tl_phase_e tl_phase);
  // TODO(#31292): generate traffic for this tlul interface and test it here.
endtask : process_tl_prim_access

function void rram_ctrl_scoreboard::on_allowed_host_item(cip_tl_seq_item item,
                                                         tl_channels_e channel);
  // This is an access on the host_tl interface that isn't expected to cause an error (otherwise
  // is_tl_mem_access_allowed would have returned false, causing cip_base_scoreboard::predict_tl_err
  // to return true which, in turn, would cause cip_base_scoreboard::process_tl_*_item to return
  // before calling process_tl_access.
  //
  // As such, it's definitely a read. Snapshot a generation in the A channel request transaction,
  // then check that rdata matches any model that we have when there is a D channel response.

  uvm_reg_addr_t base_addr = cfg.ral_models[cfg.host_ral_name].get_default_map().get_base_addr();
  uvm_reg_addr_t byte_offset = item.a_addr - base_addr;
  int unsigned   word_idx = byte_offset / (DataWidth / 8);
  int unsigned   subword8 = byte_offset - word_idx * (DataWidth / 8);
  int unsigned   subword32 = subword8 / 4;

  if (channel == AddrChannel) begin
    // Get the current generation for the word that is being addressed and store it under a_source
    // (so that we can look it up for the response)
    m_host_start_gens[item.a_source] = m_data_partition.get_generation(word_idx);
  end else begin
    int unsigned        gen_a, gen_d;
    bit [DataWidth-1:0] exp_word;
    bit [31:0]          exp_word32, lane_mask;

    bit [31:0]   exp_word_value, rdata_mask, exp_rdata;

    // When the A channel item for this transaction came through, we should have got the generation
    // for the word being addressed. Look it up here.
    if (!m_host_start_gens.exists(item.a_source)) begin
      `uvm_fatal("missing_start_gen",
                 $sformatf({"D chanel host_tl item with a_source %0d has ",
                            "no matching entry in m_host_start_gens."},
                           item.a_source))
    end
    gen_a = m_host_start_gens[item.a_source];

    // Look up the current generation
    gen_d = m_data_partition.get_generation(word_idx);

    // Do the generations match? If not, the value might have changed while this read was in
    // progress, so we don't have any way to check the result. Print a debug message at UVM_HIGH and
    // return.
    if (gen_a != gen_d) begin
      `uvm_info("gen_change",
                $sformatf({"The host_tl read of address 0x%0h has word index 0x%0h. ",
                           "When the A channel transaction was seen, that word had generation %0d ",
                           "but now it has generation %0d. Cannot predict rdata."},
                          item.a_addr, word_idx, gen_a, gen_d),
                UVM_HIGH)
      return;
    end

    // Have we got a model of the value of this word? If not, we have no way to check whether rdata
    // is correct. Print a debug message at UVM_HIGH and return.
    if (!m_data_partition.get_known(word_idx)) begin
      `uvm_info("word_unknown",
                $sformatf({"The host_tl read of address 0x%0h has word index 0x%0h but we ",
                           "have no model for that value in the memory. Cannot predict rdata."},
                          item.a_addr, word_idx),
                UVM_HIGH)
      return;
    end

    // The generation is unchanged and we have a model for the value of the word. Get that.
    exp_word = get_data_value(word_idx);

    // Extract the 32-bit word that is being addressed by the bus transaction
    exp_word32 = exp_word[subword32 * 32 +: 32];

    // Extract a mask based on a_size and the address mod 4 (for the relevant byte lanes in the
    // transaction)
    lane_mask = ((1 << (8 << item.a_size)) - 1) << (8 * (byte_offset % 4));

    if (lane_mask & (item.d_data ^ exp_word32)) begin
      `uvm_error("rdata_mismatch",
                 $sformatf({"Read from address 0x%0h (word 0x%0d) with size %0d returned 0x%0h, ",
                            "which masks down to 0x%0h. This word is%0s scrambled. ",
                            "The expected result was 0x%0h (the 32-bit word with index %0d ",
                            "from 0x%0h, masked with 0x%0h)."},
                           item.a_addr, word_idx, item.a_size,
                           item.d_data, item.d_data & lane_mask,
                           data_word_scrambled(word_idx) ? "" : " not",
                           exp_word32 & lane_mask,
                           subword32, exp_word, lane_mask))
    end
  end
endfunction

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

function void rram_ctrl_scoreboard::reset(string kind = "HARD");
  super.reset(kind);

  m_cbs.on_reset();

  m_seen_otp_data_key = 0;
  m_seen_otp_addr_key = 0;
  m_seen_init_done = 0;
  m_seen_local_esc = 0;
  m_seen_sw_dis = 0;
  m_dis_sw_window_counter = 0;

  // This function is called (by dv_base_scoreboard::monitor_reset) at the end of reset. Clear any
  // write transaction count on the partition models. Also, do backdoor reads of the underlying
  // macro if we can.
  m_data_partition.end_of_reset();
  m_info_partition.end_of_reset();

  // If this is the first time we have ended a reset then take a snapshot of the contents of the
  // partitions through the backdoor utilities.
  if (!m_have_bkdr_snapshot) begin
    m_data_partition.take_backdoor_snapshot(m_data_bkdr_util);
    m_info_partition.take_backdoor_snapshot(m_info_bkdr_util);
    m_have_bkdr_snapshot = 1;
  end
endfunction : reset

function void rram_ctrl_scoreboard::write_key_txn(nvm_otp_key_rsp_seq_item item);
  // Check that the returned key hasn't already been seen since the last reset (rram_ctrl should
  // only request each once)
  if (item.m_req.m_is_data_req ? m_seen_otp_data_key : m_seen_otp_addr_key) begin
    `uvm_error("extra_otp_key",
               $sformatf("Have already seen an OTP transaction for the %0s key.",
                         item.m_req.m_is_data_req ? "data" : "addr"))
  end

  if (item.m_req.m_is_data_req) begin
    m_seen_otp_data_key = 1;
    m_otp_data_key = item.m_key;
  end else begin
    m_seen_otp_addr_key = 1;
    m_otp_addr_key = item.m_key;
  end
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

function bit rram_ctrl_scoreboard::page_in_enabled_region(int unsigned        page_idx,
                                                          output int unsigned region_idx);
  for (int unsigned i = 0; i < NumRegions; i++) begin
    uvm_reg_data_t base, size;

    if (ral.mp_region_cfg[i].en.get_mirrored_value() != MuBi4True) continue;

    base = ral.mp_region[i].base.get_mirrored_value();
    size = ral.mp_region[i].size.get_mirrored_value();

    if ((base <= page_idx) && (page_idx - base <= size)) begin
      region_idx = i;
      return 1;
    end
  end
  return 0;
endfunction

function bit rram_ctrl_scoreboard::data_word_scrambled(int unsigned word_idx);
  int unsigned page_idx = word_idx / WordsPerPage;
  int unsigned region_idx;
  bit          is_scrambled;

  if (page_in_enabled_region(page_idx, region_idx)) begin
    return (ral.mp_region_cfg[region_idx].scramble_en.get_mirrored_value() == MuBi4True);
  end else begin
    return (ral.default_region.scramble_en.get_mirrored_value() == MuBi4True);
  end
endfunction

function bit [DataWidth-1:0] rram_ctrl_scoreboard::get_data_value(int unsigned word_idx);
  bit [DataWidth-1:0] infected, disinfected;
  int unsigned        word_start_addr32 = word_idx * (DataWidth / 8) / 4;

  // This function should only be called when we have both OTP keys (because it's only called in
  // response to a successful host transaction)
  if (!m_seen_otp_data_key || !m_seen_otp_addr_key) begin
    `uvm_fatal("need_both_keys", "get_data_value() shouldn't be called before both keys are set.")
  end

  // Get our model of the data that was stored into the data partition. This value has been XORed
  // with the lower bits of the bus address that was used when writing it.
  if (data_word_scrambled(word_idx)) begin
    infected = m_data_bkdr_util.rram_descramble_data(m_data_partition.get_value(word_idx),
                                                     word_idx, m_otp_addr_key, m_otp_data_key);
  end else begin
    infected = m_data_partition.get_value(word_idx);
  end

  // Undo the address infection for each bus word
  for (int unsigned i = 0; i < DataWidth / 32; i++) begin
    int unsigned bus_word_start_addr32 = word_start_addr32 + i;
    disinfected[32 * i +: 32] = infected[32 * i +: 32] ^ bus_word_start_addr32;
  end

  return disinfected;
endfunction

function void rram_ctrl_scoreboard::make_explicitly_track_reg();
  m_explicitly_track_reg.delete();

  // This function works through the list of registers from the hjson block description in order,
  // except for the multi-registers. Those come first so that they can share for loops.

  for (int unsigned i = 0; i < NumRegions; i++) begin
    // Nothing to do for one of REGION_CFG_REGWEN_*, MP_REGION_CFG_*, MP_REGION_*. These registers'
    // action is modelled through mirrored values and reads are already checked in
    // m_tl_core_reg_predictor.
    m_explicitly_track_reg[ral.region_cfg_regwen[i]] = 0;
    m_explicitly_track_reg[ral.mp_region_cfg[i]] = 0;
    m_explicitly_track_reg[ral.mp_region[i]] = 0;
  end

  for (int unsigned i = 0; i < NumInfoPages; i++) begin
    // Nothing to do for one of INFO_REGWEN_*, INFO_PAGE_CFG_*. These registers' action is modelled
    // through mirrored values and reads are already checked in m_tl_core_reg_predictor.
    m_explicitly_track_reg[ral.info_regwen[i]] = 0;
    m_explicitly_track_reg[ral.info_page_cfg[i]] = 0;
  end

  for (int unsigned i = 0; i < NumEmulInfoRegions; i++) begin
    // Nothing to do for one of EMUL_INFO_REGWEN_*, EMUL_INFO_REGION_*. These registers' action is
    // modelled through mirrored values and reads are already checked in m_tl_core_reg_predictor.
    m_explicitly_track_reg[ral.emul_info_regwen[i]] = 0;
    m_explicitly_track_reg[ral.emul_info_region[i]] = 0;
  end

  for (int unsigned i = 0; i < NumEmulInfoSubregions; i++) begin
    // Nothing to do for one of EMUL_INFO_SUBREGION_REGWEN_*, EMUL_INFO_SUBREGION_*,
    // EMUL_INFO_SUBREGION_CFG_REGWEN_*, EMUL_INFO_SUBREGION_CFG_*. These registers' action is
    // modelled through mirrored values and reads are already checked in m_tl_core_reg_predictor.
    m_explicitly_track_reg[ral.emul_info_subregion_regwen[i]] = 0;
    m_explicitly_track_reg[ral.emul_info_subregion[i]] = 0;
    m_explicitly_track_reg[ral.emul_info_subregion_cfg_regwen[i]] = 0;
    m_explicitly_track_reg[ral.emul_info_subregion_cfg[i]] = 0;
  end

  // Nothing to do for INTR_STATE, INTR_ENABLE, INTR_TEST, ALERT_TEST. These registers are tracked
  // in the underlying cip_base_scoreboard.
  m_explicitly_track_reg[ral.intr_state] = 0;
  m_explicitly_track_reg[ral.intr_enable] = 0;
  m_explicitly_track_reg[ral.intr_test] = 0;
  m_explicitly_track_reg[ral.alert_test] = 0;

  // Nothing to do for DIS: its action is modelled through the mirrored value and reads are already
  // checked in m_tl_core_reg_predictor.
  m_explicitly_track_reg[ral.dis] = 0;

  // Nothing to do for EXEC: its action is modelled through the mirrored value and reads are already
  // checked in m_tl_core_reg_predictor.
  m_explicitly_track_reg[ral.exec] = 0;

  // The INIT register does need tracking (because writing to INIT.VAL causes a side-effect)
  m_explicitly_track_reg[ral.init] = 1;

  // The CTRL_REGWEN register needs tracking (it is updated by hardware).
  m_explicitly_track_reg[ral.ctrl_regwen] = 1;

  // The CONTROL register does need tracking (because writing to it causes a side-effect)
  m_explicitly_track_reg[ral.control] = 1;

  // Nothing to do for ADDR: its action is modelled through the mirrored value and reads are already
  // checked in m_tl_core_reg_predictor.
  m_explicitly_track_reg[ral.addr] = 0;

  // Nothing to do for DEFAULT_REGION: its action is modelled through the mirrored value and reads
  // are already checked in m_tl_core_reg_predictor.
  m_explicitly_track_reg[ral.default_region] = 0;

  // Nothing to do for HW_INFO_CFG_OVERRIDE: its action is modelled through the mirrored value and
  // reads are already checked in m_tl_core_reg_predictor.
  m_explicitly_track_reg[ral.hw_info_cfg_override] = 0;

  // The following registers do need tracking directly in on_reg_access. These are all updated by
  // the hardware to reflect current status.
  m_explicitly_track_reg[ral.op_status] = 1;
  m_explicitly_track_reg[ral.status] = 1;
  m_explicitly_track_reg[ral.err_code] = 1;
  m_explicitly_track_reg[ral.std_fault_status] = 1;
  m_explicitly_track_reg[ral.fault_status] = 1;
  m_explicitly_track_reg[ral.err_addr] = 1;
  m_explicitly_track_reg[ral.corr1_err_cnt] = 1;
  m_explicitly_track_reg[ral.corr2_err_cnt] = 1;
  m_explicitly_track_reg[ral.corr1_err_loc] = 1;
  m_explicitly_track_reg[ral.corr2_err_loc] = 1;
  m_explicitly_track_reg[ral.phy_status] = 1;

  // Nothing to do for SCRATCH. This register has no specified behaviour other than to be a 32-bit
  // register that can be read and written. That basic requirement is checked by
  // m_tl_core_reg_predictor.
  m_explicitly_track_reg[ral.scratch] = 0;

  // Nothing to do for FIFO_LVL: tis is a config register whose action is modelled through the
  // mirrored value and reads are already checked in m_tl_core_reg_predictor.
  m_explicitly_track_reg[ral.fifo_lvl] = 0;

  // More status registers that need tracking directly in on_reg_access.
  m_explicitly_track_reg[ral.fifo_clr] = 1;
  m_explicitly_track_reg[ral.curr_fifo_lvl] = 1;
endfunction
