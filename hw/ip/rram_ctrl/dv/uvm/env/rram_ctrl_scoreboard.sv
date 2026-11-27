// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`uvm_analysis_imp_decl(_key_txn)
`uvm_analysis_imp_decl(_reg_item)
`uvm_analysis_imp_decl(_macro_item)

class rram_ctrl_scoreboard extends cip_base_scoreboard #(
  .CFG_T(rram_ctrl_env_cfg),
  .RAL_T(rram_ctrl_core_reg_block),
  .COV_T(rram_ctrl_env_cov)
);
  `uvm_component_utils(rram_ctrl_scoreboard)

  // A model of the current state of a read or write FIFO. All of the "pointers" are measured in
  // 32-bit words. The RRAM word index can by found by dividing by (DataWidth / 32).
  typedef struct {
    // The current SW operation. This is only relevant if next_d_bus_idx < last_bus_idx.
    rram_op_e    op;

    // The partition on which the operation is operating
    rram_part_e  partition;

    // The 32-bit word addressed by the operation.
    int unsigned first_bus_idx;

    // The index of the last 32-bit word touched by the operation. When this struct is cleared,
    // last_bus_idx is zeroed and next_a_bus_idx and next_d_bus_idx are both set to '1.
    int unsigned last_bus_idx;

    // The bus word that will be addressed by the next read or write that appears on the A channel
    int unsigned next_a_bus_idx;

    // The bus word that will be addressed by the next read or write that appears on the D channel.
    int unsigned next_d_bus_idx;
  } fifo_ptr_t;

  // A simple encoding of an "option type" for 32-bit values
  typedef struct {
    // True if this value is considered known, in which case value is meaningful.
    bit        known;

    // The modelled 32-bit value
    bit [31:0] value;
  } maybe_b32_t;

  // A write operation that we expect to see. Tracked with m_pending_macro_writes and checked by
  // write_macro_item (responding to m_macro_imp).
  typedef struct {
    // The partition being written
    rram_part_e         partition;

    // The index of the RRAM word being written
    int unsigned        word_idx;

    // The value being written
    bit [DataWidth-1:0] wdata;
  } macro_write_t;

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

  // An implementation port that tracks transactions with the rram_macro
  uvm_analysis_imp_macro_item #(rram_macro_rsp_seq_item, rram_ctrl_scoreboard) m_macro_imp;

  // Track the fact that wait_for_idle() has started
  local bit m_waiting_for_idle;

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

  // A model of the current state of the fifo that is in use. This will either be the read or write
  // fifo (but we can use the same information because only one fifo is used at once)
  local fifo_ptr_t m_fifo_ptr;

  // 32-bit words between the bus and the FIFO.
  //
  // For write operations, a 32-bit word is added to the queue when the A channel operation is seen
  // (from a_data). Each time that bus_words_per_word elements have been pushed, we collect them
  // together into a word of (known) DataWidth bits and encode them for the appropriate RRAM word
  // index, moving the result to m_pending_enc_word, zeroing the queue again.
  //
  // For read operations, an RRAM word is read from the RRAM model when the A channel operation for
  // its first 32-bit word is seen. This is unpacked into multiple 32-bit words that are added to
  // the queue and are then popped and compared with d_data values when D channel operations are
  // seen.
  local maybe_b32_t m_fifo_pending[$];

  // A DataWidth-bit word that is being written to wr_fifo. This is accumulated from a group of
  // bus_words_per_word values written to m_fifo_pending (see the description of that queue), and
  // scrambled if appropriate and infected with the write address.
  //
  // That value is immediately added to m_pending_macro_writes. If this is the last word of the
  // write operation, it will be passed to complete_write_operation() on the partition model when
  // the D-channel transaction is seen.
  bit [DataWidth-1:0] m_pending_enc_word;

  // Pending writes that we expect to see sent to rram_macro. These are generated by SW write
  // operations and checked against transactions reported through m_macro_imp.
  local macro_write_t m_pending_macro_writes[$];

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
  extern function void phase_ready_to_end(uvm_phase phase);

  // Wait until all pending transactions have cleared (so run_phase can finish)
  extern task wait_for_idle();

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

  // A call-back run by process_tl_core_access when it sees a read to or write from a memory (the
  // rd_fifo and wr_fifo addresses).
  //
  // This function collects accesses to the fifo and converts them between bus operations and
  // operations on (longer) RRAM words. It updates the RRAM prediction after writes and checks read
  // data for reads.
  extern local function void on_mem_access(tl_seq_item item, tl_phase_e tl_phase, uvm_mem memory);

  // True if there is currently the requested a SW operation in progress and it still expects to
  // transmit words on the given channel.
  //
  //   - write_op:  Look at Write operations (not Read or Rewrite operations)
  //   - d_channel: Look at counters for the D (not A) channel.
  extern local function bit is_sw_op_in_progress(bit write_op, bit d_channel);

  // Clear m_fifo_ptr (so that it no longer tracks an operation in progress)
  extern local function void clear_fifo_ptr();

  // Called when a SW operation is started by a write to CONTROL when CTRL_REGWEN=1.
  //
  // The arguments are the wdata for the fields of the register. This sets the modelled state of the
  // appropriate FIFO, causing bus accesses to rd_fifo/wr_fifo to have an effect.
  extern local function void start_sw_operation(bit [1:0]   raw_op,
                                                rram_part_e partition,
                                                bit [9:0]   num);

  // Called when a SW operation runs to completion (maybe because the last corresponding FIFO
  // operation has run). Clear the modelled value of CONTROL.START and zero out the fifo pointer.
  extern local function void end_sw_operation();

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

  // The write function for m_macro_imp. This is called every time rram_macro responds to a request
  // from rram_ctrl.
  extern function void write_macro_item(rram_macro_rsp_seq_item item);

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

  // Return true if the given page of the data partition is in a region that is enabled
  //
  // If so, writes the index of the first enabled region containing the page to the region_idx
  // output variable.
  extern local function bit data_page_in_enabled_region(int unsigned        page_idx,
                                                        output int unsigned region_idx);

  // Return true if the given RRAM word in the given partition is scrambled (either by info page
  // configuration, an enabled region, or by default_region).
  extern local function bit is_word_scrambled(rram_part_e part, int unsigned word_idx);

  // XOR a word with the address (used as part of translating between bus words and RRAM words)
  extern local function bit [DataWidth-1:0] addr_xor(int unsigned        word_idx,
                                                     bit [DataWidth-1:0] data);

  // Encode a word for the given partition, XORing with the word address and also scrambling if
  // is_word_scrambled() is true.
  extern local function bit [DataWidth-1:0] encode_word(rram_part_e         part,
                                                        int unsigned        word_idx,
                                                        bit [DataWidth-1:0] wdata);

  // Return the modelled value of the given word in the given partition, unscrambling if
  // rram_word_scrambled() is true.
  extern local function bit [DataWidth-1:0] get_rram_value(rram_part_e part, int unsigned word_idx);

  // Populate the m_explicitly_track_reg associative array, which on_reg_access will use to track
  // whether it needs to directly reason about access to a given register.
  extern local function void make_explicitly_track_reg();

  // Render a macro_write_t to a string (with hex values)
  extern local function string sprint_macro_write_t(const ref macro_write_t expected);

  // Check whether an observed rram_macro_req_seq_item matches a macro_write_t.
  extern local function bit is_matching_macro_seq_item(rram_macro_req_seq_item req_item,
                                                       const ref macro_write_t expected);
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

  m_macro_imp = new ("m_macro_imp", this);

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

  // Post-test checks:
  //
  //  - We don't currently check that m_fifo_pending and m_fifo_ptr are empty: it's perfectly
  //    reasonable to end the test before a SW operation has finished.

endfunction : check_phase

function void rram_ctrl_scoreboard::phase_ready_to_end(uvm_phase phase);
  // The only phase that we might delay is the run_phase: we can ignore anything else
  if (!phase.is(uvm_run_phase::get())) return;

  // Spawn a task to wait until the device becomes idle, setting a flag to track the fact that it's
  // running (because the UVM callback might be called several times at the end of run_phase).
  if (!m_waiting_for_idle) begin
    fork begin
      m_waiting_for_idle = 1;

      fork
        wait_for_idle();
        begin
          #(cfg.m_phase_end_timeout_ns * 1ns);
          `uvm_error("phase_end_timeout",
                     $sformatf("At the end of run_phase, scoreboard still busy after %0d ns.",
                               cfg.m_phase_end_timeout_ns))
        end
      join_any
      disable fork;

      m_waiting_for_idle = 0;
    end join_none
  end
endfunction

task rram_ctrl_scoreboard::wait_for_idle();
  wait(m_pending_macro_writes.size() == 0);
endtask

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

      if (data_page_in_enabled_region(page_idx, region_idx)) begin
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
    if (tl_phase == DataWrite && !item.d_error && m_cbs.get_reg_prediction(ral.ctrl_regwen)) begin
      // This is the D channel response to a transaction to writing item.a_data to CONTROL. The
      // transaction didn't get an error response and the modelled value of CTRL_REGWEN is true.
      //
      // If the write sets START=1, it will start a SW operation.
      if ((item.a_data >> ral.control.start.get_lsb_pos()) & 1) begin
        // This write will start a SW operation
        bit [1:0] raw_op        = (item.a_data >> ral.control.op.get_lsb_pos());
        bit       raw_partition = (item.a_data >> ral.control.partition.get_lsb_pos());
        bit [9:0] num           = (item.a_data >> ral.control.num.get_lsb_pos());

        start_sw_operation(raw_op, rram_part_e'(raw_partition), num);
      end

      // No need to update the prediction for the register contents: that will be handled by
      // m_tl_core_reg_predictor.

    end else if (tl_phase == DataRead) begin
      // When reading the CONTROL register, we don't need to check the rdata (this has already been
      // done in m_cbs.post_predict). We do need to check that we don't get a d_error response.
      if (item.d_error) begin
        `uvm_error("unexpected_d_error", "Unexpected d_error=1 when reading CONTROL register.")
      end
    end
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
  // The number of 32-bit bus words in each RRAM word.
  int unsigned bus_words_per_word = DataWidth / 32;

  // The partition name and model for the partition that's being addressed by the currently running
  // SW operation (if there is one)
  string               partition_name;
  rram_partition_model partition_model;

  case (m_fifo_ptr.partition)
    RramPartData: begin
      partition_name = "data";
      partition_model = m_data_partition;
    end
    RramPartInfo: begin
      partition_name = "info";
      partition_model = m_info_partition;
    end
    // Note that this can't happen: rram_part_e has two known values and is backed by a 1-bit
    // vector.
    default: `uvm_fatal("bad_enum", "Invalid value for m_fifo_ptr.partition")
  endcase

  if (memory == ral.wr_fifo) begin
    case (tl_phase)
      AddrWrite: begin
        // The write to the FIFO only has an effect if there is a Write operation in progress, which
        // still expects a value on the A channel. If not, it will be discarded.
        if (is_sw_op_in_progress(.write_op(1), .d_channel(0))) begin
          // Is this the first 32-bit word in a particular RRAM word? Since writes must be aligned
          // to RRAM words, this will only ever happen when next_a_bus_idx is divisible by
          // bus_words_per_word.
          if (m_fifo_ptr.next_a_bus_idx % bus_words_per_word == 0) begin
            // Since this is the first bus word of the RRAM word, tell the partition model that the
            // appropriate word has a write operation incoming.
            partition_model.start_write_operation(m_fifo_ptr.next_a_bus_idx / bus_words_per_word);
          end

          // Either way, push the 32-bit word into m_fifo_pending and increment next_a_bus_idx
          // (supporting pipelining if the hardware does)
          m_fifo_pending.push_back('{known: 1, value: item.a_data});

          // Is this the last 32-bit word in a particular RRAM word? This happens when
          // next_a_bus_idx+1 is divisible by bus_words_per_word.
          if ((m_fifo_ptr.next_a_bus_idx + 1) % bus_words_per_word == 0) begin
            int unsigned        next_word_idx = m_fifo_ptr.next_a_bus_idx / bus_words_per_word;
            bit [DataWidth-1:0] collected_bus_words;
            macro_write_t       macro_write;

            // Since this is the last bus word of the RRAM word, we know that m_fifo_pending will
            // contain exactly bus_words_per_word items.
            if (m_fifo_pending.size() != bus_words_per_word) begin
              `uvm_fatal("fifo_pending_len",
                         $sformatf("m_fifo_pending should have exactly %0d elements but has %0d.",
                                   bus_words_per_word, m_fifo_pending.size()))
            end

            // Pull out the bus words and assemble them into the (unencoded) value that will be
            // written to RRAM.
            for (int unsigned i = 0; i < bus_words_per_word; i++) begin
              collected_bus_words[i * 32 +: 32] = m_fifo_pending[i].value;
            end
            m_fifo_pending.delete();

            // Infect that word with the destination address and scramble if necessary. Write that
            // value to m_pending_enc_word (for partition_model.complete_write_operation() when the
            // D-channel transaction is seen)
            m_pending_enc_word = encode_word(m_fifo_ptr.partition,
                                             next_word_idx,
                                             collected_bus_words);

            // Combine that word with the address to make a macro_write_t value and push it to
            // m_pending_macro_writes. That guarantees that the value will be pending by the time
            // rram_ctrl passes it to the RRAM macro (even if the D channel response is slow).
            macro_write = '{partition: m_fifo_ptr.partition,
                            word_idx:  next_word_idx,
                            wdata:     m_pending_enc_word};
            m_pending_macro_writes.push_back(macro_write);

            `uvm_info("macro_write",
                      $sformatf("Added expected macro write to queue: %0s",
                                sprint_macro_write_t(macro_write)),
                      UVM_HIGH)
          end

          m_fifo_ptr.next_a_bus_idx++;
        end
      end
      DataWrite: begin
        // The TL write of a word to the FIFO has just completed. This only has an effect if there
        // is a Write operation in progress, which still expects to report a transaction on the D
        // channel. If not, it will be ignored.
        if (is_sw_op_in_progress(.write_op(1), .d_channel(1))) begin
          int unsigned next_word_idx = m_fifo_ptr.next_d_bus_idx / bus_words_per_word;

          // This D channel response shows that the 32-bit write has completed. If this is the last
          // of the bus_words_per_word words for an RRAM word, tell the partition model that the
          // RRAM word write is complete.
          if ((m_fifo_ptr.next_d_bus_idx + 1) % bus_words_per_word == 0) begin
            partition_model.complete_write_operation(next_word_idx, m_pending_enc_word);
          end

          // Either way, increment next_d_bus_idx
          m_fifo_ptr.next_d_bus_idx++;

          // If doing this means it becomes greater than last_bus_idx, mark the SW operation
          // complete.
          if (m_fifo_ptr.next_d_bus_idx > m_fifo_ptr.last_bus_idx) begin
            end_sw_operation();
          end
        end
      end
      AddrRead, DataRead: begin
        // Because this is a write-only memory, the infrastructure in
        // cip_base_scoreboard::process_tl_*_item should have predicted an error and not passed the
        // item down to process_tl_core_access (which called on_mem_access).
        `uvm_fatal("missed_error",
                   "Read access to write FIFO should have been caught by cip_base_scoreboard.")
      end
      default: `uvm_fatal("bad_phase", $sformatf("Unknown tl_phase: %0d", tl_phase))
    endcase
  end else if (memory == ral.rd_fifo) begin
    case (tl_phase)
      AddrRead: begin
        // If there is no operation in progress, the specification doesn't actually say what
        // happens. Replace this with something sensible when issue #32461 is resolved.
        if (!is_sw_op_in_progress(.write_op(0), .d_channel(0))) begin
          `uvm_error("unspecified_rd_fifo",
                     "No specification for rd_fifo accesses when no operation in progress.")
        end else begin
          // If this is the first 32-bit word in an RRAM word (either because the next_a_bus_idx is
          // a multiple of bus_words_per_word or because it equals first_bus_idx), grab that word's
          // value and append bus words to m_fifo_pending (from which we will pop values when
          // comparing D channel transactions).
          if ((m_fifo_ptr.next_a_bus_idx == m_fifo_ptr.first_bus_idx) ||
              (m_fifo_ptr.next_a_bus_idx % bus_words_per_word == 0)) begin
            int unsigned word_idx = m_fifo_ptr.next_a_bus_idx / bus_words_per_word;
            int unsigned lo_lane, hi_lane;

            // Handle partial RRAM words here by working out which bus words to look at. The first
            // one will be next_a_bus_idx, modulo bus_words_per_word. The last will normally
            // bus_words_per_word - 1, but might be truncated if this is the last RRAM word.
            //
            // end_word_bus_word is the bus word index for the end of the current RRAM word.
            // last_addressed_bus_word is highest bus word index in the current RRAM word that is
            // addressed by this operation (clamping with last_bus_idx).
            int unsigned end_word_bus_idx = (word_idx + 1) * bus_words_per_word - 1;
            int unsigned cur_last_bus_idx = ((end_word_bus_idx < m_fifo_ptr.last_bus_idx) ?
                                             end_word_bus_idx : m_fifo_ptr.last_bus_idx);

            // At this point, next_a_bus_idx and cur_last_bus_idx give the bounds for the bus words
            // that are being extracted from the current RRAM word. As a simple consistency check,
            // make sure that next_a_bus_idx and cur_last_bus_idx both point at the same RRAM word.
            if (word_idx != (cur_last_bus_idx / bus_words_per_word)) begin
              `uvm_fatal("bus_sample_err",
                         $sformatf({"When computing bus words to read starting at bus idx 0x%0h, ",
                                    "we expect to read up to index 0x%0h. But these indices are ",
                                    "from different RRAM words (0x%0h and 0x%0h)."},
                                   m_fifo_ptr.next_a_bus_idx, cur_last_bus_idx,
                                   word_idx, (cur_last_bus_idx / bus_words_per_word)))
            end

            // Work modulo bus_words_per_word to get indices of 32-bit "lanes" of the RRAM word.
            lo_lane = m_fifo_ptr.next_a_bus_idx % bus_words_per_word;
            hi_lane = cur_last_bus_idx % bus_words_per_word;

            if (partition_model.get_known(word_idx)) begin
              bit [DataWidth-1:0] rdata = get_rram_value(m_fifo_ptr.partition, word_idx);

              for (int unsigned i = lo_lane; i <= hi_lane; i++) begin
                m_fifo_pending.push_back('{known: 1, value: rdata[32 * i +: 32]});
              end
            end else begin
              repeat (hi_lane - lo_lane + 1) begin
                m_fifo_pending.push_back('{default: '0});
              end
            end
          end

          // Either way, increment next_a_bus_idx
          m_fifo_ptr.next_a_bus_idx++;
        end
      end
      DataRead: begin
        // If there is no operation in progress, the specification doesn't actually say what
        // happens. Replace this with something sensible when issue #32461 is resolved.
        if (!is_sw_op_in_progress(.write_op(0), .d_channel(1))) begin
          `uvm_error("unspecified_rd_fifo",
                     "No specification for rd_fifo accesses when no operation in progress.")
        end else begin
          maybe_b32_t exp_value;

          // There should be at least one item in m_fifo_pending (as part of a group that were
          // pushed for the first A channel transaction for this RRAM word).
          if (!m_fifo_pending.size()) begin
            `uvm_fatal("empty_fifo_pending",
                       "D channel transaction reading from rd_fifo with no pending data.")
          end

          exp_value = m_fifo_pending.pop_front();

          if (!exp_value.known) begin
            // The partition model does not have an expected value for this word in RRAM, so there's
            // nothing that we can check.
            `uvm_info("unknown_mem_value",
                      $sformatf({"As part of a SW read operation, we just read 32 bits from byte ",
                                 "offset 0x%0h in the %0s partition (bus word %0d of RRAM word ",
                                 "0x%0h). The model of the partition does not have a prediction ",
                                 "for this word, so we cannot check it was supplied correctly."},
                                m_fifo_ptr.next_d_bus_idx * 4,
                                partition_name,
                                m_fifo_ptr.next_d_bus_idx % bus_words_per_word,
                                m_fifo_ptr.next_d_bus_idx / bus_words_per_word),
                      UVM_HIGH)
          end else begin
            if (item.d_data != exp_value.value) begin
              `uvm_error("rdata_mismatch",
                         $sformatf({"As part of a SW read operation, we just read 0x%0h from byte ",
                                    "offset 0x%0h in the %0s partition (bus word %0d of RRAM word ",
                                    "0x%0h). The model predicted 0x%0h."},
                                   item.d_data,
                                   m_fifo_ptr.next_d_bus_idx * 4,
                                   partition_name,
                                   m_fifo_ptr.next_d_bus_idx % bus_words_per_word,
                                   m_fifo_ptr.next_d_bus_idx / bus_words_per_word,
                                   exp_value.value))
            end
          end

          // Increment next_d_bus_idx. If this gets past last_bus_idx, mark the SW operation
          // complete.
          m_fifo_ptr.next_d_bus_idx++;
          if (m_fifo_ptr.next_d_bus_idx > m_fifo_ptr.last_bus_idx) begin
            end_sw_operation();
          end
        end
      end
      AddrWrite, DataWrite: begin
        // Because this is a read-only memory, the infrastructure in
        // cip_base_scoreboard::process_tl_*_item should have predicted an error and not passed the
        // item down to process_tl_core_access (which called on_mem_access).
        `uvm_fatal("missed_error",
                   "Write access to read FIFO should have been caught by cip_base_scoreboard.")
      end
      default: `uvm_fatal("bad_phase", $sformatf("Unknown tl_phase: %0d", tl_phase))
    endcase
  end else begin
    `uvm_fatal("new_mem", "Unknown memory not yet supported in on_mem_access.")
  end
endfunction : on_mem_access

function bit rram_ctrl_scoreboard::is_sw_op_in_progress(bit write_op, bit d_channel);
  int unsigned next_bus_idx;

  // If write_op doesn't match whether m_fifo_ptr.op is RramOpWrite, there is either no operation in
  // progress or it's another operation.
  if (write_op != (m_fifo_ptr.op == RramOpWrite)) return 0;

  // If this is the right type of operation, there are still bus words expected on the appropriate
  // channel if the appropriate next bus index is less than or equal to the last one.
  next_bus_idx = (d_channel ? m_fifo_ptr.next_d_bus_idx : m_fifo_ptr.next_a_bus_idx);
  return next_bus_idx <= m_fifo_ptr.last_bus_idx;
endfunction

function void rram_ctrl_scoreboard::clear_fifo_ptr();
  m_fifo_ptr = '{
    op: RramOpRead,
    partition: RramPartData,
    first_bus_idx: 0,
    last_bus_idx: 0,
    next_a_bus_idx: '1,
    next_d_bus_idx: '1
  };
endfunction

function void rram_ctrl_scoreboard::start_sw_operation(bit [1:0]   raw_op,
                                                       rram_part_e partition,
                                                       bit [9:0]   num);
  int unsigned   bus_words_per_word = DataWidth / 32;
  int unsigned   first_bus_idx = ral.addr.start.get_mirrored_value() / 4;
  int unsigned   last_bus_idx = first_bus_idx + num;
  uvm_reg_addr_t byte_addr = 4 * first_bus_idx;
  rram_op_e      op = rram_op_e'(raw_op);
  string         op_name = (op.name() == "") ? "(??)" : op.name();

  // Check that we don't believe an operation is already running. Our register model believes there
  // is nothing running (otherwise this function would not have been called), but we should check
  // that our fifo models agree.
  if ((m_fifo_ptr.next_a_bus_idx <= m_fifo_ptr.last_bus_idx) ||
      (m_fifo_ptr.next_d_bus_idx <= m_fifo_ptr.last_bus_idx)) begin
    `uvm_error("overlapping_sw_ops",
               $sformatf({"Reg modelling thought we could start a SW op but m_fifo_ptr has ",
                          "bus indices 0x%0h, 0x%0h for a %0s operation with last bus idx 0x%0h."},
                         m_fifo_ptr.next_a_bus_idx,
                         m_fifo_ptr.next_d_bus_idx,
                         m_fifo_ptr.op.name(),
                         m_fifo_ptr.last_bus_idx))
  end

  // If there is no operation running, we expect m_fifo_pending to be empty (it should have been
  // cleared when we concluded there was no operation).
  //
  // This check is helpful because it makes sure that values from one operation don't pollute
  // expected values for the next one.
  if (m_fifo_pending.size()) begin
    `uvm_fatal("stray_pending",
               $sformatf("There is no SW operation running, but m_fifo_pending.size() is %0d.",
                         m_fifo_pending.size()))
  end

  // Update the FIFO pointer to match, switching on the value being written to the OP field. The
  // enum values are defined in rram_ctrl.hjson.
  case (raw_op)
    RramOpRead: begin
      m_fifo_ptr.op = op;
      m_fifo_ptr.partition = partition;
      m_fifo_ptr.first_bus_idx = first_bus_idx;
      m_fifo_ptr.last_bus_idx = last_bus_idx;
      m_fifo_ptr.next_a_bus_idx = first_bus_idx;
      m_fifo_ptr.next_d_bus_idx = first_bus_idx;
    end
    RramOpWrite: begin
      if (first_bus_idx % bus_words_per_word) begin
        // ADDR.START is not RRAM-word-aligned. This operation won't write to RRAM and will instead
        // report an error.
        //
        // TODO(#31290): These errors are not yet modelled in the scoreboard.
      end else begin
        m_fifo_ptr.op = op;
        m_fifo_ptr.partition = partition;
        m_fifo_ptr.first_bus_idx = first_bus_idx;
        m_fifo_ptr.last_bus_idx = last_bus_idx;
        m_fifo_ptr.next_a_bus_idx = first_bus_idx;
        m_fifo_ptr.next_d_bus_idx = first_bus_idx;
      end
    end
    RramOpRewrite: begin
      // Nothing to do here: the Rewrite operation doesn't have any effect that is visible through
      // rd_fifo or wr_fifo. Any other effects will be modelled elsewhere.
    end
    default: begin // Undefined op
      // This operation is unsupported, which means that the operation will immediately complete
      // with an error (raising the RECOV_ERR alert and setting OP_STATUS.ERR and ERR_CODE.OP_ERR)
      //
      // TODO(#31290): These errors are not yet modelled in the scoreboard.
    end
  endcase

  `uvm_info("start_sw_opn",
            $sformatf({"Starting software operation (op = %0s, partition = %0s, num = %0d). ",
                       "first_bus_idx is 0x%0h (the operation covers addresses 0x%0h .. 0x%0h)"},
                      op_name, partition.name(), num,
                      first_bus_idx, byte_addr, byte_addr + (num + 1) * 4 - 1),
            UVM_HIGH)
endfunction

function void rram_ctrl_scoreboard::end_sw_operation();
  // TODO(#31290):
  //
  //   We don't currently predict the value of RAL.CONTROL, so there isn't any modelling to do here.
  //   When we *do* start predicting the value (and checking the prediction), we should clear any
  //   prediction, on the basis that we don't currently have a model of the expected value.
  //
  //   We'll know the correct value again when we either see the OP_DONE interrupt or read the
  //   CONTROL register as zero.

  clear_fifo_ptr();
endfunction

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
    exp_word = get_rram_value(RramPartData, word_idx);

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
                           is_word_scrambled(RramPartData, word_idx) ? "" : " not",
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

  // Zero out the FIFO pointer, which also clears any pending operation.
  clear_fifo_ptr();

  // Clear the queue that might have been tracking partially complete words for a SW operation.
  m_fifo_pending.delete();

  // Clear any pending macro writes (although it's not a great sign if a user resets rram_ctrl in
  // the middle of doing them)
  m_pending_macro_writes.delete();

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

function void rram_ctrl_scoreboard::write_macro_item(rram_macro_rsp_seq_item item);
  if (item.m_req.m_wr_req) begin
    // Some writes to the RRAM macro are triggered by SW transactions (which we observe by looking
    // at register accesses). However, there are other writes to the RRAM macro as well. We want to
    // check that the SW writes are passed to the RRAM macro in order.
    //
    // To do this, search through the list of expected pending RRAM writes for a match.
    //
    //  - If there is no match, we conclude that this was not triggered by a SW transaction (so have
    //    nothing to do here).
    //
    //  - If there is a match at index zero, everything matches up correctly. Good!
    //
    //  - If there is a match, but not at index zero, then the previous items in the expected
    //    queue have got lost. Generate an error.
    int unsigned skip_count;
    bit          seen_match;

    foreach (m_pending_macro_writes[i]) begin
      if (is_matching_macro_seq_item(item.m_req, m_pending_macro_writes[i])) begin
        seen_match = 1;
        break;
      end
      skip_count++;
    end

    if (!seen_match) begin
      // Nothing matched item. Nothing to do here.
    end else begin
      if (skip_count != 0) begin
        // We got a match at a later item in m_pending_macro_writes. Since we expect to predict
        // these things in order, this means that we've failed to send skip_count items. Oh dear!
        // Generate an error.
        `uvm_error("missed_macro_write",
                   $sformatf({"A transaction with the RRAM macro has been seen which matches ",
                              "item %0d of the list of pending macro writes, meaning that we ",
                              "have lost that many.\n",
                              "Item seen:\n%0s\n",
                              "Matching pending req:\n%0s"},
                             skip_count,
                             item.sprint(),
                             sprint_macro_write_t(m_pending_macro_writes[skip_count])))
      end

      // Discard items from the front of m_pending_macro_writes up to the one that just matched
      repeat (skip_count + 1) void'(m_pending_macro_writes.pop_front());
    end
  end
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

function bit rram_ctrl_scoreboard::data_page_in_enabled_region(int unsigned        page_idx,
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

function bit rram_ctrl_scoreboard::is_word_scrambled(rram_part_e part, int unsigned word_idx);
  int unsigned page_idx = word_idx / WordsPerPage;
  int unsigned region_idx;
  bit          is_scrambled;

  case (part)
    RramPartData: begin
      if (page_idx >= TotalDataPages) begin
        // This page doesn't exist in the data partition. The scoreboard shouldn't be reasoning
        // about it.
        `uvm_fatal("word_oob",
                   $sformatf({"There is no word 0x%0h in the data partition. ",
                              "This would have page index 0x%0h but the data partition ",
                              "only has 0x%0h pages."},
                             word_idx, page_idx, TotalDataPages))
      end

      // The page is scrambled if it is either in an enabled region with scrambling enabled or if
      // it's in no enabled region, but scrambling is enabled in the default region config.
      if (data_page_in_enabled_region(page_idx, region_idx)) begin
        return (ral.mp_region_cfg[region_idx].scramble_en.get_mirrored_value() == MuBi4True);
      end else begin
        return (ral.default_region.scramble_en.get_mirrored_value() == MuBi4True);
      end
    end

    RramPartInfo: begin
      if (page_idx >= TotalInfoPages) begin
        // This page doesn't exist in the info partition. The scoreboard shouldn't be reasoning
        // about it.
        `uvm_fatal("word_oob",
                   $sformatf({"There is no word 0x%0h in the info partition. ",
                              "This would have page index 0x%0h but the info partition ",
                              "only has 0x%0h pages."},
                             word_idx, page_idx, TotalInfoPages))
      end

      // The info page is scrambled if it has SCRAMBLE_EN = MuBi4True. (Note that the page is
      // completely disabled if EN is not MuBi4True, but that is tracked elsewhere)
      return (ral.info_page_cfg[page_idx].scramble_en.get_mirrored_value() == MuBi4True);
    end

    // Note that this can't happen: rram_part_e has two known values and is backed by a 1-bit
    // vector.
    default: `uvm_fatal("bad_enum", "Invalid value for part")
  endcase
endfunction

function bit [DataWidth-1:0] rram_ctrl_scoreboard::addr_xor(int unsigned        word_idx,
                                                            bit [DataWidth-1:0] data);
  int unsigned        word_start_addr32 = word_idx * (DataWidth / 8) / 4;
  bit [DataWidth-1:0] transformed;

  for (int unsigned i = 0; i < DataWidth / 32; i++) begin
    int unsigned bus_word_start_addr32 = word_start_addr32 + i;
    transformed[32 * i +: 32] = data[32 * i +: 32] ^ bus_word_start_addr32;
  end

  return transformed;
endfunction

function bit [DataWidth-1:0] rram_ctrl_scoreboard::encode_word(rram_part_e         part,
                                                               int unsigned        word_idx,
                                                               bit [DataWidth-1:0] wdata);
  bit [DataWidth-1:0] infected;

  if (!m_seen_otp_addr_key || !m_seen_otp_data_key) begin
    `uvm_fatal("missing_key", "Cannot encode data for RRAM unless both keys are known.")
  end

  infected = addr_xor(word_idx, wdata);

  if (is_word_scrambled(part, word_idx)) begin
    rram_ctrl_bkdr_util bkdr_util = ((part == RramPartData) ? m_data_bkdr_util : m_info_bkdr_util);
    return bkdr_util.rram_scramble_data(infected, word_idx, m_otp_addr_key, m_otp_data_key);
  end else begin
    return infected;
  end
endfunction

function bit [DataWidth-1:0] rram_ctrl_scoreboard::get_rram_value(rram_part_e  part,
                                                                  int unsigned word_idx);
  rram_partition_model part_model;
  rram_ctrl_bkdr_util  bkdr_util;
  bit [DataWidth-1:0]  encoded, infected;

  // This function should only be called when we have both OTP keys (because it's only called in
  // response to a successful host transaction)
  if (!m_seen_otp_addr_key || !m_seen_otp_data_key) begin
    `uvm_fatal("need_both_keys", "get_rram_value() shouldn't be called before both keys are set.")
  end

  case (part)
    RramPartData: begin
      part_model = m_data_partition;
      bkdr_util  = m_data_bkdr_util;
    end
    RramPartInfo: begin
      part_model = m_info_partition;
      bkdr_util  = m_info_bkdr_util;
    end
  endcase

  // Get our model of the data that was stored into the data partition. This value has been XORed
  // with the lower bits of the bus address that was used when writing it and has possibly also been
  // scrambled
  encoded = part_model.get_value(word_idx);

  // If the word is scrambled, remove the scrambling, to result in a word that just has address
  // infection.
  if (is_word_scrambled(part, word_idx)) begin
    infected = bkdr_util.rram_descramble_data(encoded, word_idx, m_otp_addr_key, m_otp_data_key);
  end else begin
    infected = encoded;
  end

  return addr_xor(word_idx, infected);
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

function string rram_ctrl_scoreboard::sprint_macro_write_t(const ref macro_write_t expected);
  return $sformatf("macro_write_t'({partition: %0p, word_idx: 'h%0x, wdata: 'h%0x})",
                   expected.partition, expected.word_idx, expected.wdata);
endfunction

function bit rram_ctrl_scoreboard::is_matching_macro_seq_item(rram_macro_req_seq_item req_item,
                                                              const ref macro_write_t expected);
  return ((req_item.m_part == expected.partition) &&
          (req_item.m_addr == expected.word_idx) &&
          (req_item.m_wr_data == expected.wdata));
endfunction
