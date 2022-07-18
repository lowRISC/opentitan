// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define loop_ral_models_to_create_threads(body) \
  fork \
    begin : isolation_fork \
      foreach (cfg.ral_models[i]) begin \
        automatic string ral_name = i; \
        fork \
          begin \
            body \
          end \
        join_none \
      end \
      wait fork; \
    end : isolation_fork \
  join

class cip_base_vseq #(type RAL_T               = dv_base_reg_block,
                      type CFG_T               = cip_base_env_cfg,
                      type COV_T               = cip_base_env_cov,
                      type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer)
                      extends dv_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T);
  `uvm_object_new
  // knobs to disable post_start clear interrupt routine
  bit do_clear_all_interrupts = 1'b1;

  bit expect_fatal_alerts = 1'b0;

  // knobs to enable alert auto reponse, once disabled it won't be able to enable again unless
  // reset is issued
  bit en_auto_alerts_response = 1'b1;

  // knob to enable/disable running csr_vseq with passthru_mem_tl_intg_err
  bit en_csr_vseq_w_passthru_mem_intg = 1;

  // csr queues
  dv_base_reg all_csrs[$];
  dv_base_reg intr_state_csrs[$];

  // user can set the name of common seq to run directly without using $value$plusargs
  string common_seq_type;

  // address mask struct
  typedef struct packed {
    bit [BUS_AW-1:0]  addr;
    bit [BUS_DBW-1:0] mask;
  } addr_mask_t;

  addr_mask_t mem_exist_addr_q[string][$];

  // mem_ranges without base address
  addr_range_t updated_mem_ranges[string][$];

  // unmapped addr ranges without base address
  addr_range_t updated_unmapped_addr_ranges[string][$];

  // mask out bits out of the csr/mem range and LSB 2 bits
  bit [BUS_AW-1:0] csr_addr_mask[string];

  // This knob is used in run_seq_with_rand_reset_vseq to control how long we wait before injecting
  // a reset.
  rand uint rand_reset_delay;
  constraint rand_reset_delay_c {
    rand_reset_delay dist {
        [1         :1000]       :/ 1,
        [1001      :100_000]    :/ 2,
        [100_001   :1_000_000]  :/ 6,
        [1_000_001 :5_000_000]  :/ 1
    };
  }

  // control the chance to let tl adapter to abort CSR access if the valid isn't accept within given
  // a_valid_len
  rand uint csr_access_abort_pct;
  constraint csr_access_abort_pct_c {
    csr_access_abort_pct dist {
      0      :/ 50,
      [1:99] :/ 40,
      100    :/ 10
    };
  }

  `uvm_object_param_utils_begin(cip_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T))
    `uvm_field_string(common_seq_type, UVM_DEFAULT)
  `uvm_object_utils_end

  `include "cip_base_vseq__tl_errors.svh"
  `include "cip_base_vseq__shadow_reg_errors.svh"
  `include "cip_base_vseq__sec_cm_fi.svh"

  virtual task post_apply_reset(string reset_kind = "HARD");
    super.post_apply_reset(reset_kind);

    // Wait for alert init done, then start the sequence.
    foreach (cfg.list_of_alerts[i]) begin
      if (cfg.m_alert_agent_cfg[cfg.list_of_alerts[i]].is_active) begin
        wait (cfg.m_alert_agent_cfg[cfg.list_of_alerts[i]].alert_init_done == 1);
      end
    end

    if (en_auto_alerts_response && cfg.list_of_alerts.size()) run_alert_rsp_seq_nonblocking();
  endtask

  function void pre_randomize();
    super.pre_randomize();
    // Disable csr_access_abort because shadow_reg sequence requires all shadow registers'
    // read/write to be executed into design without aborting.
    if (common_seq_type inside {"shadow_reg_errors", "shadow_reg_errors_with_csr_rw"}) begin
      csr_access_abort_pct.rand_mode(0);
    end
  endfunction

  task pre_start();
    if (common_seq_type == "") void'($value$plusargs("run_%0s", common_seq_type));
    if (common_seq_type == "alert_test") en_auto_alerts_response = 0;

    csr_utils_pkg::max_outstanding_accesses = 1 << BUS_AIW;
    super.pre_start();
    extract_common_csrs();
  endtask

  task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask : body

  task post_start();
    super.post_start();

    if (expect_fatal_alerts) begin
      // Fatal alert is triggered in this seq. Wait 10_000ns so the background check
      // `check_fatal_alert_nonblocking` has enough time to execute before dut_init.
      // Issue reset if reset is allowed, otherwise, reset will be called in upper vseq.
      #10_000ns;
      dut_init();
    end else begin
      check_no_fatal_alerts();
    end

    // Some fatal alerts might trigger interrupt as well, so only check interrupt after fatal alert
    // is cleared.
    void'($value$plusargs("do_clear_all_interrupts=%0b", do_clear_all_interrupts));
    if (do_clear_all_interrupts) clear_all_interrupts();
  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      fork
        if (cfg.num_edn) apply_edn_reset(kind);
        super.apply_reset(kind);
      join
    end
  endtask

  virtual task apply_edn_reset(string kind = "HARD");
    if (cfg.num_edn && kind == "HARD") cfg.edn_clk_rst_vif.apply_reset();
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    if (cfg.num_edn) begin
      cfg.edn_clk_rst_vif.drive_rst_pin(0);
      reset_duration_ps = max2(reset_duration_ps, cfg.edn_clk_rst_vif.clk_period_ps);
    end
    super.apply_resets_concurrently(reset_duration_ps);
    if (cfg.num_edn) cfg.edn_clk_rst_vif.drive_rst_pin(1);
  endtask

  // tl_access task: does a single BUS_DW-bit write or read transaction to the specified address
  // note that this task does not update ral model; optionally also checks for error response
  // TODO: randomize size, addr here based on given addr range, data, and mask, eventually can be
  // reused for mem_read, partial read, and hmac msg fifo write
  virtual task tl_access(input bit [BUS_AW-1:0]  addr,
                         input bit               write,
                         inout bit [BUS_DW-1:0]  data,
                         input uint             tl_access_timeout_ns = default_spinwait_timeout_ns,
                         input bit [BUS_DBW-1:0] mask = '1,
                         input bit               check_rsp = 1'b1,
                         input bit               exp_err_rsp = 1'b0,
                         input bit [BUS_DW-1:0]  exp_data = 0,
                         input bit [BUS_DW-1:0]  compare_mask = '1,
                         input bit               check_exp_data = 1'b0,
                         input bit               blocking = csr_utils_pkg::default_csr_blocking,
                         input mubi4_t           instr_type = MuBi4False,
                         tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h,
                         input tl_intg_err_e     tl_intg_err_type = TlIntgErrNone);

    bit completed, saw_err;
    tl_access_w_abort(addr, write, data, completed, saw_err, tl_access_timeout_ns, mask, check_rsp,
                      exp_err_rsp, exp_data, compare_mask, check_exp_data, blocking, instr_type,
                      tl_sequencer_h, tl_intg_err_type);
  endtask

  // this tl_access can input req_abort_pct (pertentage to enable req abort) and output status for
  // seq to update predicted value
  virtual task tl_access_w_abort(
      input bit [BUS_AW-1:0]  addr,
      input bit               write,
      inout bit [BUS_DW-1:0]  data,
      output bit              completed,
      output bit              saw_err,
      input uint              tl_access_timeout_ns = default_spinwait_timeout_ns,
      input bit [BUS_DBW-1:0] mask = '1,
      input bit               check_rsp = 1'b1,
      input bit               exp_err_rsp = 1'b0,
      input bit [BUS_DW-1:0]  exp_data = 0,
      input bit [BUS_DW-1:0]  compare_mask = '1,
      input bit               check_exp_data = 1'b0,
      input bit               blocking = csr_utils_pkg::default_csr_blocking,
      input                   mubi4_t instr_type = MuBi4False,
      tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h,
      input                   tl_intg_err_e tl_intg_err_type = TlIntgErrNone,
      input int               req_abort_pct = 0);

    cip_tl_seq_item rsp;
    bit                       use_rsp_ff = 0; //fixme
    if (blocking) begin
      tl_access_sub(addr, write, data, completed, saw_err, rsp, tl_access_timeout_ns, mask,
                    check_rsp, exp_err_rsp, exp_data, compare_mask, check_exp_data, req_abort_pct,
                    instr_type, tl_sequencer_h, tl_intg_err_type);
    end else begin
      fork
        tl_access_sub(addr, write, data, completed, saw_err, rsp, tl_access_timeout_ns, mask,
                      check_rsp, exp_err_rsp, exp_data, compare_mask, check_exp_data,
                      req_abort_pct, instr_type, tl_sequencer_h, tl_intg_err_type);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  virtual task tl_access_sub(input bit [BUS_AW-1:0]  addr,
                             input bit               write,
                             inout bit [BUS_DW-1:0]  data,
                             output bit              completed,
                             output bit              saw_err,
                             output                  cip_tl_seq_item rsp,
                             input                   uint tl_access_timeout_ns = default_spinwait_timeout_ns,
                             input bit [BUS_DBW-1:0] mask = '1,
                             input bit               check_rsp = 1'b1,
                             input bit               exp_err_rsp = 1'b0,
                             input bit [BUS_DW-1:0]  exp_data = 0,
                             input bit [BUS_DW-1:0]  compare_mask = '1,
                             input bit               check_exp_data = 1'b0,
                             input int               req_abort_pct = 0,
                             input                   mubi4_t instr_type = MuBi4False,
                                                     tl_sequencer tl_sequencer_h = p_sequencer.tl_sequencer_h,
                             input                   tl_intg_err_e tl_intg_err_type = TlIntgErrNone,
                             input bit               use_rsp_ff = 1'b0);
    bit [BUS_AW:0]                                   ff_data;
    `DV_SPINWAIT(
        // thread to read/write tlul
        cip_tl_host_single_seq tl_seq;
        `uvm_create_on(tl_seq, tl_sequencer_h)
        tl_seq.instr_type = instr_type;
        tl_seq.tl_intg_err_type = tl_intg_err_type;
        if (cfg.zero_delays) begin
          tl_seq.min_req_delay = 0;
          tl_seq.max_req_delay = 0;
        end
        tl_seq.req_abort_pct = req_abort_pct;
        csr_utils_pkg::increment_outstanding_access();
        `DV_CHECK_RANDOMIZE_WITH_FATAL(tl_seq,
            addr  == local::addr;
            write == local::write;
            mask  == local::mask;
            data  == local::data;)

        `uvm_send_pri(tl_seq, 100)
        rsp = tl_seq.rsp;

        if (!write) begin
          data = rsp.d_data;
          if (check_exp_data && !cfg.under_reset) begin
            bit [BUS_DW-1:0] masked_data = data & compare_mask;
            exp_data &= compare_mask;
            `DV_CHECK_EQ(masked_data, exp_data, $sformatf("addr 0x%0h read out mismatch", addr))
          end
        end
        if (check_rsp && !cfg.under_reset && tl_intg_err_type == TlIntgErrNone) begin
          `DV_CHECK_EQ(rsp.d_error, exp_err_rsp,
                       $sformatf("unexpected error response for addr: 0x%x", rsp.a_addr))
        end

        // Expose whether the transaction ran and whether it generated an error. Note that we
        // probably only want to do a RAL update if it ran and caused no error.
        completed = rsp.rsp_completed;
        saw_err = rsp.d_error;

        csr_utils_pkg::decrement_outstanding_access();,
        // thread to check timeout
        $sformatf("Timeout waiting tl_access : addr=0x%0h", addr),
        // Timeout parameter
        tl_access_timeout_ns)
  endtask

  // CIP spec indicates all comportable IPs will have the same standardized interrupt csrs. We can
  // leverage that to create a common set of tasks that all IP environments can reuse. The following
  // are descriptions of some of the args:

  // interrupts: bit vector indicating which interrupts to process
  // suffix: if there are more than BUS_DW interrupts, then add suffix 'hi' or 'lo' to the interrupt
  // TODO add support for suffix
  // csr to configure the right one (ex: intr_enable_hi, intr_enable_lo, etc)
  // indices[$]: registers could be indexed (example, rv_timer) in which case, push as many desired
  // index values as required by the design to the queue
  // scope: for top level, specify which ip / sub module's interrupt to clear

  // common task
  local function dv_base_reg get_interrupt_csr(string csr_name,
                                               string suffix = "",
                                               int indices[$] = {},
                                               dv_base_reg_block scope = null);
    if (indices.size() != 0) begin
      foreach (indices[i]) begin
        suffix = {suffix, (i == 0) ? "" : "_", $sformatf("%0d", i)};
      end
      csr_name = {csr_name, suffix};
    end
    // check within scope first, if supplied
    if (scope != null)  begin
      get_interrupt_csr = scope.get_dv_base_reg_by_name(csr_name);
    end else begin
      get_interrupt_csr = ral.get_dv_base_reg_by_name(csr_name);
    end
  endfunction

  local function void extract_common_csrs();
    foreach (cfg.ral_models[i]) begin
      dv_base_reg regs[$];
      cfg.ral_models[i].get_dv_base_regs(regs);
      foreach (regs[i]) all_csrs.push_back(regs[i]);
    end
    foreach (all_csrs[i]) begin
      string csr_name = all_csrs[i].get_name();
      if (!uvm_re_match("intr_state*", csr_name)) begin
        intr_state_csrs.push_back(get_interrupt_csr(csr_name));
      end
    end
  endfunction

  // task to enable multiple interrupts
  // enable: if set, then selected interrupts are enabled, else disabled
  // see description above for other args
  virtual task cfg_interrupts(bit [BUS_DW-1:0] interrupts,
                              bit enable = 1'b1,
                              string suffix = "",
                              int indices[$] = {},
                              dv_base_reg_block scope = null);

    uvm_reg          csr;
    bit [BUS_DW-1:0] data;

    csr = get_interrupt_csr("intr_enable", "", indices, scope);
    data = csr.get_mirrored_value();
    if (enable) data |= interrupts;
    else        data &= ~interrupts;
    csr.set(data);
    csr_update(.csr(csr));
  endtask

  // generic task to check if given interrupt bits & status are set
  // check_set: check if interrupts are set (1) or unset (0)
  // clear: bit vector indicating which interrupt bit to clear
  // see description above for other args
  virtual task check_interrupts(bit [BUS_DW-1:0] interrupts,
                                bit check_set,
                                string suffix = "",
                                int indices[$] = {},
                                dv_base_reg_block scope = null,
                                bit [BUS_DW-1:0] clear = '1);
    uvm_reg          csr_intr_state, csr_intr_enable;
    bit [BUS_DW-1:0] act_pins;
    bit [BUS_DW-1:0] exp_pins;
    bit [BUS_DW-1:0] exp_intr_state;

    if (cfg.under_reset) return;

    act_pins = cfg.intr_vif.sample() & interrupts;
    if (check_set) begin
      csr_intr_enable = get_interrupt_csr("intr_enable", "", indices, scope);
      exp_pins = interrupts & csr_intr_enable.get_mirrored_value();
      exp_intr_state = interrupts;
    end else begin
      exp_pins = '0;
      exp_intr_state = ~interrupts;
    end
    `DV_CHECK_EQ(act_pins, exp_pins)
    csr_intr_state = get_interrupt_csr("intr_state", "", indices, scope);
    csr_rd_check(.ptr(csr_intr_state), .compare_value(exp_intr_state), .compare_mask(interrupts));

    if (check_set && |(interrupts & clear)) begin
      csr_wr(.ptr(csr_intr_state), .value(interrupts & clear));
    end
  endtask

  // some coverage sampling should be disabled when it's a CSR test
  virtual function void disable_coverage_sample_for_csr_test();
    `uvm_info(`gfn, "mubi reg coverage sampling is disabled as this is a CSR test", UVM_HIGH)
    foreach (all_csrs[i]) begin
      dv_base_reg_field fields[$];

      all_csrs[i].get_dv_base_reg_fields(fields);
      // assign null to all mubi_cov object, so that coverage sampling is skipped
      foreach (fields[j]) fields[j].mubi_cov = null;
    end
  endfunction

  // wrapper task to call common test or csr tests
  virtual task run_common_vseq_wrapper(int num_times = 1);
    if (common_seq_type == "") void'($value$plusargs("run_%0s", common_seq_type));

    disable_coverage_sample_for_csr_test();

    // check which test type
    case (common_seq_type)
      "intr_test":                     run_intr_test_vseq(num_times);
      "alert_test":                    run_alert_test_vseq(num_times);
      "tl_errors":                     run_tl_errors_vseq(num_times);
      // Each iteration only sends 1 item with TL integrity error. Increase to send at least
      // 10 x num_times integrity errors
      "tl_intg_err":                   run_tl_intg_err_vseq(10 * num_times);
      "passthru_mem_tl_intg_err":      run_passthru_mem_tl_intg_err_vseq(10 * num_times);
      // Each iteration only issues at most one reset. Increase to send at least 5 X num_times.
      "stress_all_with_rand_reset":    run_plusarg_vseq_with_rand_reset(5 * num_times);
      "same_csr_outstanding":          run_same_csr_outstanding_vseq(num_times);
      "shadow_reg_errors":             run_shadow_reg_errors(num_times);
      "shadow_reg_errors_with_csr_rw": run_shadow_reg_errors(num_times, 1);
      "mem_partial_access":            run_mem_partial_access_vseq(num_times);
      "csr_mem_rw_with_rand_reset":    run_csr_mem_rw_with_rand_reset_vseq(num_times);
      "csr_mem_rw":                    run_csr_mem_rw_vseq(num_times);
      // Increase iteration, otherwise each sec_cm is only tested 1-2 times
      "sec_cm_fi":                     run_sec_cm_fi_vseq(10 * num_times);
      default:                         run_csr_vseq_wrapper(num_times);
    endcase
  endtask

  // generic task to check interrupt test reg functionality
  virtual task run_intr_test_vseq(int num_times = 1);
    dv_base_reg intr_csrs[$];

    foreach (all_csrs[i]) begin
      string csr_name = all_csrs[i].get_name();
      if (!uvm_re_match("intr_test*", csr_name) ||
          !uvm_re_match("intr_enable*", csr_name) ||
          !uvm_re_match("intr_state*", csr_name)) begin
        intr_csrs.push_back(get_interrupt_csr(csr_name));
      end
    end

    num_times = num_times * intr_csrs.size();
    for (int trans = 1; trans <= num_times; trans++) begin
      bit [BUS_DW-1:0] num_used_bits;
      bit [BUS_DW-1:0] intr_enable_val[$];
      `uvm_info(`gfn, $sformatf("Running intr test iteration %0d/%0d", trans, num_times), UVM_LOW)

      // Random Write to all intr related registers
      intr_csrs.shuffle();
      foreach (intr_csrs[i]) begin
        uvm_reg_data_t data = $urandom();
        `uvm_info(`gfn, $sformatf("Write %s: 0x%0h", intr_csrs[i].`gfn, data), UVM_MEDIUM)
        csr_wr(.ptr(intr_csrs[i]), .value(data));
      end

      // Read all intr related csr and check interrupt pins
      intr_csrs.shuffle();
      foreach (intr_csrs[i]) begin
        uvm_reg_data_t exp_val = `gmv(intr_csrs[i]);
        uvm_reg_data_t act_val;

        csr_rd(.ptr(intr_csrs[i]), .value(act_val));
        if (cfg.under_reset) continue;
        `uvm_info(`gfn, $sformatf("Read %s: 0x%0h", intr_csrs[i].`gfn, act_val), UVM_MEDIUM)
        `DV_CHECK_EQ(exp_val, act_val, {"when reading the intr CSR", intr_csrs[i].`gfn})

        // if it's intr_state, also check the interrupt pin value
        if (!uvm_re_match("intr_state*", intr_csrs[i].get_name())) begin
          dv_utils_pkg::interrupt_t exp_intr_pin = intr_csrs[i].get_intr_pins_exp_value();
          dv_utils_pkg::interrupt_t act_intr_pin = cfg.intr_vif.sample();
          act_intr_pin &= dv_utils_pkg::interrupt_t'((1 << cfg.num_interrupts) - 1);
          `DV_CHECK_CASE_EQ(exp_intr_pin, act_intr_pin)
        end // if (!uvm_re_match
      end // foreach (intr_csrs[i])
    end // for (int trans = 1; ...
  endtask

  // Task to clear register intr status bits
  virtual task clear_all_interrupts();
    if (cfg.num_interrupts == 0) return;
    foreach (intr_state_csrs[i]) begin
      bit [BUS_DW-1:0] data;
      csr_rd(.ptr(intr_state_csrs[i]), .value(data));
      if (data != 0) begin
        `uvm_info(`gtn, $sformatf("Clearing %0s", intr_state_csrs[i].get_name()), UVM_HIGH)
        csr_wr(.ptr(intr_state_csrs[i]), .value(data));
        csr_rd(.ptr(intr_state_csrs[i]), .value(data));
        if (!cfg.under_reset) `DV_CHECK_EQ(data, 0)
        else break;
      end
    end
    if (!cfg.under_reset) `DV_CHECK_EQ(cfg.intr_vif.sample(), {NUM_MAX_INTERRUPTS{1'b0}})
  endtask

  virtual task check_no_fatal_alerts();
    // Max alert_handshake shake cycles:
    // - 20 cycles includes ack response and ack stable time.
    // - 10 is the max difference between alert clock and dut clock.
    int max_alert_handshake_cycles = 20 * 10;

    // Please only use `bypass_alert_ready_to_end_check` in top-level test.
    // Because in top-level issuing an reset takes a large amount of simulation time.
    // For IP level test, please set `exp_fatal_alert` in post_start() instead.
    bit bypass_alert_ready_to_end_check;
    void'($value$plusargs("bypass_alert_ready_to_end_check=%0b",
          bypass_alert_ready_to_end_check));
    if (cfg.list_of_alerts.size() > 0 && !bypass_alert_ready_to_end_check) begin
      int check_cycles = $urandom_range(max_alert_handshake_cycles,
                                        max_alert_handshake_cycles * 3);

      // This task allows recoverable alerts to fire, or fatal alert being triggered once by
      // `alert_test` register.
      cfg.clk_rst_vif.wait_clks(max_alert_handshake_cycles);

      repeat(check_cycles) begin
        cfg.clk_rst_vif.wait_clks(1);
        foreach (cfg.m_alert_agent_cfg[alert_name]) begin
          `DV_CHECK_EQ(0, cfg.m_alert_agent_cfg[alert_name].vif.get_alert(),
                       $sformatf("Alert %0s fired unexpectedly!", alert_name))
        end
      end
    end
  endtask

  virtual task run_alert_test_vseq(int num_times = 1);
    int num_alerts = cfg.list_of_alerts.size();
    dv_base_reg alert_test_csr = ral.get_dv_base_reg_by_name("alert_test");
    `DV_CHECK_FATAL(num_alerts > 0, "Please declare `list_of_alerts` under cfg!")

    for (int trans = 1; trans <= num_times; trans++) begin
      `uvm_info(`gfn, $sformatf("Running alert test iteration %0d/%0d", trans, num_times), UVM_LOW)

      repeat ($urandom_range(num_alerts, num_alerts * 10)) begin
        bit [BUS_DW-1:0] alert_req = $urandom_range(0, (1'b1 << num_alerts) - 1);
        csr_wr(.ptr(alert_test_csr), .value(alert_req));
        `uvm_info(`gfn, $sformatf("Write alert_test with val %0h", alert_req), UVM_HIGH)
        fork
          begin
            for (int i = 0; i < num_alerts; i++) begin
              automatic int index = i;
              automatic string alert_name = cfg.list_of_alerts[index];
              if (alert_req[index]) begin
                fork
                  begin
                    // if previous alert_handler just finish, there is a max of two clock_cycle
                    // pause in between
                    wait_alert_trigger(alert_name, .max_wait_cycle(2));

                    // write alert_test during alert handshake will be ignored
                    if ($urandom_range(1, 10) == 10) begin
                      csr_wr(.ptr(alert_test_csr), .value(1'b1 << index));
                      `uvm_info(`gfn, "Write alert_test again during alert handshake", UVM_HIGH)
                    end

                    // drive alert response sequence
                    drive_alert_rsp_and_check_handshake(alert_name, index);
                  end
                join_none
              end else begin
                fork
                  begin
                    cfg.clk_rst_vif.wait_clks($urandom_range(0, 3));
                    `DV_CHECK_EQ(cfg.m_alert_agent_cfg[alert_name].vif.get_alert(), 0,
                                 $sformatf("alert_test did not set alert:%0s", alert_name))

                    // test alert_test write when there is ongoing alert handshake
                    if ($urandom_range(1, 10) == 10) begin
                      `uvm_info(`gfn,
                                $sformatf("Write alert_test with val %0h during alert_handshake",
                                1'b1 << index), UVM_HIGH)
                      csr_wr(.ptr(alert_test_csr), .value(1'b1 << index));
                      `DV_SPINWAIT_EXIT(while (!cfg.m_alert_agent_cfg[alert_name].vif.get_alert())
                                        cfg.clk_rst_vif.wait_clks(1);,
                                        cfg.clk_rst_vif.wait_clks(2);,
                                        $sformatf("expect alert_%0d:%0s to fire",
                                                  index, alert_name))
                      drive_alert_rsp_and_check_handshake(alert_name, index);
                    end
                  end
                join_none
              end
            end // end for loop
            wait fork;
          end
        join

        // check no alert triggers continuously
        foreach (cfg.list_of_alerts[i]) begin
          `DV_CHECK_EQ(cfg.m_alert_agent_cfg[cfg.list_of_alerts[i]].vif.get_alert(), 0,
                       $sformatf("expect alert:%0s to stay low", cfg.list_of_alerts[i]))
        end
      end // end repeat
    end
  endtask

  // if alerts are triggered continuously, there are 6 cycles gap between 2 alerts. 2-3 cycles for
  // clock domain crossing, 2 for pauses, 1 for idle state.
  // So use 7 cycle for default max_wait_cycle.
  virtual task wait_alert_trigger(string alert_name, int max_wait_cycle = 7, bit wait_complete = 0);
    `DV_SPINWAIT_EXIT(while (!cfg.m_alert_agent_cfg[alert_name].vif.is_alert_handshaking())
                      cfg.clk_rst_vif.wait_clks(1);,
                      // another thread to wait for given cycles. If timeout, report an error.
                      cfg.clk_rst_vif.wait_clks(max_wait_cycle);
                      `uvm_error(`gfn, $sformatf("expect alert:%0s to fire", alert_name)))
    if (wait_complete) begin
      `DV_SPINWAIT(cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();,
                   $sformatf("timeout wait for alert handshake:%0s", alert_name))
    end
  endtask

  virtual task drive_alert_rsp_and_check_handshake(string alert_name, int alert_index);
    alert_receiver_alert_rsp_seq ack_seq =
        alert_receiver_alert_rsp_seq::type_id::create("ack_seq");
    `DV_CHECK_RANDOMIZE_FATAL(ack_seq);
    ack_seq.start(p_sequencer.alert_esc_sequencer_h[alert_name]);

    `DV_SPINWAIT(cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();,
                 $sformatf("timeout wait for alert_%0d handshake:%0s", alert_index, alert_name))

    if (cfg.m_alert_agent_cfg[alert_name].is_async) cfg.clk_rst_vif.wait_clks(2);
  endtask

  // override csr_vseq to control adapter to abort transaction
  virtual task run_csr_vseq(string csr_test_type,
                            int    num_test_csrs = 0,
                            bit    do_rand_wr_and_reset = 1,
                            dv_base_reg_block models[$] = {},
                            string ral_name = "");

    if (csr_access_abort_pct.rand_mode()) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(csr_access_abort_pct)
    end else begin
      csr_access_abort_pct = 0;
    end
    foreach (cfg.m_tl_agent_cfgs[i]) begin
      cfg.m_tl_agent_cfgs[i].csr_access_abort_pct_in_adapter = csr_access_abort_pct;
    end
    // when allowing TL transaction to be aborted, TL adapter will return status UVM_NOT_OK, skip
    // checking the status.
    if (csr_access_abort_pct > 0) csr_utils_pkg::default_csr_check = UVM_NO_CHECK;
    else                          csr_utils_pkg::default_csr_check = UVM_CHECK;
    super.run_csr_vseq(csr_test_type, num_test_csrs, do_rand_wr_and_reset, models, ral_name);
  endtask


  // Run a stress sequence (chosen by plusarg) in parallel with a TL errors vseq and then suddenly
  // inject a reset.
  virtual task run_plusarg_vseq_with_rand_reset(int num_times);
    string stress_seq_name;
    int had_stress_seq_plusarg = $value$plusargs("stress_seq=%0s", stress_seq_name);
    `DV_CHECK_FATAL(had_stress_seq_plusarg)

    run_seq_with_rand_reset_vseq(create_seq_by_name(stress_seq_name), num_times);
  endtask

  // Some blocks needs input ports and status / intr csr clean up
  // for multi loop rand_reset tests
  // override this task from {block}_common_vseq if needed
  virtual task rand_reset_eor_clean_up();
  endtask
  // Run the given sequence and possibly a TL errors vseq (if do_tl_err is set). Suddenly inject a
  // reset after at most reset_delay_bound cycles. When we come out of reset, check all CSR values
  // to ensure they are the documented reset values.
  virtual task run_seq_with_rand_reset_vseq(uvm_sequence seq,
                                            int          num_times = 1,
                                            bit          do_tl_err = 1,
                                            uint         reset_delay_bound = 10_000_000);
    `DV_CHECK_FATAL(seq != null)

    for (int i = 1; i <= num_times; i++) begin
      bit ongoing_reset;
      bit do_read_and_check_all_csrs;
      `uvm_info(`gfn, $sformatf("running run_seq_with_rand_reset_vseq iteration %0d/%0d",
                                i, num_times), UVM_LOW)
      // Arbitration: requests at highest priority granted in FIFO order, so that we can predict
      // results for many non-blocking accesses
      if (do_tl_err) p_sequencer.tl_sequencer_h.set_arbitration(UVM_SEQ_ARB_STRICT_FIFO);
      fork
        begin: isolation_fork
          fork : run_test_seqs
            begin : seq_wo_reset
              fork
                begin : tl_err_seq
                  if (do_tl_err) begin
                    run_tl_errors_vseq(.num_times($urandom_range(10, 1000)), .do_wait_clk(1'b1));
                  end
                end
                begin : run_stress_seq
                  dv_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T) dv_vseq;
                  `downcast(dv_vseq, seq.clone())

                  dv_vseq.do_apply_reset = 0;
                  dv_vseq.set_sequencer(p_sequencer);
                  `DV_CHECK_RANDOMIZE_FATAL(dv_vseq)
                  dv_vseq.start(p_sequencer);
                end
              join
              wait(ongoing_reset == 0);
              `uvm_info(`gfn, $sformatf("\nFinished run %0d/%0d w/o reset", i, num_times), UVM_LOW)
            end
            begin : issue_rand_reset
              wait_to_issue_reset(reset_delay_bound);
              ongoing_reset = 1'b1;
              `uvm_info(`gfn, $sformatf("\nReset is issued for run %0d/%0d", i, num_times), UVM_LOW)
              apply_resets_concurrently();
              do_read_and_check_all_csrs = 1'b1;
              ongoing_reset = 1'b0;
            end
          join_any
          `DV_CHECK_EQ(has_outstanding_access(),  0, "No CSR outstanding items after reset!")
          disable fork;
          `uvm_info(`gfn, $sformatf("\nStress w/ reset is done for run %0d/%0d", i, num_times),
                    UVM_LOW)
          // delay to avoid race condition when sending item and checking no item after reset occur
          // at the same time
          #1ps;
          post_apply_reset("HARD");
          if (do_read_and_check_all_csrs) read_and_check_all_csrs_after_reset();
        end : isolation_fork
      join
      rand_reset_eor_clean_up();
    end
  endtask

  // Helper function for stress_all_with_rand_reset task to wait for random time before issuing
  // reset. This function can be extended to wait for certain special timing to issue reset.
  virtual task wait_to_issue_reset(uint reset_delay_bound = 10_000_000);
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(
        rand_reset_delay,
        rand_reset_delay inside {[1:reset_delay_bound]};
    )

    cfg.clk_rst_vif.wait_clks(rand_reset_delay);
    #($urandom_range(0, cfg.clk_rst_vif.clk_period_ps) * 1ps);
  endtask

  virtual task read_and_check_all_csrs_after_reset();
    `uvm_info(`gfn, "running csr hw_reset vseq", UVM_HIGH)

    run_csr_vseq(.csr_test_type("hw_reset"), .do_rand_wr_and_reset(0));
    // abort should not occur after this, as the following is normal seq
    foreach (cfg.m_tl_agent_cfgs[i]) begin
      cfg.m_tl_agent_cfgs[i].csr_access_abort_pct_in_adapter = 0;
    end
    csr_utils_pkg::default_csr_check = UVM_CHECK;
  endtask

  virtual task run_same_csr_outstanding_vseq(int num_times);
    csr_test_type_e csr_test_type = CsrRwTest; // share the same exclusion as csr_rw_test

    for (int trans = 1; trans <= num_times; trans++) begin
      `uvm_info(`gfn, $sformatf("Running same CSR outstanding test iteration %0d/%0d",
                                 trans, num_times), UVM_LOW)
      all_csrs.shuffle();

      // first iteration already issued dut_init in pre_start
      if (trans != 1 && $urandom_range(0, 1)) dut_init();

      foreach (all_csrs[i]) begin
        uvm_reg_data_t exp_data = all_csrs[i].get_mirrored_value();
        uvm_reg_data_t rd_data, wr_data, rd_mask, wr_mask;
        csr_excl_item  csr_excl = get_excl_item(all_csrs[i]);

        rd_mask = get_mask_excl_fields(all_csrs[i], CsrExclWriteCheck, csr_test_type);
        wr_mask = get_mask_excl_fields(all_csrs[i], CsrExclWrite, csr_test_type);

        repeat ($urandom_range(2, 20)) begin
          // do read, exclude CsrExclWriteCheck, CsrExclCheck
          if ($urandom_range(0, 1) &&
              !csr_excl.is_excl(all_csrs[i], CsrExclWriteCheck, csr_test_type)) begin
            tl_access(.addr(all_csrs[i].get_address()), .write(0), .data(rd_data),
                      .exp_data(exp_data), .check_exp_data(1), .compare_mask(rd_mask),
                      .blocking(0));
          end
          // do write, exclude CsrExclWrite
          if ($urandom_range(0, 1) &&
              !csr_excl.is_excl(all_csrs[i], CsrExclWrite, csr_test_type)) begin
            // Shadowed register requires two writes and thus call predict function twice.
            int num_write = all_csrs[i].get_is_shadowed() ? 2 : 1;

            `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
            wr_data &= wr_mask;
            repeat (num_write) begin
              tl_access(.addr(all_csrs[i].get_address()), .write(1), .data(wr_data), .blocking(0));
              void'(all_csrs[i].predict(.value(wr_data), .kind(UVM_PREDICT_WRITE)));
            end
            exp_data = all_csrs[i].get_mirrored_value();
          end
        end
        csr_utils_pkg::wait_no_outstanding_access();

        // Manually lock lockable flds because we use tl_access() instead of csr_wr().
        if (all_csrs[i].is_wen_reg()) all_csrs[i].lock_lockable_flds(`gmv(all_csrs[i]));
      end
    end
  endtask

  virtual task check_fatal_alert_nonblocking(string alert_name);
    fork
      `DV_SPINWAIT_EXIT(
          forever begin
            // 1 extra cycle to make sure no race condition
            repeat (alert_esc_agent_pkg::ALERT_B2B_DELAY + 1) begin
              cfg.clk_rst_vif.wait_n_clks(1);
              if (cfg.m_alert_agent_cfg[alert_name].vif.get_alert() == 1) break;
            end
            `DV_CHECK_EQ(cfg.m_alert_agent_cfg[alert_name].vif.get_alert(), 1,
                         $sformatf("fatal error %0s does not trigger!", alert_name))
            cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();
          end,
          wait(cfg.under_reset);)
    join_none
  endtask

  // test partial mem read with non-blocking random read/write
  virtual task run_mem_partial_access_vseq(int num_times);
    `loop_ral_models_to_create_threads(
        if (cfg.ral_models[ral_name].mem_ranges.size() > 0) begin
          run_mem_partial_access_vseq_sub(num_times, ral_name);
        end)
  endtask

  virtual task run_mem_partial_access_vseq_sub(int num_times, string ral_name);
    addr_range_t loc_mem_range[$] = cfg.ral_models[ral_name].mem_ranges;
    uint num_accesses;
    // limit to 100k accesses if mem is very big
    uint max_accesses = 100_000;
    // Set a minimal access to avoid memory is too small and very little chance to read memory
    uint min_accesses = 100;
    uvm_reg_block local_ral = cfg.ral_models[ral_name];

    void'($value$plusargs("max_accesses_for_partial_mem_access_vseq=%0d", max_accesses));

    // Calculate how many accesses to run based on mem size, from 100 up to 100k.
    foreach (loc_mem_range[i]) begin
      if (get_mem_access_by_addr(local_ral, loc_mem_range[i].start_addr) != "RO") begin
        num_accesses += (loc_mem_range[i].end_addr - loc_mem_range[i].start_addr) >> 2;
        if (num_accesses >= max_accesses) begin
          num_accesses = max_accesses;
          break;
        end
      end
    end
    num_accesses = (num_accesses < min_accesses) ? min_accesses : num_accesses;

    repeat (num_accesses * num_times) begin
      if (cfg.under_reset) break;
      fork
        begin
          bit [BUS_AW-1:0]  addr;
          bit [BUS_DW-1:0]  data;
          bit [BUS_DBW-1:0] mask;
          randcase
            1: begin // write
              dv_base_mem mem;
              int mem_idx = $urandom_range(0, loc_mem_range.size - 1);
              bit write_completed, write_error;

              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr,
                  addr inside {[loc_mem_range[mem_idx].start_addr :
                                loc_mem_range[mem_idx].end_addr]};)

              if (get_mem_access_by_addr(local_ral, addr) != "RO") begin
                `downcast(mem, get_mem_by_addr(cfg.ral_models[ral_name],
                                               loc_mem_range[mem_idx].start_addr))

                if (mem.get_mem_partial_write_support()) mask = get_rand_contiguous_mask();
                else                                     mask = '1;
                data = $urandom;
                // set check_rsp to 0 to skip checking rsp in sequence, as there could be a mem
                // which always returns d_error = 1. scb will be overriden to handle it and check
                // the d_error.
                tl_access_w_abort(.addr(addr), .write(1), .data(data),
                                  .completed(write_completed), .saw_err(write_error), .check_rsp(0),
                                  .mask(mask), .blocking(1), .req_abort_pct($urandom_range(0, 100)),
                                  .tl_sequencer_h(p_sequencer.tl_sequencer_hs[ral_name]));

                if (!cfg.under_reset && write_completed && !write_error) begin
                  addr[1:0] = 0;
                  mem_exist_addr_q[ral_name].push_back(addr_mask_t'{addr, mask});
                end
              end
            end
            // Randomly pick a previously written address for partial read.
            mem_exist_addr_q[ral_name].size() > 0: begin // read
              // get all the programmed addresses and randomly pick one
              addr_mask_t addr_mask = mem_exist_addr_q[ral_name][
                   $urandom_range(0, mem_exist_addr_q[ral_name].size - 1)];

              addr = addr_mask.addr;
              if (get_mem_access_by_addr(local_ral, addr) != "WO") begin
                bit completed, saw_err;
                mask = get_rand_contiguous_mask(addr_mask.mask);
                // set check_rsp to 0 due to a reason above (in the write section)
                tl_access_w_abort(.addr(addr), .write(0), .data(data),
                                  .completed(completed), .saw_err(saw_err),
                                  .mask(mask), .blocking(1), .check_rsp(0),
                                  .req_abort_pct($urandom_range(0, 100)),
                                  .tl_sequencer_h(p_sequencer.tl_sequencer_hs[ral_name]));
              end
            end
          endcase
        end
      join_none
      #0; // for outstanding_accesses to be updated
      csr_utils_pkg::wait_if_max_outstanding_accesses_reached();
    end
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // This task runs random csr and mem accesses in parallel, which can be used to cross with
  // tl_errors and random reset
  virtual task run_csr_mem_rw_vseq(int num_times);
    fork
      begin
        `uvm_info(`gfn, "running csr rw vseq", UVM_HIGH)
        run_csr_vseq(.csr_test_type("rw"), .do_rand_wr_and_reset(0));
      end
      run_mem_partial_access_vseq(num_times);
    join
  endtask

  virtual task run_csr_mem_rw_with_rand_reset_vseq(int num_times);
    cip_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T) cip_seq;
    `downcast(cip_seq, this.clone())
    cip_seq.common_seq_type = "csr_mem_rw";
    `uvm_info(`gfn, "Running run_csr_mem_rw_with_rand_reset_vseq", UVM_HIGH)

    // The reset_delay_bound of 1000 here ensures that we don't pick an enormous delay before
    // injecting a reset. Since the IP block is otherwise quiescent, we only really care about what
    // point in a TL transaction the reset occurs. Each TL transaction takes roughly 10 cycles, so
    // there's no need to wait longer than 1000 cycles (which would be ~100 TL transactions).
    run_seq_with_rand_reset_vseq(.seq(cip_seq), .num_times(num_times), .do_tl_err(1),
                                 .reset_delay_bound(1000));
  endtask

  virtual task run_alert_rsp_seq_nonblocking();
    foreach (cfg.list_of_alerts[i]) begin
      if (cfg.m_alert_agent_cfg[cfg.list_of_alerts[i]].is_active) begin
        automatic string alert_name = cfg.list_of_alerts[i];
        fork
          begin
            fork
              forever begin
                alert_receiver_alert_rsp_seq ack_seq =
                    alert_receiver_alert_rsp_seq::type_id::create("ack_seq");
                `DV_CHECK_RANDOMIZE_FATAL(ack_seq);
                ack_seq.start(p_sequencer.alert_esc_sequencer_h[alert_name]);
              end
              begin
                wait(!en_auto_alerts_response || cfg.under_reset);
                cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();
              end
            join_any
            disable fork;
          end
        join_none
      end
    end
  endtask

  // TLUL mask must be contiguous, e.g. 'b1001, 'b1010 aren't allowed
  virtual function bit[BUS_DBW-1:0] get_rand_contiguous_mask(bit [BUS_DBW-1:0] valid_mask = '1);
    bit [BUS_DBW-1:0] mask;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask,
                                       $countones(mask ^ {mask[BUS_DBW-2:0], 1'b0}) <= 2;
                                       // for data bits aren't valid (unknown), mask bit should be 0
                                       foreach (valid_mask[i]) {
                                         !valid_mask[i] -> !mask[i];
                                       })
    return mask;
  endfunction

  // enable/disable tl_assert
  virtual function void set_tl_assert_en(bit enable, string path = "*");
    uvm_config_db#(bit)::set(null, path, "tlul_assert_en", enable);
  endfunction

endclass

`undef loop_ral_models_to_create_threads
