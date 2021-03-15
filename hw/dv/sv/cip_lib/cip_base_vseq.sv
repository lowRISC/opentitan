// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_vseq #(type RAL_T               = dv_base_reg_block,
                      type CFG_T               = cip_base_env_cfg,
                      type COV_T               = cip_base_env_cov,
                      type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer)
                      extends dv_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T);
  `uvm_object_new
  // knobs to disable post_start clear interrupt routine
  bit do_clear_all_interrupts = 1'b1;

  // knobs to enable alert auto reponse, once disabled it won't be able to enable again unless
  // dut_init is issued
  bit en_auto_alerts_response = 1'b1;

  // knobs to lock shadow register write access if fatal storage error occurred
  bit do_lock_shadow_reg = 1'b1;

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

  addr_mask_t mem_exist_addr_q[$];

  // mem_ranges without base address
  addr_range_t     updated_mem_ranges[$];
  // mask out bits out of the csr/mem range and LSB 2 bits
  bit [BUS_AW-1:0] csr_addr_mask;

  rand uint delay_to_reset;
  constraint delay_to_reset_c {
    delay_to_reset dist {
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
    `uvm_field_queue_int(mem_exist_addr_q, UVM_DEFAULT)
  `uvm_object_utils_end

  `include "cip_base_vseq__tl_errors.svh"

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    if (en_auto_alerts_response && cfg.list_of_alerts.size()) run_alert_rsp_seq_nonblocking();
  endtask

  task pre_start();
    if (common_seq_type == "") void'($value$plusargs("run_%0s", common_seq_type));
    if (common_seq_type == "alert_test") en_auto_alerts_response = 0;

    // num_trans is constrained to a small number for CSR test in common test, need a bigger number
    // for stress_all with reset
    if (common_seq_type == "stress_all_with_rand_reset") begin
      num_trans_c.constraint_mode(0);
      num_trans = $urandom_range(5, 10);
    end
    csr_utils_pkg::max_outstanding_accesses = 1 << BUS_AIW;
    super.pre_start();
    extract_common_csrs();
  endtask

  task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask : body

  task post_start();
    super.post_start();
    void'($value$plusargs("do_clear_all_interrupts=%0b", do_clear_all_interrupts));
    if (do_clear_all_interrupts) clear_all_interrupts();
  endtask

  // tl_access task: does a single BUS_DW-bit write or read transaction to the specified address
  // note that this task does not update ral model; optionally also checks for error response
  // TODO: randomize size, addr here based on given addr range, data, and mask, eventually can be
  // reused for mem_read, partial read, and hmac msg fifo write
  virtual task tl_access(input bit [BUS_AW-1:0]  addr,
                         input bit               write,
                         inout bit [BUS_DW-1:0]  data,
                         input bit [BUS_DBW-1:0] mask = '1,
                         input bit               check_rsp = 1'b1,
                         input bit               exp_err_rsp = 1'b0,
                         input bit [BUS_DW-1:0]  exp_data = 0,
                         input bit [BUS_DW-1:0]  compare_mask = '1,
                         input bit               check_exp_data = 1'b0,
                         input bit               blocking = csr_utils_pkg::default_csr_blocking,
                         tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h);
    uvm_status_e status;
    tl_access_w_abort(addr, write, data, status, mask, check_rsp, exp_err_rsp, exp_data,
                      compare_mask, check_exp_data, blocking, tl_sequencer_h);
  endtask

  // this tl_access can input req_abort_pct (pertentage to enable req abort) and output status for
  // seq to update predicted value
  virtual task tl_access_w_abort(
      input bit [BUS_AW-1:0]  addr,
      input bit               write,
      inout bit [BUS_DW-1:0]  data,
      output uvm_status_e     status,
      input bit [BUS_DBW-1:0] mask = '1,
      input bit               check_rsp = 1'b1,
      input bit               exp_err_rsp = 1'b0,
      input bit [BUS_DW-1:0]  exp_data = 0,
      input bit [BUS_DW-1:0]  compare_mask = '1,
      input bit               check_exp_data = 1'b0,
      input bit               blocking = csr_utils_pkg::default_csr_blocking,
      tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h,
      input int               req_abort_pct = 0);

    if (blocking) begin
      tl_access_sub(addr, write, data, status, mask, check_rsp, exp_err_rsp, exp_data,
                    compare_mask, check_exp_data, req_abort_pct, tl_sequencer_h);
    end else begin
      fork
        tl_access_sub(addr, write, data, status, mask, check_rsp, exp_err_rsp, exp_data,
                      compare_mask, check_exp_data, req_abort_pct, tl_sequencer_h);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  virtual task tl_access_sub(input bit [BUS_AW-1:0]  addr,
                             input bit               write,
                             inout bit [BUS_DW-1:0]  data,
                             output uvm_status_e     status,
                             input bit [BUS_DBW-1:0] mask = '1,
                             input bit               check_rsp = 1'b1,
                             input bit               exp_err_rsp = 1'b0,
                             input bit [BUS_DW-1:0]  exp_data = 0,
                             input bit [BUS_DW-1:0]  compare_mask = '1,
                             input bit               check_exp_data = 1'b0,
                             input int               req_abort_pct = 0,
                             tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h);
    `DV_SPINWAIT(
        // thread to read/write tlul
        tl_host_single_seq  tl_seq;
        `uvm_create_on(tl_seq, tl_sequencer_h)
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
        if (!write) begin
          data = tl_seq.rsp.d_data;
          if (check_exp_data && !cfg.under_reset) begin
            bit [BUS_DW-1:0] masked_data = data & compare_mask;
            exp_data &= compare_mask;
            `DV_CHECK_EQ(masked_data, exp_data, $sformatf("addr 0x%0h read out mismatch", addr))
          end
        end
        if (check_rsp && !cfg.under_reset) begin
          `DV_CHECK_EQ(tl_seq.rsp.d_error, exp_err_rsp, "unexpected error response")
        end

        // when error occurs or item isn't completed, use status to let seq not update predicted
        // value
        if (tl_seq.rsp.d_error || !tl_seq.rsp.rsp_completed) status = UVM_NOT_OK;
        else                                                 status = UVM_IS_OK;

        csr_utils_pkg::decrement_outstanding_access();,
        // thread to check timeout
        $sformatf("Timeout waiting tl_access : addr=0x%0h", addr))
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
    foreach (cfg.ral_models[i]) cfg.ral_models[i].get_dv_base_regs(all_csrs);
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
      csr_wr(.csr(csr_intr_state), .value(interrupts & clear));
    end
  endtask

  // wrapper task to call common test or csr tests
  virtual task run_common_vseq_wrapper(int num_times = 1);
    if (common_seq_type == "") void'($value$plusargs("run_%0s", common_seq_type));
    // check which test type
    case (common_seq_type)
      "intr_test":                  run_intr_test_vseq(num_times);
      "alert_test":                 run_alert_test_vseq(num_times);
      "tl_errors":                  run_tl_errors_vseq(num_times);
      "stress_all_with_rand_reset": run_stress_all_with_rand_reset_vseq(num_times);
      "same_csr_outstanding":       run_same_csr_outstanding_vseq(num_times);
      "shadow_reg_errors":          run_shadow_reg_errors(num_times);
      "mem_partial_access":         run_mem_partial_access_vseq(num_times);
      "csr_mem_rw_with_rand_reset": run_csr_mem_rw_with_rand_reset_vseq(num_times);
      "csr_mem_rw":                 run_csr_mem_rw_vseq(num_times);
      default:                      run_csr_vseq_wrapper(num_times);
    endcase
  endtask

  // generic task to check interrupt test reg functionality
  virtual task run_intr_test_vseq(int num_times = 1);
    dv_base_reg all_intr_csrs[$];

    foreach (all_csrs[i]) begin
      string csr_name = all_csrs[i].get_name();
      if (!uvm_re_match("intr_test*", csr_name) ||
          !uvm_re_match("intr_enable*", csr_name) ||
          !uvm_re_match("intr_state*", csr_name)) begin
        all_intr_csrs.push_back(get_interrupt_csr(csr_name));
      end
    end

    num_times = num_times * all_intr_csrs.size;
    for (int trans = 1; trans <= num_times; trans++) begin
      bit [BUS_DW-1:0] num_used_bits;
      bit [BUS_DW-1:0] intr_enable_val[$];
      `uvm_info(`gfn, $sformatf("Running intr test iteration %0d/%0d", trans, num_times), UVM_LOW)

      // Random Write to all intr related registers
      all_intr_csrs.shuffle();
      foreach (all_intr_csrs[i]) begin
        uvm_reg_data_t data = $urandom;
        `uvm_info(`gfn, $sformatf("Write intr CSR %s: 0x%0h", all_intr_csrs[i].get_name(), data),
                  UVM_MEDIUM)
        csr_wr(.csr(all_intr_csrs[i]), .value(data));
      end

      // Read all intr related csr and check interrupt pins
      all_intr_csrs.shuffle();
      foreach (all_intr_csrs[i]) begin
        dv_base_reg csr = all_intr_csrs[i];
        uvm_reg_data_t act_val;
        string csr_name = csr.get_name();

        csr_rd(.ptr(csr), .value(act_val));
        `uvm_info(`gfn, $sformatf("Read %s: 0x%0h", csr.get_full_name(), act_val),
            UVM_MEDIUM)

        if (cfg.under_reset) continue;

        `DV_CHECK_EQ(act_val, `gmv(csr))

        // if it's intr_state, also check the interrupt pin value
        if (!uvm_re_match("intr_state*", csr_name)) begin
          uvm_reg_data_t exp_intr_pin = csr.get_intr_pins_exp_value();

          for (int j = 0; j < csr.get_n_used_bits(); j++) begin
            bit act_intr_pin_val = cfg.intr_vif.sample_pin(j);
            `DV_CHECK_CASE_EQ(act_intr_pin_val, exp_intr_pin[j])
          end // for
        end // if (!uvm_re_match
      end // foreach (all_intr_csrs[i])
    end // for (int trans = 1; ...
  endtask

  // Task to clear register intr status bits
  virtual task clear_all_interrupts();
    foreach (intr_state_csrs[i]) begin
      bit [BUS_DW-1:0] data;
      csr_rd(.ptr(intr_state_csrs[i]), .value(data));
      if (data != 0) begin
        `uvm_info(`gtn, $sformatf("Clearing %0s", intr_state_csrs[i].get_name()), UVM_HIGH)
        csr_wr(.csr(intr_state_csrs[i]), .value(data));
        csr_rd(.ptr(intr_state_csrs[i]), .value(data));
        if (!cfg.under_reset) `DV_CHECK_EQ(data, 0)
        else break;
      end
    end
    if (!cfg.under_reset) `DV_CHECK_EQ(cfg.intr_vif.sample(), {NUM_MAX_INTERRUPTS{1'b0}})
  endtask

  virtual task run_alert_test_vseq(int num_times = 1);
    int num_alerts = cfg.list_of_alerts.size();
    dv_base_reg alert_test_csr = ral.get_dv_base_reg_by_name("alert_test");

    for (int trans = 1; trans <= num_times; trans++) begin
      `uvm_info(`gfn, $sformatf("Running alert test iteration %0d/%0d", trans, num_times), UVM_LOW)

      repeat ($urandom_range(num_alerts, num_alerts * 10)) begin
        bit [BUS_DW-1:0] alert_req = $urandom_range(0, (1'b1 << num_alerts) - 1);
        csr_wr(.csr(alert_test_csr), .value(alert_req));
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
                    `DV_SPINWAIT_EXIT(while (!cfg.m_alert_agent_cfg[alert_name].vif.get_alert())
                                      cfg.clk_rst_vif.wait_clks(1);,
                                      cfg.clk_rst_vif.wait_clks(2);,
                                      $sformatf("expect alert_%0d:%0s to fire", index, alert_name))

                    // write alert_test during alert handshake will be ignored
                    if ($urandom_range(1, 10) == 10) begin
                      csr_wr(.csr(alert_test_csr), .value(1'b1 << index));
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
                      csr_wr(.csr(alert_test_csr), .value(1'b1 << index));
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
  virtual task run_csr_vseq(string          csr_test_type = "",
                            csr_excl_item   csr_excl = null,
                            int             num_test_csrs = 0,
                            bit             do_rand_wr_and_reset = 1);

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(csr_access_abort_pct)
    cfg.m_tl_agent_cfg.csr_access_abort_pct_in_adapter = csr_access_abort_pct;
    // when allowing TL transaction to be aborted, TL adapter will return status UVM_NOT_OK, skip
    // checking the status.
    if (csr_access_abort_pct > 0) csr_utils_pkg::default_csr_check = UVM_NO_CHECK;
    else                          csr_utils_pkg::default_csr_check = UVM_CHECK;
    super.run_csr_vseq(csr_test_type, csr_excl, num_test_csrs, do_rand_wr_and_reset);
  endtask


  // task to insert random reset within the input vseqs list, then check all CSR values
  virtual task run_stress_all_with_rand_reset_vseq(int num_times = 1, bit do_tl_err = 1,
                                                   uvm_sequence seq = null);
    string stress_seq_name;
    void'($value$plusargs("stress_seq=%0s", stress_seq_name));

    for (int i = 1; i <= num_times; i++) begin
      bit ongoing_reset;
      bit do_read_and_check_all_csrs;
      `uvm_info(`gfn, $sformatf("running run_stress_all_with_rand_reset_vseq iteration %0d/%0d",
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
                  if (seq == null) begin
                    `downcast(dv_vseq, create_seq_by_name(stress_seq_name))
                  end else begin
                    `downcast(dv_vseq, seq.clone())
                  end
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
              `DV_CHECK_MEMBER_RANDOMIZE_FATAL(delay_to_reset)
              cfg.clk_rst_vif.wait_clks(delay_to_reset);
              ongoing_reset = 1'b1;
              `uvm_info(`gfn, $sformatf("\nReset is issued for run %0d/%0d", i, num_times), UVM_LOW)
              apply_reset("HARD");
              ongoing_reset = 1'b0;
              do_read_and_check_all_csrs = 1'b1;
            end
          join_any
          disable fork;
          `uvm_info(`gfn, $sformatf("\nStress w/ reset is done for run %0d/%0d", i, num_times),
                    UVM_LOW)
          // delay to avoid race condition when sending item and checking no item after reset occur
          // at the same time
          #1ps;
          if (do_read_and_check_all_csrs) read_and_check_all_csrs_after_reset();
        end : isolation_fork
      join
    end
  endtask

  virtual task read_and_check_all_csrs_after_reset();
    csr_excl_item csr_excl = add_and_return_csr_excl("hw_reset");
    `uvm_info(`gfn, "running csr hw_reset vseq", UVM_HIGH)

    run_csr_vseq(.csr_test_type("hw_reset"), .csr_excl(csr_excl), .do_rand_wr_and_reset(0));
    // abort should not occur after this, as the following is normal seq
    cfg.m_tl_agent_cfg.csr_access_abort_pct_in_adapter = 0;
    csr_utils_pkg::default_csr_check = UVM_CHECK;
  endtask

  virtual task run_same_csr_outstanding_vseq(int num_times);
    csr_excl_item   csr_excl = add_and_return_csr_excl("csr_excl");
    csr_test_type_e csr_test_type = CsrRwTest; // share the same exclusion as csr_rw_test
    dv_base_reg     test_csrs[$];

    ral.get_dv_base_regs(test_csrs);

    for (int trans = 1; trans <= num_times; trans++) begin
      `uvm_info(`gfn, $sformatf("Running same CSR outstanding test iteration %0d/%0d",
                                 trans, num_times), UVM_LOW)
      test_csrs.shuffle();

      // first iteration already issued dut_init in pre_start
      if (trans != 1 && $urandom_range(0, 1)) dut_init();

      foreach (test_csrs[i]) begin
        uvm_reg_data_t exp_data = test_csrs[i].get_mirrored_value();
        uvm_reg_data_t rd_data, wr_data, rd_mask, wr_mask;

        rd_mask = get_mask_excl_fields(test_csrs[i], CsrExclWriteCheck, csr_test_type, csr_excl);
        wr_mask = get_mask_excl_fields(test_csrs[i], CsrExclWrite, csr_test_type, csr_excl);

        repeat ($urandom_range(2, 20)) begin
          // do read, exclude CsrExclWriteCheck, CsrExclCheck
          if ($urandom_range(0, 1) &&
              !csr_excl.is_excl(test_csrs[i], CsrExclWriteCheck, csr_test_type)) begin
            tl_access(.addr(test_csrs[i].get_address()), .write(0), .data(rd_data),
                      .exp_data(exp_data), .check_exp_data(1), .compare_mask(rd_mask),
                      .blocking(0));
          end
          // do write, exclude CsrExclWrite
          if ($urandom_range(0, 1) &&
              !csr_excl.is_excl(test_csrs[i], CsrExclWrite, csr_test_type)) begin
            `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
            wr_data &= wr_mask;
            tl_access(.addr(test_csrs[i].get_address()), .write(1), .data(wr_data), .blocking(0));
            void'(test_csrs[i].predict(.value(wr_data), .kind(UVM_PREDICT_WRITE)));
            exp_data = test_csrs[i].get_mirrored_value();
          end
        end
        csr_utils_pkg::wait_no_outstanding_access();

        // Manually lock lockable flds because we use tl_access() instead of csr_wr().
        if (test_csrs[i].is_wen_reg()) test_csrs[i].lock_lockable_flds(`gmv(test_csrs[i]));
      end
    end
  endtask

  // callback for individual modules to override
  // can be used to update storage error status register
  virtual function void shadow_reg_storage_err_post_write();
  endfunction

  // alert triggers as soon as design accept the TLUL transaction, if wait until csr_wr() finishes
  // then check alert, the alert transaction might already finished
  // this task can be override in block level common_vseq for specific shadow_regs
  virtual task shadow_reg_wr(dv_base_reg csr, uvm_reg_data_t wdata, output bit alert_triggered);
    fork
      begin
        fork
          begin
            csr_wr(.csr(csr), .value(wdata), .en_shadow_wr(0), .predict(1));
          end
          begin
            string alert_name = csr.get_update_err_alert_name();
            while (1) begin
              cfg.clk_rst_vif.wait_clks(1);
              if (!alert_triggered) begin
                alert_triggered = cfg.m_alert_agent_cfg[alert_name].vif.get_alert();
              end
            end
          end
        join_any
        disable fork;
      end
    join
  endtask

  // this function will return a storage_err value to backdoor poke shadow_reg's storage registers
  // it can generate a rand value, or randomly flip one bit from the original value
  virtual function bit [BUS_DW-1:0] gen_storage_err_val(dv_base_reg csr,
                                                        bit [BUS_DW-1:0] origin_val,
                                                        bit gen_rand_val = $urandom_range(0, 1));
    int addr_index = $urandom_range(0, csr.get_msb_pos());
    int shift_bits = BUS_DW - addr_index - 1;
    gen_storage_err_val = (gen_rand_val) ? $urandom() : origin_val;
    gen_storage_err_val[addr_index] = ~gen_storage_err_val[addr_index];
    gen_storage_err_val = gen_storage_err_val << shift_bits >> shift_bits;
  endfunction

  virtual task check_fatal_alert_nonblocking(string alert_name);
    fork
      `DV_SPINWAIT_EXIT(
          forever begin
            // 1 extra cycle to make sure no race condition
            repeat(alert_esc_agent_pkg::ALERT_B2B_DELAY + 1) begin
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

  virtual task run_shadow_reg_errors(int num_times);
    csr_excl_item      csr_excl = add_and_return_csr_excl("csr_excl");
    dv_base_reg        shadowed_csrs[$], test_csrs[$];
    uvm_reg_data_t     wdata;
    bit                alert_triggered;

    ral.get_shadowed_regs(shadowed_csrs);

    for (int trans = 1; trans <= num_times; trans++) begin
      `uvm_info(`gfn, $sformatf("Running shadow reg error test iteration %0d/%0d", trans,
                                num_times), UVM_LOW)
      repeat ($urandom_range(10, 100)) begin
        all_csrs.shuffle();
        test_csrs.delete();
        test_csrs = {shadowed_csrs, all_csrs[0: $urandom_range(0, all_csrs.size()-1)]};
        test_csrs.shuffle();

        if ($urandom_range(1, 10) == 10) dut_init("HARD");

        foreach (test_csrs[i]) begin
          // check if parent block or register is excluded from write
          // if the excluded reg is shadow_reg, it won't skip writing
          if (csr_excl.is_excl(test_csrs[i], CsrExclWrite, CsrRwTest) &&
              !test_csrs[i].get_is_shadowed()) begin
            `uvm_info(`gtn, $sformatf("Skipping register %0s due to CsrExclWrite exclusion",
                                      test_csrs[i].get_full_name()), UVM_MEDIUM)
            continue;
          end

          // skip alert_test register because it will trigger alerts
          if (test_csrs[i].get_name() == "alert_test") continue;

          `DV_CHECK_STD_RANDOMIZE_FATAL(wdata)
          wdata &= get_mask_excl_fields(test_csrs[i], CsrExclWrite, CsrRwTest, csr_excl);

          // if the write is shadow register's second write, there is a 50% possibility that the
          // second write value is identical to its staged_value
          if (test_csrs[i].is_staged()) begin
            if ($urandom_range(0, 1)) wdata = test_csrs[i].get_staged_shadow_val();
          end
          if (test_csrs[i].get_is_shadowed()) shadow_reg_wr(test_csrs[i], wdata, alert_triggered);
          else csr_wr(.csr(test_csrs[i]), .value(wdata), .en_shadow_wr(0), .predict(1));

          // check shadow_reg update error
          if (test_csrs[i].get_shadow_update_err()) begin
            string alert_name = test_csrs[i].get_update_err_alert_name();
            `DV_SPINWAIT(if(!alert_triggered) begin
                           while (!cfg.m_alert_agent_cfg[alert_name].vif.get_alert())
                           cfg.clk_rst_vif.wait_clks(1);
                         end,
                         $sformatf("%0s update_err alert not detected", test_csrs[i].get_name()))
            `DV_SPINWAIT(cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();,
                         $sformatf("timeout for alert:%0s", alert_name))
            test_csrs[i].clear_shadow_update_err();
            alert_triggered = 0;
          end else if (alert_triggered) begin
            `uvm_error(`gfn, $sformatf("unexpect %0s update_err alert triggered",
                                       test_csrs[i].get_name()))
          end

          // randomly backdoor write a shadow_reg to create storage error
          if ($urandom_range(1, 10) == 10) begin
            int             index = $urandom_range(0, shadowed_csrs.size() - 1);
            uvm_reg_data_t  rand_val, origin_val;
            bkdr_reg_path_e kind;
            int             shadow_reg_width = shadowed_csrs[index].get_msb_pos() + 1;

            if (shadowed_csrs[index].shadow_reg_is_locked() == 0) begin
              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
                  kind, kind inside {BkdrRegPathRtlCommitted, BkdrRegPathRtlShadow};)
              csr_peek(.ptr(shadowed_csrs[index]), .value(origin_val), .kind(kind));
              rand_val = gen_storage_err_val(shadowed_csrs[index], origin_val);

              csr_poke(.csr(shadowed_csrs[index]), .value(rand_val), .kind(kind), .predict(1));
              `uvm_info(`gfn, $sformatf("backdoor write %0s with value %0h", kind.name, rand_val),
                        UVM_HIGH);

              // check shadow_reg storage error
              if ((origin_val ^ rand_val) & ((1 << shadow_reg_width) - 1)) begin
                string alert_name = shadowed_csrs[index].get_storage_err_alert_name();
                bit    has_storage_error;
                shadow_reg_storage_err_post_write();
                has_storage_error = shadowed_csrs[index].get_shadow_storage_err();

                if (has_storage_error && do_lock_shadow_reg) begin
                  shadowed_csrs[index].lock_shadow_reg();
                  check_fatal_alert_nonblocking(alert_name);

                  // Wait two clock cycles then backdoor write back original value.
                  // This won't stop fatal alert from firing.
                  cfg.clk_rst_vif.wait_clks(2);
                  csr_poke(.csr(shadowed_csrs[index]), .value(origin_val), .kind(kind), .predict(1));
                end else begin
                  `DV_CHECK_EQ(has_storage_error, 1,
                               "dv_base_reg did not predict shadow storage error");
                  `DV_SPINWAIT(while (!cfg.m_alert_agent_cfg[alert_name].vif.get_alert())
                               cfg.clk_rst_vif.wait_clks(1);,
                               $sformatf("%0s shadow_reg storage_err alert not detected",
                                         shadowed_csrs[index].get_name()));

                  // backdoor write back original value to avoid alert keep firing
                  csr_poke(.csr(shadowed_csrs[index]), .value(origin_val), .kind(kind), .predict(1));
                  `DV_SPINWAIT(cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();,
                               $sformatf("timeout for alert:%0s", alert_name))

                  // wait at least two clock cycle between alert_handshakes
                  cfg.clk_rst_vif.wait_clks(2);
                end
              end
            end
          end
        end

        // random read to check if the register values are equal to the predicted values,
        // reading shadow registers after their first write will clear the phase tracker
        if ($urandom_range(0, 1)) begin
          all_csrs.shuffle();
          foreach (all_csrs[i]) begin
            do_check_csr_or_field_rd(.csr(all_csrs[i]),
                                     .blocking(0),
                                     .compare(1),
                                     .compare_vs_ral(1),
                                     .csr_excl_type(CsrExclWriteCheck),
                                     .csr_test_type(CsrRwTest),
                                     .csr_excl_item(csr_excl));
            csr_utils_pkg::wait_if_max_outstanding_accesses_reached();
          end
          // read shadow_regs again in case they are excluded from read_check
          foreach (shadowed_csrs[i]) begin
            csr_rd_check(.ptr(shadowed_csrs[i]), .compare_vs_ral(1), .blocking(1));
          end
          csr_utils_pkg::wait_no_outstanding_access();
        end
      end
    end
    // Shadow register fatal error will continuously trigger alerts until reset
    dut_init();
  endtask

  // test partial mem read with non-blocking random read/write
  virtual task run_mem_partial_access_vseq(int num_times);
    uint num_accesses;
    // limit to 100k accesses if mem is very big
    uint max_accesses = 100_000;

    void'($value$plusargs("max_accesses_for_partial_mem_access_vseq=%0d", max_accesses));

    // calculate how many accesses to run based on mem size, up to 100k
    foreach (cfg.mem_ranges[i]) begin
      if (get_mem_access_by_addr(ral, cfg.mem_ranges[i].start_addr) != "RO") begin
        num_accesses += (cfg.mem_ranges[i].end_addr - cfg.mem_ranges[i].start_addr) >> 2;
        if (num_accesses >= max_accesses) begin
          num_accesses = max_accesses;
          break;
        end
      end
    end

    num_accesses = num_accesses * num_times;
    while (num_accesses) begin
      fork
        begin
          bit [BUS_AW-1:0]  addr;
          bit [BUS_DW-1:0]  data;
          bit [BUS_DBW-1:0] mask;
          uvm_status_e      status;
          randcase
            1: begin // write
              dv_base_mem mem;
              int mem_idx = $urandom_range(0, cfg.mem_ranges.size - 1);

              `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr,
                  addr inside {[cfg.mem_ranges[mem_idx].start_addr :
                                cfg.mem_ranges[mem_idx].end_addr]};)

              if (get_mem_access_by_addr(ral, addr) != "RO") begin
                `downcast(mem, get_mem_by_addr(ral, cfg.mem_ranges[mem_idx].start_addr))
                if (mem.get_mem_partial_write_support()) mask = get_rand_contiguous_mask();
                else                                     mask = '1;
                data = $urandom;
                tl_access_w_abort(.addr(addr), .write(1), .data(data), .status(status), .mask(mask),
                                  .blocking(1), .req_abort_pct($urandom_range(0, 100)));

                if (!cfg.under_reset && status == UVM_IS_OK) begin
                  addr[1:0] = 0;
                  mem_exist_addr_q.push_back(addr_mask_t'{addr, mask});
                end
              end
            end
            // Randomly pick a previously written address for partial read.
            mem_exist_addr_q.size() > 0: begin // read
              // get all the programmed addresses and randomly pick one
              addr_mask_t addr_mask = mem_exist_addr_q[$urandom_range(0,
                                                                      mem_exist_addr_q.size - 1)];
              // TODO, Remove this if condition when #5262 is solved
              // Only read when it's fully written
              if (addr_mask.mask == '1) begin
                addr = addr_mask.addr;
                if (get_mem_access_by_addr(ral, addr) != "WO") begin
                  mask = get_rand_contiguous_mask(addr_mask.mask);
                  tl_access_w_abort(.addr(addr), .write(0), .data(data), .status(status), .mask(mask),
                                    .blocking(1), .req_abort_pct($urandom_range(0, 100)));
                end
                num_accesses--;
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
        csr_excl_item csr_excl = add_and_return_csr_excl("rw");
        `uvm_info(`gfn, "running csr rw vseq", UVM_HIGH)
        run_csr_vseq(.csr_test_type("rw"), .csr_excl(csr_excl), .do_rand_wr_and_reset(0));
      end
      if (cfg.mem_ranges.size > 0) run_mem_partial_access_vseq(num_times);
    join
  endtask

  virtual task run_csr_mem_rw_with_rand_reset_vseq(int num_times);
    cip_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T) cip_seq;
    `downcast(cip_seq, this.clone())
    cip_seq.common_seq_type = "csr_mem_rw";
    `uvm_info(`gfn, "Running run_csr_mem_rw_with_rand_reset_vseq", UVM_HIGH)
    run_stress_all_with_rand_reset_vseq(.num_times(num_times), .do_tl_err(1),
                                        .seq(cip_seq));
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
