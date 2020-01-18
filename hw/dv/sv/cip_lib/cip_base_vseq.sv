// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_vseq #(type RAL_T               = dv_base_reg_block,
                      type CFG_T               = cip_base_env_cfg,
                      type COV_T               = cip_base_env_cov,
                      type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer)
                      extends dv_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T);
  `uvm_object_param_utils(cip_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T))

  `uvm_object_new
  // knobs to disable post_start clear interrupt routine
  bit  do_clear_all_interrupts = 1'b1;
  // csr queue for intr test/enable/state
  dv_base_reg intr_test_csrs[$];
  dv_base_reg intr_state_csrs[$];
  dv_base_reg intr_enable_csrs[$];

  // user can set the name of common seq to run directly without using $value$plusargs
  string common_seq_type;

  rand uint delay_to_reset;
  constraint delay_to_reset_c {
    delay_to_reset dist {
        [1         :1000]       :/ 1,
        [1001      :100_000]    :/ 2,
        [100_001   :1_000_000]  :/ 6,
        [1_000_001 :5_000_000]  :/ 1
    };
  }

  `include "cip_base_vseq__tl_errors.svh"

  task pre_start();
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

  // tl_access task: does a single TL_W-bit write or read transaction to the specified address
  // note that this task does not update ral model; optionally also checks for error response
  // TODO: randomize size, addr here based on given addr range, data, and mask, eventually can be
  // reused for mem_read, partial read, and hmac msg fifo write
  virtual task tl_access(input bit [TL_AW-1:0]  addr,
                         input bit              write,
                         inout bit [TL_DW-1:0]  data,
                         input bit [TL_DBW-1:0] mask = '1,
                         input bit [TL_SZW-1:0] size = 2,
                         input bit              check_rsp = 1'b1,
                         input bit              exp_err_rsp = 1'b0,
                         input bit [TL_DW-1:0]  exp_data = 0,
                         input bit              check_exp_data = 1'b0,
                         input bit [TL_DW-1:0]  compare_mask = '1,
                         input bit              blocking = csr_utils_pkg::default_csr_blocking);
    if (blocking) begin
      tl_access_sub(addr, write, data, mask, size, check_rsp, exp_err_rsp, exp_data,
                    compare_mask, check_exp_data);
    end else begin
      fork
        tl_access_sub(addr, write, data, mask, size, check_rsp, exp_err_rsp, exp_data,
                      compare_mask, check_exp_data);
      join_none
      // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
    end
  endtask

  virtual task tl_access_sub(input bit [TL_AW-1:0]  addr,
                             input bit              write,
                             inout bit [TL_DW-1:0]  data,
                             input bit [TL_DBW-1:0] mask = '1,
                             input bit [TL_SZW-1:0] size = 2,
                             input bit              check_rsp = 1'b1,
                             input bit              exp_err_rsp = 1'b0,
                             input bit [TL_DW-1:0]  exp_data = 0,
                             input bit [TL_DW-1:0]  compare_mask = '1,
                             input bit              check_exp_data = 1'b0);
    `DV_SPINWAIT(
        // thread to read/write tlul
        tl_host_single_seq  tl_seq;
        `uvm_create_on(tl_seq, p_sequencer.tl_sequencer_h)
        if (cfg.zero_delays) begin
        tl_seq.min_req_delay = 0;
        tl_seq.max_req_delay = 0;
        end
        csr_utils_pkg::increment_outstanding_access();
        `DV_CHECK_RANDOMIZE_WITH_FATAL(tl_seq,
            addr      == local::addr;
            size      == local::size;
            mask      == local::mask;
              if (write) {
                if ($countones(mask) < (1 << size)) opcode == tlul_pkg::PutPartialData;
                else opcode inside {tlul_pkg::PutPartialData, tlul_pkg::PutFullData};
                data    == local::data;
                } else {
                  opcode  == tlul_pkg::Get;
                })
        `uvm_send_pri(tl_seq, 100)
        if (!write) begin
          data = tl_seq.rsp.d_data;
          if (check_exp_data && !cfg.under_reset) begin
            bit [TL_DW-1:0] masked_data = data & compare_mask;
            exp_data &= compare_mask;
            `DV_CHECK_EQ(masked_data, exp_data, $sformatf("addr 0x%0h read out mismatch", addr))
          end
        end
        if (check_rsp && !cfg.under_reset) begin
          `DV_CHECK_EQ(tl_seq.rsp.d_error, exp_err_rsp, "unexpected error response")
        end
        csr_utils_pkg::decrement_outstanding_access();,
        // thread to check timeout
        $sformatf("Timeout waiting tl_access : addr=0x%0h", addr))
  endtask

  // CIP spec indicates all comportable IPs will have the same standardized interrupt csrs. We can
  // leverage that to create a common set of tasks that all IP environments can reuse. The following
  // are descriptions of some of the args:

  // interrupts: bit vector indicating which interrupts to process
  // suffix: if there are more than TL_DW interrupts, then add suffix 'hi' or 'lo' to the interrupt
  // TODO add support for suffix
  // csr to configure the right one (ex: intr_enable_hi, intr_enable_lo, etc)
  // indices[$]: registers could be indexed (example, rv_timer) in which case, push as many desired
  // index values as required by the design to the queue
  // scope: for top level, specify which ip / sub module's interrupt to clear

  // common task
  local function dv_base_reg get_interrupt_csr(string csr_name,
                                               string suffix = "",
                                               int indices[$] = {},
                                               uvm_reg_block scope = null);
    uvm_reg csr;
    if (indices.size() != 0) begin
      foreach (indices[i]) begin
        suffix = {suffix, (i == 0) ? "" : "_", $sformatf("%0d", i)};
      end
      csr_name = {csr_name, suffix};
    end
    // check within scope first, if supplied
    if (scope != null)  begin
      csr = scope.get_reg_by_name(csr_name);
    end else begin
      csr = ral.get_reg_by_name(csr_name);
    end
    `downcast(get_interrupt_csr, csr)
    `DV_CHECK_NE_FATAL(get_interrupt_csr, null)
  endfunction

  // function to extract common csrs and fill the respective queue
  // for ex. intr_test_csr, intr_enable_csr, intr_state_csr etc.
  local function void extract_common_csrs();
    uvm_reg all_csrs[$];
    intr_test_csrs.delete();
    intr_state_csrs.delete();
    intr_enable_csrs.delete();
    // Get all interrupt test/state/enable registers
    ral.get_registers(all_csrs);
    foreach (all_csrs[i]) begin
      string csr_name = all_csrs[i].get_name();
      if (!uvm_re_match("intr_test*", csr_name)) begin
        intr_test_csrs.push_back(get_interrupt_csr(csr_name));
      end
      else if (!uvm_re_match("intr_enable*", csr_name)) begin
        intr_enable_csrs.push_back(get_interrupt_csr(csr_name));
      end
      else if (!uvm_re_match("intr_state*", csr_name)) begin
        intr_state_csrs.push_back(get_interrupt_csr(csr_name));
      end
    end
    all_csrs.delete();
    // check intr test, enable and state queue sizes are equal
    `DV_CHECK_EQ_FATAL(intr_enable_csrs.size(), intr_test_csrs.size())
    `DV_CHECK_EQ_FATAL(intr_state_csrs.size(), intr_test_csrs.size())
  endfunction

  // task to enable multiple interrupts
  // enable: if set, then selected interrupts are enabled, else disabled
  // see description above for other args
  virtual task cfg_interrupts(bit [TL_DW-1:0] interrupts,
                              bit enable = 1'b1,
                              string suffix = "",
                              int indices[$] = {},
                              uvm_reg_block scope = null);

    uvm_reg         csr;
    bit [TL_DW-1:0] data;

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
  virtual task check_interrupts(bit [TL_DW-1:0] interrupts,
                                bit check_set,
                                string suffix = "",
                                int indices[$] = {},
                                uvm_reg_block scope = null,
                                bit [TL_DW-1:0] clear = '1);
    uvm_reg         csr;
    bit [TL_DW-1:0] act_pins;
    bit [TL_DW-1:0] exp_pins;
    bit [TL_DW-1:0] exp_intr_state;

    act_pins = cfg.intr_vif.sample() & interrupts;
    if (check_set) begin
      exp_pins = interrupts;
      exp_intr_state = interrupts;
    end else begin
      exp_pins = '0;
      exp_intr_state = ~interrupts;
    end
    // if reset, pin should be reset to 0
    if (!cfg.clk_rst_vif.rst_n) begin
      exp_pins = '0;
      exp_intr_state = '0;
      `uvm_info(`gfn, "interrupt pin expect value set to 0 due to reset", UVM_LOW)
    end
    if (!cfg.under_reset) `DV_CHECK_EQ(act_pins, exp_pins)
    csr = get_interrupt_csr("intr_state", "", indices, scope);
    csr_rd_check(.ptr(csr), .compare_value(exp_intr_state), .compare_mask(interrupts));
    if (check_set && |(interrupts & clear)) begin
      csr_wr(.csr(csr), .value(interrupts & clear));
    end
  endtask

  // wrapper task to call common test or csr tests
  virtual task run_common_vseq_wrapper(int num_times = 1);
    if (common_seq_type == "") void'($value$plusargs("run_%0s", common_seq_type));
    // check which test type
    case (common_seq_type)
      "intr_test":                  run_intr_test_vseq(num_times);
      "tl_errors":                  run_tl_errors_vseq(num_times);
      "stress_all_with_rand_reset": run_stress_all_with_rand_reset_vseq(num_times);
      "same_csr_outstanding":       run_same_csr_outstanding_vseq(num_times);
      default:                      run_csr_vseq_wrapper(num_times);
    endcase
  endtask

  // generic task to check interrupt test reg functionality
  virtual task run_intr_test_vseq(int num_times = 1);
    bit [TL_DW-1:0] exp_intr_state[$];
    int test_index[$];

    foreach (intr_test_csrs[i]) begin
      test_index.push_back(i);
      //Place holder for expected intr state value
      exp_intr_state.push_back(0);
    end

    for (int trans = 1; trans <= num_times; trans++) begin
      bit [TL_DW-1:0] num_used_bits;
      bit [TL_DW-1:0] intr_enable_val[$];
      `uvm_info(`gfn, $sformatf("Running intr test iteration %0d/%0d", trans, num_times), UVM_LOW)
      // Random Write to all intr enable registers
      test_index.shuffle();
      foreach (test_index[i]) begin
        bit [TL_DW-1:0] wr_data;
        wr_data = $urandom_range(0, ((1 << intr_enable_csrs[test_index[i]].get_n_used_bits()) - 1));
        intr_enable_val.insert(test_index[i], wr_data);
        csr_wr(.csr(intr_enable_csrs[test_index[i]]), .value(wr_data));
      end

      // Random write to all interrupt test reg
      test_index.shuffle();
      foreach (test_index[i]) begin
        bit [TL_DW-1:0] wr_data;
        wr_data = $urandom_range(1, ((1 << intr_test_csrs[test_index[i]].get_n_used_bits()) - 1));
        // Add wr_data to expected state queue
        exp_intr_state[test_index[i]] |= wr_data;
        csr_wr(.csr(intr_test_csrs[test_index[i]]), .value(wr_data));
      end

      // Read all intr state
      test_index.shuffle();
      foreach (test_index[i]) begin
        bit [TL_DW-1:0] dut_intr_state;
        `uvm_info(`gtn, $sformatf("Verifying %0s", intr_test_csrs[test_index[i]].get_full_name()),
            UVM_LOW)
        csr_rd(.ptr(intr_state_csrs[test_index[i]]), .value(dut_intr_state));
        if (!cfg.under_reset) `DV_CHECK_EQ(dut_intr_state, exp_intr_state[test_index[i]])
      end

      // check interrupt pins
      if (!cfg.under_reset) begin
        foreach (intr_test_csrs[i]) begin
          bit [TL_DW-1:0] exp_intr_pin;
          exp_intr_pin = exp_intr_state[i] & intr_enable_val[i];
          for (int j = 0; j < intr_test_csrs[i].get_n_used_bits(); j++) begin
            bit act_intr_pin_val = cfg.intr_vif.sample_pin(j + num_used_bits);
            `DV_CHECK_CASE_EQ(act_intr_pin_val, exp_intr_pin[j], $sformatf(
                "exp_intr_state: 0x%0h, en_intr: 0x%0h", exp_intr_state[i], intr_enable_val[i]))
          end
          num_used_bits += intr_test_csrs[i].get_n_used_bits();
        end
      end

      // clear random bits of intr state
      test_index.shuffle();
      foreach (test_index[i]) begin
        if ($urandom_range(0, 1)) begin
          bit [TL_DW-1:0] wr_data;
          wr_data = $urandom_range((1 << intr_state_csrs[test_index[i]].get_n_used_bits()) - 1);
          exp_intr_state[test_index[i]] &= (~wr_data);
          csr_wr(.csr(intr_state_csrs[test_index[i]]), .value(wr_data));
        end
      end
    end
  endtask

  // Task to clear register intr status bits
  virtual task clear_all_interrupts();
    bit [TL_DW-1:0] data;
    foreach (intr_state_csrs[i]) begin
      csr_rd(.ptr(intr_state_csrs[i]), .value(data));
      if (data != 0) begin
        `uvm_info(`gtn, $sformatf("Clearing %0s", intr_state_csrs[i].get_name()), UVM_HIGH)
        csr_wr(.csr(intr_state_csrs[i]), .value(data));
        csr_rd(.ptr(intr_state_csrs[i]), .value(data));
        if (!cfg.under_reset) `DV_CHECK_EQ(data, 0)
        else                  break;
      end
    end
    if (!cfg.under_reset) `DV_CHECK_EQ(cfg.intr_vif.sample(), {NUM_MAX_INTERRUPTS{1'b0}})
  endtask

  // task to insert random reset within the input vseqs list, then check all CSR values
  virtual task run_stress_all_with_rand_reset_vseq(int num_times = 1, bit do_tl_err = 1);
    string stress_seq_name;
    void'($value$plusargs("stress_seq=%0s", stress_seq_name));

    for (int i = 1; i <= num_times; i++) begin
      bit ongoing_reset;
      bit do_read_and_check_all_csrs;
      // use weight arbitration to lower the priority of tl_error seq
      if (do_tl_err) p_sequencer.tl_sequencer_h.set_arbitration(UVM_SEQ_ARB_WEIGHTED);
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
                begin : stress_seq
                  uvm_sequence seq;
                  dv_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T) dv_vseq;

                  seq = create_seq_by_name(stress_seq_name);
                  `downcast(dv_vseq, seq)
                  dv_vseq.do_dut_init = 0;
                  dv_vseq.set_sequencer(p_sequencer);
                  `DV_CHECK_RANDOMIZE_FATAL(dv_vseq)
                  dv_vseq.start(p_sequencer);
                end
              join
              wait (ongoing_reset == 0);
              `uvm_info(`gfn, $sformatf("Finished run %0d/%0d w/o reset", i, num_trans), UVM_LOW)
            end
            begin : issue_rand_reset
              cfg.clk_rst_vif.wait_clks(delay_to_reset);
              ongoing_reset = 1'b1;
              `uvm_info(`gfn, $sformatf("Reset is issued for run %0d/%0d", i, num_trans), UVM_LOW)
              apply_reset("HARD");
              ongoing_reset = 1'b0;
              do_read_and_check_all_csrs = 1'b1;
              csr_utils_pkg::clear_outstanding_access();
            end
          join_any
          p_sequencer.tl_sequencer_h.stop_sequences();
          disable fork;
          `uvm_info(`gfn, $sformatf("Stress w/ reset is done for run %0d/%0d", i, num_trans),
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
    csr_excl_item csr_excl = create_and_add_csr_excl("hw_reset");
    `uvm_info(`gfn, "running csr hw_reset vseq", UVM_HIGH)
    run_csr_vseq(.csr_test_type("hw_reset"), .csr_excl(csr_excl), .do_rand_wr_and_reset(0));
  endtask

  virtual task run_same_csr_outstanding_vseq(int num_times);
    csr_excl_item csr_excl = create_and_add_csr_excl("csr_excl");
    uvm_reg     test_csrs[$];
    ral.get_registers(test_csrs);

    for (int trans = 1; trans <= num_times; trans++) begin
      `uvm_info(`gfn, $sformatf("Running same CSR outstanding test iteration %0d/%0d",
                                 trans, num_times), UVM_LOW)
      test_csrs.shuffle();

      foreach (test_csrs[i]) begin
        uvm_reg_data_t exp_data = test_csrs[i].get_reset();
        uvm_reg_data_t rd_data, wr_data, rd_mask, wr_mask;

        rd_mask = get_mask_excl_fields(test_csrs[i], CsrExclWriteCheck, csr_excl);
        wr_mask = get_mask_excl_fields(test_csrs[i], CsrExclWrite, csr_excl);

        // reset before every csr to avoid situation of writing one csr affect another's value
        dut_init("HARD");
        repeat ($urandom_range(10, 100)) begin
          // do read, exclude CsrExclWriteCheck, CsrExclCheck
          if ($urandom_range(0, 1) && !csr_excl.is_excl(test_csrs[i], CsrExclWriteCheck)) begin
            tl_access(.addr(test_csrs[i].get_address()), .write(0), .data(rd_data),
                      .exp_data(exp_data), .check_exp_data(1), .compare_mask(rd_mask), .blocking(0));
          end
          // do write, exclude CsrExclWrite
          if ($urandom_range(0, 1) && !csr_excl.is_excl(test_csrs[i], CsrExclWrite)) begin
            uvm_reg_field csr_fields[$];
            test_csrs[i].get_fields(csr_fields);
            `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
            wr_data &= wr_mask;
            tl_access(.addr(test_csrs[i].get_address()), .write(1), .data(wr_data), .blocking(0));
            void'(test_csrs[i].predict(.value(wr_data), .kind(UVM_PREDICT_WRITE)));
            exp_data = test_csrs[i].get_mirrored_value();
          end
        end
        csr_utils_pkg::wait_no_outstanding_access();
      end
    end
  endtask

  virtual task run_alert_rsp_seq_nonblocking();
    foreach(cfg.list_of_alerts[i]) begin
      automatic string seqr_name = cfg.list_of_alerts[i];
      fork
        forever begin
          alert_receiver_alert_rsp_seq ack_seq =
              alert_receiver_alert_rsp_seq::type_id::create("ack_seq");
          `DV_CHECK_RANDOMIZE_FATAL(ack_seq);
          ack_seq.start(p_sequencer.alert_esc_sequencer_h[seqr_name]);
        end
      join_none
    end
  endtask
endclass
