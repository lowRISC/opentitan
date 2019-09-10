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
  bit do_clear_all_interrupts = 1'b1;

  task pre_start();
    super.pre_start();
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
  // TODO: add additional args? non-blocking? respose data check? timeout? spinwait?
  virtual task tl_access(input bit [TL_AW-1:0]  addr,
                         input bit              write,
                         inout bit [TL_DW-1:0]  data,
                         input bit [TL_DBW-1:0] mask = '1,
                         input bit [TL_SZW-1:0] size = 2,
                         input bit              check_rsp = 1'b1,
                         input bit              exp_err_rsp = 1'b0);
    tl_host_single_seq  tl_seq;
    `uvm_create_on(tl_seq, p_sequencer.tl_sequencer_h)
    if (cfg.zero_delays) begin
      tl_seq.min_req_delay = 0;
      tl_seq.max_req_delay = 0;
    end
    `DV_CHECK_RANDOMIZE_WITH_FATAL(tl_seq,
        addr      == local::addr;
        size      == local::size;
        mask      == local::mask;
        if (write) {
          opcode  == ((size == 2) ? tlul_pkg::PutFullData : tlul_pkg::PutPartialData);
          data    == local::data;
        } else {
          opcode  == tlul_pkg::Get;
        })
    `uvm_send(tl_seq)
    if (!write) data = tl_seq.rsp.d_data;
    if (check_rsp) begin
      `DV_CHECK_EQ(tl_seq.rsp.d_error, exp_err_rsp, "unexpected error response")
    end
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
    `DV_CHECK_EQ(act_pins, exp_pins)
    csr = get_interrupt_csr("intr_state", "", indices, scope);
    csr_rd_check(.ptr(csr), .compare_value(exp_intr_state), .compare_mask(interrupts));
    if (check_set && |(interrupts & clear)) begin
      csr_wr(.csr(csr), .value(interrupts & clear));
    end
  endtask

  // wrapper task to call common test or csr tests
  virtual task run_common_vseq_wrapper(int num_times = 1);
    string test_type;
    void'($value$plusargs("run_%0s", test_type));
    // check which test type
    case (test_type)
      "intr_test": run_intr_test_vseq(num_times);
      default    : run_csr_vseq_wrapper(num_times);
    endcase
  endtask

  // generic task to check interrupt test reg functionality
  virtual task run_intr_test_vseq(int num_times = 1);
    uvm_reg     all_csrs[$];
    dv_base_reg intr_test_csrs[$];
    dv_base_reg intr_state_csrs[$];
    dv_base_reg intr_enable_csrs[$];
    bit [TL_DW-1:0] exp_intr_state[$];
    int test_index[$];

    // Get all interrupt test/state/enable registers
    ral.get_registers(all_csrs);
    foreach (all_csrs[i]) begin
      string csr_name = all_csrs[i].get_name();
      if (!uvm_re_match("intr_test*", csr_name)) begin
        test_index.push_back(intr_test_csrs.size());
        intr_test_csrs.push_back(get_interrupt_csr(csr_name));
      end
      else if (!uvm_re_match("intr_enable*", csr_name)) begin
        intr_enable_csrs.push_back(get_interrupt_csr(csr_name));
      end
      else if (!uvm_re_match("intr_state*", csr_name)) begin
        intr_state_csrs.push_back(get_interrupt_csr(csr_name));
        //Place holder for expected intr state value
        exp_intr_state.push_back(0);
      end
    end
    all_csrs.delete();

    // check intr test, enable and state queue sizes are equal
    `DV_CHECK_EQ_FATAL(intr_enable_csrs.size(), intr_test_csrs.size())
    `DV_CHECK_EQ_FATAL(intr_state_csrs.size(), intr_test_csrs.size())

    for (int trans = 1; trans <= num_times; trans++) begin
      bit [TL_DW-1:0] num_used_bits;
      bit [TL_DW-1:0] intr_enable_val[$];
      `uvm_info(`gfn, $sformatf("Running intr test iteration %0d/%0d", trans, num_times), UVM_LOW)
      // Random Write to all intr enable registers
      test_index.shuffle();
      foreach (test_index[i]) begin
        bit [TL_DW-1:0] wr_data;
        wr_data = $urandom_range(1, ((1 << intr_enable_csrs[test_index[i]].get_n_used_bits()) - 1));
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
        `DV_CHECK_EQ(dut_intr_state, exp_intr_state[test_index[i]])
      end

      // check interrupt pins
      foreach (intr_test_csrs[i]) begin
        bit [TL_DW-1:0] exp_intr_pin;
        exp_intr_pin = exp_intr_state[i] & intr_enable_val[i];
        for (int j = 0; j < intr_test_csrs[i].get_n_used_bits(); j++) begin
          bit act_intr_pin_val = cfg.intr_vif.sample_pin(j + num_used_bits);
          `DV_CHECK_CASE_EQ(act_intr_pin_val, exp_intr_pin[j], $sformatf(
              "exp_intr_state: %0h, en_intr: %0h", exp_intr_state[i], intr_enable_val[i]))
        end
        num_used_bits += intr_test_csrs[i].get_n_used_bits();
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
    uvm_reg     all_csrs[$];
    dv_base_reg csr;
    bit [TL_DW-1:0] data;
    bit [TL_DW-1:0] num_used_bits;
    ral.get_registers(all_csrs);
    foreach (all_csrs[i]) begin
      string csr_name = all_csrs[i].get_name();
      if (!uvm_re_match("intr_state*", csr_name)) begin
        csr = get_interrupt_csr(csr_name);
        csr_rd(.ptr(csr), .value(data));
        if (data != 0) begin
          `uvm_info(`gtn, $sformatf("Clearing %0s", csr.get_name()), UVM_HIGH)
          csr_wr(.csr(csr), .value(data));
          csr_rd(.ptr(csr), .value(data));
          `DV_CHECK_EQ(data, 0)
        end
        // check interrupt pins
        for (int j = 0; j < csr.get_n_used_bits(); j++) begin
          bit act_intr_pin_val = cfg.intr_vif.sample_pin(j + num_used_bits);
          `DV_CHECK_CASE_EQ(act_intr_pin_val, 0)
        end
        num_used_bits += csr.get_n_used_bits();
      end
    end
    all_csrs.delete();
  endtask

endclass
