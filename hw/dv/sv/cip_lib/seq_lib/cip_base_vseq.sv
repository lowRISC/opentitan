// Copyright lowRISC contributors (OpenTitan project).
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

class cip_base_vseq #(
  type RAL_T               = dv_base_reg_block,
  type CFG_T               = cip_base_env_cfg,
  type COV_T               = cip_base_env_cov,
  type VIRTUAL_SEQUENCER_T = cip_base_virtual_sequencer
) extends dv_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T);
  `uvm_object_new

  // This is the number of consecutive cycles with no outstanding accesses before
  // a random reset can fire.
  parameter int CyclesWithNoAccessesThreshold = 80;

  // knobs to disable post_start clear interrupt routine
  bit do_clear_all_interrupts = 1'b1;

  bit expect_fatal_alerts = 1'b0;

  // knob to enable/disable running csr_vseq with passthru_mem_tl_intg_err
  bit en_csr_vseq_w_passthru_mem_intg = 1;

  // knob to enable/disable running csr_vseq with tl_intg_err
  bit en_csr_vseq_w_tl_intg = 1;

  // csr queues
  dv_base_reg all_csrs[$];
  dv_base_reg intr_state_csrs[$];

  // user can set the name of common seq to run directly without using $value$plusargs
  string common_seq_type;

  // address mask struct
  typedef struct packed {
    bit [BUS_AW-1:0] addr;
    bit [BUS_DBW-1:0] mask;
  } addr_mask_t;

  addr_mask_t mem_exist_addr_q[string][$];

  // mem_ranges without base address
  addr_range_t updated_mem_ranges[string][$];

  // mask out bits out of the csr/mem range and LSB 2 bits
  bit [BUS_AW-1:0] csr_addr_mask[string];

  // This knob is used in run_seq_with_rand_reset_vseq to control how long we wait before injecting
  // a reset.
  rand uint rand_reset_delay;
  extern constraint rand_reset_delay_c;

  // control the chance to let tl adapter to abort CSR access if the valid isn't accept within given
  // a_valid_len
  rand uint csr_access_abort_pct;
  extern constraint csr_access_abort_pct_c;

  `uvm_object_param_utils_begin(cip_base_vseq#(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T))
    `uvm_field_string(common_seq_type, UVM_DEFAULT)
  `uvm_object_utils_end

  `include "cip_base_vseq__tl_errors.svh"
  `include "cip_base_vseq__shadow_reg_errors.svh"
  `include "cip_base_vseq__sec_cm_fi.svh"

  extern virtual task post_apply_reset(string reset_kind = "HARD");
  extern function void pre_randomize();
  extern task pre_start();
  extern task body();
  extern task post_start();

  // A specialization of dv_base_vseq::apply_reset, which also applies an EDN reset if num_edn is
  // positive.
  extern task apply_reset(string kind = "HARD");

  // Apply a reset on the EDN vif
  extern local task apply_edn_reset(string kind = "HARD");

  // A specialization of dv_base_vseq::apply_resets_concurrently, which holds the EDN in reset over
  // the time the base class does the reset, and ensures the reset lasts at least one EDN clock.
  extern task apply_resets_concurrently(int reset_duration_ps = 0);

  // Do a single BUS_DW-bit read or write transaction to the specified address.
  //
  //  addr                   The address to access
  //
  //  write                  True if this is a write (instead of a read)
  //
  //  data                   The data to be driven in a_data. This is the value to be written if
  //                         write is true.
  //
  //  tl_access_timeout_ns   The amount of time to give the TL transaction once it has been started
  //                         on the sequencer. If the driver takes longer than this, its process
  //                         will be killed.
  //
  //  mask                   The byte-enable mask used in the generated A channel transaction.
  //
  //  check_err_rsp          If this is true, the d_error signal in the response reported by the
  //                         driver are checked against exp_err_rsp (the next argument). On a
  //                         mismatch, an error is raised.
  //
  //  exp_err_rsp            Only used if check_err_rsp is true. If so, this is the expected value
  //                         of the d_error signal in the response.
  //
  //  check_exp_data         If this is true, the d_data signal in the response reported by the
  //                         driver are checked against exp_data, when masked with compare_mask. On
  //                         a mismatch, an error is raised.
  //
  //  exp_data               Only used if check_exp_data is true. If so, this is the expected value
  //                         of the d_data response for all bits that are set in compare_mask.
  //
  //  compare_mask           Only used if check_exp_data is true. A mask of the bits of the d_data
  //                         response that are compared with exp_data.
  //
  //  blocking               If this is true, the task doesn't complete until the access finishes.
  //                         If it is false, the access is run in a separate process and this task
  //                         completes immediately.
  //
  //  instr_type             The value given to the instr_type field of the a_user field sent on
  //                         the A channel.
  //
  //  tl_sequencer_h         The sequencer on which to run the sequence that generates the TL
  //                         access.
  //
  //  tl_intg_err_type       The value of tl_intg_err_type used for the generated cip_tl_seq_item.
  //                         These errors (in comand, data or both) are injected into the A channel
  //                         transaction that is sent from the agent.
  extern task tl_access(input bit [BUS_AW-1:0]  addr,
                        input bit               write,
                        inout bit [BUS_DW-1:0]  data,
                        input uint              tl_access_timeout_ns = cfg.tl_access_timeout_ns,
                        input bit [BUS_DBW-1:0] mask = '1,
                        input bit               check_err_rsp = 1'b1,
                        input bit               exp_err_rsp = 1'b0,
                        input bit               check_exp_data = 1'b0,
                        input bit [BUS_DW-1:0]  exp_data = 0,
                        input bit [BUS_DW-1:0]  compare_mask = '1,
                        input bit               blocking = csr_utils_pkg::default_csr_blocking,
                        input mubi4_t           instr_type = MuBi4False,
                        tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h,
                        input tl_intg_err_e     tl_intg_err_type = TlIntgErrNone);

  // An internal task for the body of tl_access(), which allows the caller to give a probability of
  // aborting the transaction and also reports its end status through two output arguments.
  //
  // The arguments are the same as for tl_access, with the following extra arguments:
  //
  //  completed        An output argument, used to pass back the rsp_completed signal from the
  //                   driver. This will be true if a D channel response was accepted (so the
  //                   transaction was not aborted and was not interrupted by a reset).
  //
  //  saw_err          An output argument, used to pass back the d_error signal from the device.
  //
  //  req_abort_pct    A percentage used to control the generated TL sequence. This is the
  //                   probability that the host driver will abort a transaction after a cycle where
  //                   it sends a_valid but the device isn't signaling a_ready.
  extern virtual protected task tl_access_w_abort(
                        input bit [BUS_AW-1:0]  addr,
                        input bit               write,
                        inout bit [BUS_DW-1:0]  data,
                        output bit              completed,
                        output bit              saw_err,
                        input uint              tl_access_timeout_ns = cfg.tl_access_timeout_ns,
                        input bit [BUS_DBW-1:0] mask = '1,
                        input bit               check_err_rsp = 1'b1,
                        input bit               exp_err_rsp = 1'b0,
                        input bit               check_exp_data = 1'b0,
                        input bit [BUS_DW-1:0]  exp_data = 0,
                        input bit [BUS_DW-1:0]  compare_mask = '1,
                        input bit               blocking = csr_utils_pkg::default_csr_blocking,
                        input                   mubi4_t instr_type = MuBi4False,
                        tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h,
                        input                   tl_intg_err_e tl_intg_err_type = TlIntgErrNone,
                        input int               req_abort_pct = 0);

  // A task that is the guts of tl_access_w_abort(). The arguments are as documented for that task,
  // plus one extra argument.
  //
  //  rsp              An output argument that contains the response item reported by the driver.
  extern protected task tl_access_sub(
                        input bit [BUS_AW-1:0]  addr,
                        input bit               write,
                        inout bit [BUS_DW-1:0]  data,
                        output bit              completed,
                        output bit              saw_err,
                        output                  cip_tl_seq_item rsp,
                        input uint              tl_access_timeout_ns = cfg.tl_access_timeout_ns,
                        input bit [BUS_DBW-1:0] mask = '1,
                        input bit               check_err_rsp = 1'b1,
                        input bit               exp_err_rsp = 1'b0,
                        input bit               check_exp_data = 1'b0,
                        input bit [BUS_DW-1:0]  exp_data = 0,
                        input bit [BUS_DW-1:0]  compare_mask = '1,
                        input int               req_abort_pct = 0,
                        input                   mubi4_t instr_type = MuBi4False,
                        tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h,
                        input                   tl_intg_err_e tl_intg_err_type = TlIntgErrNone);

  // Set up the all_csrs queue of CSRs across all register blocks, where each register has the more
  // specific type dv_base_reg. Also, set up the intr_state_csrs queue, with all the interrupt state
  // registers.
  extern local function void extract_common_csrs();

  // Enable or disable the interrupts for the bits that are true in the interrupts argument by
  // writing to the INTR_ENABLE register.
  //
  //  interrupts    A bit mask of interrupts (in the format of INTR_ENABLE) which specifies the
  //                interrupts that should be enabled/disabled by the function.
  //
  //  enable        If true, the selected interrupts will be enabled. If false, they will be
  //                disabled.
  extern protected task cfg_interrupts(bit [BUS_DW-1:0] interrupts, bit enable = 1'b1);

  // Check that the selected interrupts have the expected values, possibly clearing them afterwards.
  //
  //  interrupts    A bit mask of interrupts (in the format of INTR_ENABLE) which specifies the
  //                interrupts that should be checked by the function.
  //
  //  check_set     If this is false, the task checks that all of the interrupts are low. If it
  //                is true, the task checks that the interrupts are low exactly when they are
  //                enabled. In either case, this check is done by looking at intr_vif and also
  //                doing a front-door read of INTR_STATE.
  //
  //  clear         If true and any interrupts have been asserted then write to INTR_STATE to clear
  //                those interrupts.
  extern protected task check_interrupts(bit [BUS_DW-1:0]  interrupts,
                                         bit               check_set,
                                         bit [BUS_DW-1:0]  clear = '1);

  // Disable coverage sampling for things that aren't really tested by a CSR test
  extern local function void disable_coverage_sample_for_csr_test();

  // A wrapper task that runs some common sequence
  //
  //  num_times    Passed to the task that is run, controlling how many times to do the basic check.
  extern protected virtual task run_common_vseq_wrapper(int num_times = 1);

  // A basic check that tries to control and monitor interrupts through CSRs.
  //
  // This writes a random value to each writeable interrupt CSR (INTR_TEST, INTR_ENABLE, INTR_STATE)
  // for each interrupt, then reads the registers back again, checking the values match what is
  // expected and also checking that the interrupt pins themselves match the INTR_STATE values.
  //
  // Finally, it clears all the INTR_TEST registers.
  extern local task run_intr_test_vseq(int num_times = 1);

  // Access an INTR_STATUS register, trying to clear any asserted event-type interrupt.
  //
  // The task first reads the current INTR_STATUS, using ro_mask to extract just the event-type
  // interrupts. If any of those interrupts are asserted, it next writes 1 to those bits (clearing
  // the latched event) and finally reads INTR_STATUS again, asserting that those interrupts are now
  // clear.
  //
  //   register    The dv_base_reg for the INTR_STATUS register.
  //
  //   ro_mask     A mask of interrupts. Status-type interrupts (which can't be cleared by writing
  //               to INTR_STATUS) are read-only and their bits are ignored by this task.
  extern local task clear_interrupt_reg(dv_base_reg register, bit [BUS_DW-1:0] ro_mask);

  // Loop over all the interrupts, writing to INTR_STATE registers to clear those interrupts
  // that can by cleared.
  extern protected task clear_all_interrupts();

  // Watch the interface for the alert called alert_name and check that either it doesn't fire or
  // that it is currently firing, but gets cleared and doesn't re-assert itself.
  //
  // This task is safe to kill (on reset).
  //
  //  alert_name    The name of the alert to test
  //
  //  alert_cfg     A config object for the alert agent
  extern local task check_not_fatal_alert(string alert_name, alert_esc_agent_cfg alert_cfg);

  // Watch the interface for each alert and check that none fire as a fatal alert (using the
  // check_not_fatal_alert() task)
  //
  // If a reset is asserted, this task completes immediately.
  extern protected virtual task check_no_fatal_alerts();

  // Use the ALERT_TEST register to check that each alert can be triggered.
  extern local task run_alert_test_vseq(int num_times = 1);

  // Blocks if there's a ping in-flight
  extern local task wait_until_ping_is_finished(alert_esc_agent_cfg alert_agent_cfg);

  // Wait for the named alert to be triggered
  //
  //  alert_name      The name of the alert to wait for.
  //
  //  max_wait_cycle  After any pending ping operation has completed, this gives the number of
  //                  cycles to wait until the alert. By default it is 7, which gives one extra
  //                  cycle longer than the gap we expect between continuously triggered alerts.
  //                  That gap is 6 cycles: 2-3 cycles for a CDC, 2 for pauses and 1 for the idle
  //                  state.
  //
  //  wait_complete   If this is true, the task waits for the alert to be acked before exiting.
  extern protected task wait_alert_trigger(string alert_name,
                                           int    max_wait_cycle = 7,
                                           bit    wait_complete = 0);

  // Run a sequence on the alert sequencer for the named alert to act as a prim_alert_receiver and
  // respond to the alert.
  extern local task drive_alert_rsp_and_check_handshake(string alert_name, int alert_index);

  // A specialization of dv_base_vseq::run_csr_vseq, which might configure the sequence to abort
  // some transactions and, if so, disables the self-checking feature of the sequences.
  // override csr_vseq to control adapter to abort transaction
  extern task run_csr_vseq(string            csr_test_type,
                           int               num_test_csrs = 0,
                           bit               do_rand_wr_and_reset = 1,
                           dv_base_reg_block models[$] = {},
                           string            ral_name = "");

  // Run a stress sequence (chosen by plusarg) in parallel with a TL errors vseq and then suddenly
  // inject a reset.
  //
  //  num_times    The number of times to run that sequence, possibly injecting a reset each time.
  extern local task run_plusarg_vseq_with_rand_reset(int num_times);

  // A virtual task which is run at the end of each iteration of the loop in
  // run_seq_with_rand_reset_vseq(). Subclasses can implement this if they are testing a block that
  // needs input ports and status or interrupt registers cleaned up.
  extern protected virtual task rand_reset_eor_clean_up();

  // Run the given sequence together with a TL errors vseq. Suddenly inject a reset after at most
  // reset_delay_bound cycles. When we come out of reset, check all CSR values to ensure they are
  // the documented reset values.
  //
  //   seq                The sequence to run
  //
  //   num_times          The number of times to run the sequence (and inject a reset)
  //
  //   reset_delay_bound  Each time the sequence runs, this task will wait a random amount of time
  //                      before it starts waiting for an opportune time to inject the reset. This
  //                      is the upper bound on that wait.
  extern protected task run_seq_with_rand_reset_vseq(uvm_sequence seq,
                                                     int          num_times,
                                                     uint         reset_delay_bound);

  // If cfg.can_reset_with_csr_accesses is false, wait_to_issue_reset() will try to wait for a time
  // with no CSR accesses before it injects the reset. The value returned by this function is an
  // upper bound on how long to wait.
  extern virtual function int wait_cycles_with_no_outstanding_accesses();

  // Helper function for the stress_all_with_rand_reset() task that waits for random time before
  // issuing a reset. This function can be extended to wait for certain special timing to issue
  // reset.
  //
  // The number of cycles to wait for a run of enough consecutive cycles with no outstanding
  // accesses can also be set by derived classes for special cases. If the wait doesn't clear
  // something is probably wrong: perhaps some loop sending CSR transactions is not breaking even
  // after stop_transaction_generators() returns true.
  //
  //   reset_delay_bound  This will wait a random amount of time before it starts waiting for an
  //                      opportune time to inject the reset. This is the upper bound on that wait.
  extern virtual protected task wait_to_issue_reset(uint reset_delay_bound);

  // Run the hw_reset CSR test sequence (csr_hw_reset_seq) through run_csr_vseq(). It reads each CSR
  // and checks that each has the value expected in the ral. This task is run just after a reset, so
  // the ral will expect all registers to have their specified reset values.
  extern virtual protected task read_and_check_all_csrs_after_reset();

  // Run through all the CSRs. For each CSR, send a sequence of reads and writes, updating
  // predictions as we go. To allow multiple operations to be outstanding, this sequence runs the
  // reads and writes with the blocking argument set to zero. Since the arbitration in the
  // tl_sequencer instances is UVM_SEQ_ARB_FIFO, the operations run in issue order and their
  // behaviour can be predicted in this task.
  extern local task run_same_csr_outstanding_vseq(int num_times);

  // Check that a fatal alert that has been requested comes out. This waits for alert_p & ~alert_n
  // when there isn't a ping in progress and has a timeout based on the fatal alert repeat time. The
  // alert signal isn't asserted within the time limit, an error gets raised.
  //
  // This uses join_none to spawn a background task and check_fatal_alert_nonblocking() will always
  // return without consuming time.
  extern protected task check_fatal_alert_nonblocking(string alert_name);

  // Run the partial access test described in run_mem_partial_access_vseq_sub() for each RAL model,
  // with all the bus interfaces running concurrently.
  extern local task run_mem_partial_access_vseq(int num_times);

  // Run a partial access test on any memory accessible through the interface called ral_name.
  //
  // This writes random values to some addresses and, interleaved with these writes, performs reads
  // from addresses that have been written. Note that this task doesn't contain any checking of the
  // results, which should hopefully be provided by a scoreboard.
  //
  //  num_times   A scaling constant for the number of accesses to perform. The total number of
  //              accesses is also scaled by the size of the memory.
  //
  //  ral_name    The key of the RAL model associated with the interface.
  extern local task run_mem_partial_access_vseq_sub(int num_times, string ral_name);

  // Perform CSR accesses (with csr_rw_seq) and memory accesses (with run_mem_partial_access_vseq)
  // across each RAL model's interface.
  extern local task run_csr_mem_rw_vseq(int num_times);

  // Run CSR and memory accesses (with run_csr_mem_rw_vseq) for a short time and then inject a reset
  // at a random time.
  //
  //  num_times   The number of times to run the sequence (and interrupt it with a reset).
  extern local task run_csr_mem_rw_with_rand_reset_vseq(int num_times);

  // Return a randomised byte-enable mask, of width BUS_DBW. This must be contiguous (so masks like
  // 4'b1001 are not allowed). The mask is also constrained to be false on byte lanes that aren't
  // known to be valid (as conveyed by valid_mask).
  extern protected function bit[BUS_DBW-1:0]
    get_rand_contiguous_mask(bit [BUS_DBW-1:0] valid_mask = '1);

  // Set the tlul_assert_en configuration flag in uvm_config_db. This is consumed by the code in
  // tlul_assert.sv and can enable/disable the assertions in that file
  extern virtual protected function void set_tl_assert_en(bit enable, string path = "*");
endclass

constraint cip_base_vseq::rand_reset_delay_c {
  rand_reset_delay dist {
    [1 : 1000]              :/ 1,
    [1001 : 100_000]        :/ 2,
    [100_001 : 1_000_000]   :/ 6,
    [1_000_001 : 5_000_000] :/ 1
  };
}

constraint cip_base_vseq::csr_access_abort_pct_c {
  csr_access_abort_pct dist {
    0        :/ 50,
    [1 : 99] :/ 40,
    100      :/ 10
  };
}

task cip_base_vseq::post_apply_reset(string reset_kind = "HARD");
  super.post_apply_reset(reset_kind);

  // Wait for alert init done, then start the sequence.
  foreach (cfg.list_of_alerts[i]) begin
    if (cfg.m_alert_agent_cfgs[cfg.list_of_alerts[i]].is_active) begin
      `DV_WAIT(cfg.m_alert_agent_cfgs[cfg.list_of_alerts[i]].alert_init_done == 1)
    end
  end
endtask

function void cip_base_vseq::pre_randomize();
  super.pre_randomize();
  // Disable csr_access_abort because shadow_reg sequence requires all shadow registers'
  // read/write to be executed into design without aborting.
  if (common_seq_type inside {"shadow_reg_errors", "shadow_reg_errors_with_csr_rw"}) begin
    csr_access_abort_pct.rand_mode(0);
  end
endfunction

task cip_base_vseq::pre_start();
  if (common_seq_type == "") void'($value$plusargs("run_%0s", common_seq_type));
  csr_utils_pkg::max_outstanding_accesses = 1 << BUS_AIW;
  super.pre_start();
  extract_common_csrs();
endtask

task cip_base_vseq::body();
  `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
endtask : body

task cip_base_vseq::post_start();
  super.post_start();

  if (expect_fatal_alerts) begin
    // Fatal alert is triggered in this seq. Wait 10_000ns so the background check
    // `check_fatal_alert_nonblocking` has enough time to execute before we call dut_init. If
    // there is a reset in the meantime, stop waiting.
    `DV_SPINWAIT_EXIT(#10_000ns;,
                      wait(!cfg.clk_rst_vif.rst_n);)

    // If we are not in reset, ask the dut to re-initialise itself. This will issue a reset if the
    // sequence has do_apply_reset=1. If not, the reset will be applied in an upper vseq.
    if (cfg.clk_rst_vif.rst_n) dut_init();
  end else begin
    if (cfg.clk_rst_vif.rst_n) check_no_fatal_alerts();
  end

  // Some fatal alerts might trigger interrupt as well, so only check interrupt after fatal alert
  // is cleared.
  void'($value$plusargs("do_clear_all_interrupts=%0b", do_clear_all_interrupts));
  if (do_clear_all_interrupts) clear_all_interrupts();
endtask

task cip_base_vseq::apply_reset(string kind = "HARD");
  if (kind == "HARD") begin
    fork
      if (cfg.num_edn) apply_edn_reset(kind);
      super.apply_reset(kind);
    join
  end
endtask

task cip_base_vseq::apply_edn_reset(string kind = "HARD");
  if (cfg.num_edn && kind == "HARD") cfg.edn_clk_rst_vif.apply_reset();
endtask

task cip_base_vseq::apply_resets_concurrently(int reset_duration_ps = 0);
  if (cfg.num_edn) begin
    cfg.edn_clk_rst_vif.drive_rst_pin(0);
    reset_duration_ps = max2(reset_duration_ps, cfg.edn_clk_rst_vif.clk_period_ps);
  end
  super.apply_resets_concurrently(reset_duration_ps);
  if (cfg.num_edn) cfg.edn_clk_rst_vif.drive_rst_pin(1);
endtask

task cip_base_vseq::tl_access(
    input bit [BUS_AW-1:0]  addr,
    input bit               write,
    inout bit [BUS_DW-1:0]  data,
    input uint              tl_access_timeout_ns = cfg.tl_access_timeout_ns,
    input bit [BUS_DBW-1:0] mask = '1,
    input bit               check_err_rsp = 1'b1,
    input bit               exp_err_rsp = 1'b0,
    input bit               check_exp_data = 1'b0,
    input bit [BUS_DW-1:0]  exp_data = 0,
    input bit [BUS_DW-1:0]  compare_mask = '1,
    input bit               blocking = csr_utils_pkg::default_csr_blocking,
    input mubi4_t           instr_type = MuBi4False,
    tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h,
    input tl_intg_err_e     tl_intg_err_type = TlIntgErrNone);

  bit completed, saw_err;
  tl_access_w_abort(addr, write, data, completed, saw_err, tl_access_timeout_ns, mask,
                    check_err_rsp, exp_err_rsp, check_exp_data, exp_data, compare_mask, blocking,
                    instr_type, tl_sequencer_h, tl_intg_err_type);
endtask

task cip_base_vseq::tl_access_w_abort(
    input bit [BUS_AW-1:0]  addr,
    input bit               write,
    inout bit [BUS_DW-1:0]  data,
    output bit              completed,
    output bit              saw_err,
    input uint              tl_access_timeout_ns = cfg.tl_access_timeout_ns,
    input bit [BUS_DBW-1:0] mask = '1,
    input bit               check_err_rsp = 1'b1,
    input bit               exp_err_rsp = 1'b0,
    input bit               check_exp_data = 1'b0,
    input bit [BUS_DW-1:0]  exp_data = 0,
    input bit [BUS_DW-1:0]  compare_mask = '1,
    input bit               blocking = csr_utils_pkg::default_csr_blocking,
    input                   mubi4_t instr_type = MuBi4False,
    tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h,
    input                   tl_intg_err_e tl_intg_err_type = TlIntgErrNone,
    input int               req_abort_pct = 0);

  cip_tl_seq_item rsp;

  if (blocking) begin
    tl_access_sub(addr, write, data, completed, saw_err, rsp, tl_access_timeout_ns, mask,
                  check_err_rsp, exp_err_rsp, check_exp_data, exp_data, compare_mask, req_abort_pct,
                  instr_type, tl_sequencer_h, tl_intg_err_type);
  end else begin
    fork
      tl_access_sub(addr, write, data, completed, saw_err, rsp, tl_access_timeout_ns, mask,
                    check_err_rsp, exp_err_rsp, check_exp_data, exp_data, compare_mask,
                    req_abort_pct, instr_type, tl_sequencer_h, tl_intg_err_type);
    join_none
    // Add #0 to ensure that this thread starts executing before any subsequent call
    #0;
  end
endtask

task cip_base_vseq::tl_access_sub(
    input bit [BUS_AW-1:0]  addr,
    input bit               write,
    inout bit [BUS_DW-1:0]  data,
    output bit              completed,
    output bit              saw_err,
    output                  cip_tl_seq_item rsp,
    input                   uint tl_access_timeout_ns = cfg.tl_access_timeout_ns,
    input bit [BUS_DBW-1:0] mask = '1,
    input bit               check_err_rsp = 1'b1,
    input bit               exp_err_rsp = 1'b0,
    input bit               check_exp_data = 1'b0,
    input bit [BUS_DW-1:0]  exp_data = 0,
    input bit [BUS_DW-1:0]  compare_mask = '1,
    input int               req_abort_pct = 0,
    input                   mubi4_t instr_type = MuBi4False,
    tl_sequencer            tl_sequencer_h = p_sequencer.tl_sequencer_h,
    input                   tl_intg_err_e tl_intg_err_type = TlIntgErrNone);

  cip_tl_host_single_seq tl_seq;
  `uvm_create_on(tl_seq, tl_sequencer_h)
  tl_seq.tl_intg_err_type = tl_intg_err_type;
  if (cfg.zero_delays) begin
    tl_seq.min_req_delay = 0;
    tl_seq.max_req_delay = 0;
  end
  tl_seq.req_abort_pct = req_abort_pct;
  `DV_CHECK_RANDOMIZE_WITH_FATAL(tl_seq,
      addr        == local::addr;
      write       == local::write;
      mask        == local::mask;
      data        == local::data;
      instr_type  == local::instr_type;)

  csr_utils_pkg::increment_outstanding_access();
  fork begin : isolation_fork
    fork
      `uvm_send_pri(tl_seq, 100)
      begin
        // Wait until the sequence actually gets allocated to the sequencer. If a vast number of
        // TL operations have been enqueued in parallel, this might take a while. Since we're
        // using tl_host_single_seq, we expect to send exactly one item and the sequence's
        // reqs_started counter will become 1 when that item starts on the relevant bus.
        wait(tl_seq.reqs_started);

        // Now wait a bounded time to check that the bus hasn't locked up for some reason.
        #(tl_access_timeout_ns * 1ns);
      end
    join_any
    disable fork;
  end join
  csr_utils_pkg::decrement_outstanding_access();

  rsp = tl_seq.rsp;

  if (!write) begin
    data = rsp.d_data;
    if (check_exp_data && !cfg.under_reset) begin
      bit [BUS_DW-1:0] masked_data = data & compare_mask;
      exp_data &= compare_mask;
      `DV_CHECK_EQ(masked_data, exp_data, $sformatf("addr 0x%0h read out mismatch", addr))
    end
  end
  if (check_err_rsp && !cfg.under_reset && tl_intg_err_type == TlIntgErrNone) begin
    `DV_CHECK_EQ(rsp.d_error, exp_err_rsp,
                 $sformatf("unexpected error response for addr: 0x%x", rsp.a_addr))
  end

  // Expose whether the transaction ran and whether it generated an error. Note that we
  // probably only want to do a RAL update if it ran and caused no error.
  completed = rsp.rsp_completed;
  saw_err = rsp.d_error;
endtask

function void cip_base_vseq::extract_common_csrs();
  foreach (cfg.ral_models[i]) begin
    dv_base_reg regs[$];
    cfg.ral_models[i].get_dv_base_regs(regs);
    foreach (regs[i]) all_csrs.push_back(regs[i]);
  end
  foreach (all_csrs[i]) begin
    string csr_name = all_csrs[i].get_name();
    if (!uvm_re_match("intr_state*", csr_name)) begin
      intr_state_csrs.push_back(all_csrs[i]);
    end
  end
endfunction

task cip_base_vseq::cfg_interrupts(bit [BUS_DW-1:0] interrupts, bit enable = 1'b1);
  uvm_reg          csr;
  bit [BUS_DW-1:0] data;

  csr = ral.get_dv_base_reg_by_name("intr_enable");
  data = csr.get_mirrored_value();
  if (enable) data |= interrupts;
  else        data &= ~interrupts;
  csr.set(data);
  csr_update(.csr(csr));
endtask

task cip_base_vseq::check_interrupts(bit [BUS_DW-1:0]  interrupts,
                                     bit               check_set,
                                     bit [BUS_DW-1:0]  clear = '1);
  uvm_reg          csr_intr_state, csr_intr_enable;
  bit [BUS_DW-1:0] act_pins;
  bit [BUS_DW-1:0] exp_pins;
  bit [BUS_DW-1:0] exp_intr_state;

  if (cfg.under_reset) return;

  act_pins = cfg.intr_vif.sample() & interrupts;
  if (check_set) begin
    csr_intr_enable = ral.get_dv_base_reg_by_name("intr_enable");
    exp_pins = interrupts & csr_intr_enable.get_mirrored_value();
    exp_intr_state = interrupts;
  end else begin
    exp_pins = '0;
    exp_intr_state = ~interrupts;
  end
  `DV_CHECK_EQ(act_pins, exp_pins)
  csr_intr_state = ral.get_dv_base_reg_by_name("intr_state");
  csr_rd_check(.ptr(csr_intr_state), .compare_value(exp_intr_state), .compare_mask(interrupts));

  if (check_set && |(interrupts & clear)) begin
    csr_wr(.ptr(csr_intr_state), .value(interrupts & clear));
  end
endtask

function void cip_base_vseq::disable_coverage_sample_for_csr_test();
  `uvm_info(`gfn, "mubi reg coverage sampling is disabled as this is a CSR test", UVM_HIGH)
  foreach (all_csrs[i]) begin
    dv_base_reg_field fields[$];

    all_csrs[i].get_dv_base_reg_fields(fields);
    // assign null to all mubi_cov object, so that coverage sampling is skipped
    foreach (fields[j]) fields[j].mubi_cov = null;
  end
endfunction

task cip_base_vseq::run_common_vseq_wrapper(int num_times = 1);
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

task cip_base_vseq::run_intr_test_vseq(int num_times = 1);
  import dv_utils_pkg::interrupt_t;
  dv_base_reg intr_csrs[$];
  dv_base_reg intr_test_csrs[$];

  foreach (all_csrs[i]) begin
    string csr_name = all_csrs[i].get_name();
    if (!uvm_re_match("intr_test*", csr_name) ||
        !uvm_re_match("intr_enable*", csr_name) ||
        !uvm_re_match("intr_state*", csr_name)) begin
      intr_csrs.push_back(ral.get_dv_base_reg_by_name(csr_name));
    end
    if (!uvm_re_match("intr_test*", csr_name)) begin
      intr_test_csrs.push_back(ral.get_dv_base_reg_by_name(csr_name));
    end
  end

  // Checking the intr_test register works only makes sense if there is at least one interrupt
  // register. We shouldn't call this sequence for blocks that don't have one, so let's fail
  // understandably if we have done so by accident.
  `DV_CHECK(intr_csrs.size() > 0, "Called intr_test vseq without any interrupt register.")

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
      if (cfg.under_reset) break;
    end

    // Read all intr related csr and check interrupt pins
    intr_csrs.shuffle();
    foreach (intr_csrs[i]) begin
      uvm_reg_data_t exp_val = `gmv(intr_csrs[i]);
      uvm_reg_data_t act_val;

      interrupt_t irq_ro_mask = '0;

      // Status type interrupts have RO fields in intr_state, so mask those bits off here as they
      // can't be generically predicted for all IPs.
      if (!uvm_re_match("intr_state*", intr_csrs[i].get_name())) begin
        irq_ro_mask = intr_csrs[i].get_ro_mask();
      end

      exp_val &= ~irq_ro_mask;

      csr_rd(.ptr(intr_csrs[i]), .value(act_val));
      act_val &= ~irq_ro_mask;

      if (cfg.under_reset) break;
      `uvm_info(`gfn, $sformatf("Read %s: 0x%0h", intr_csrs[i].get_full_name(), act_val),
                UVM_MEDIUM)
      if (intr_csrs[i].get_predicted_mask() == 0) begin
        `DV_CHECK_EQ(exp_val, act_val, {"when reading the intr CSR ",
                                        intr_csrs[i].get_full_name()})

        // if it's intr_state, also check the interrupt pin value
        if (!uvm_re_match("intr_state*", intr_csrs[i].get_name())) begin
          interrupt_t exp_intr_pin = intr_csrs[i].get_intr_pins_exp_value();
          interrupt_t act_intr_pin = cfg.intr_vif.sample();
          act_intr_pin &= interrupt_t'((1 << cfg.num_interrupts) - 1);
          `DV_CHECK_CASE_EQ(exp_intr_pin, act_intr_pin)
        end // if (!uvm_re_match
      end
    end // foreach (intr_csrs[i])
  end
  // Write 0 to intr_test to clean up status interrupts, otherwise, status interrupts may remain
  // active. And writing any value to a status interrupt CSR (intr_state) can't clear its value.
  foreach (intr_test_csrs[i]) begin
    csr_wr(.ptr(intr_test_csrs[i]), .value(0));
  end
endtask

task cip_base_vseq::clear_interrupt_reg(dv_base_reg register, bit [BUS_DW-1:0] ro_mask);
  bit [BUS_DW-1:0] data;
  // Status type interrupts are read-only and cannot be cleared by writing 1 to them.
  // Instead, the underlying condition needs to be resolved (e.g. drain a FIFO that is full).
  // Therefore, we use the RO bitmask to mask the writes / reads below.
  csr_rd(.ptr(register), .value(data));
  if ((data & ~ro_mask) != 0) begin
    `uvm_info(`gtn, $sformatf("Clearing status bits in %0s", register.get_name()),
              UVM_HIGH)
    csr_wr(.ptr(register), .value(data & ~ro_mask));
    csr_rd(.ptr(register), .value(data));
    if (!cfg.under_reset) `DV_CHECK_EQ(data & ~ro_mask, 0)
  end
endtask

// Task to clear register intr status bits
task cip_base_vseq::clear_all_interrupts();
  import dv_utils_pkg::interrupt_t;
  interrupt_t irq_ro_mask = '0;
  if (cfg.num_interrupts == 0) return;

  // Iterate over all interrupt registers (typically there is only one).
  foreach (intr_state_csrs[i]) begin
    irq_ro_mask[i*BUS_DW +: BUS_DW] = BUS_DW'(intr_state_csrs[i].get_ro_mask());
    clear_interrupt_reg(intr_state_csrs[i], irq_ro_mask[i*BUS_DW +: BUS_DW]);
    if (cfg.under_reset) break;
  end

  if (!cfg.under_reset) begin
    // Status type interrupts may remain asserted, hence we have to mask them away.
    interrupt_t all_interrupts = interrupt_t'((1 << cfg.num_interrupts) - 1);
    interrupt_t clearable_mask = all_interrupts & ~irq_ro_mask;
    `DV_CHECK_EQ(cfg.intr_vif.sample() & clearable_mask, '0)
  end
endtask

task cip_base_vseq::check_not_fatal_alert(string alert_name, alert_esc_agent_cfg alert_cfg);
  // The maximum number of cycles that an alert handshake should take.
  // - 20 cycles includes ack response and ack stable time.
  // - 10 is the max difference between alert clock and dut clock.
  int max_alert_handshake_cycles = 20 * 10;

  // The amount of time to watch to check a new alert doesn't appear. This is chosen to be at
  // least the length of a single handshake.
  int check_cycles = $urandom_range(max_alert_handshake_cycles, max_alert_handshake_cycles * 3);

  // Take a snapshot of the number of pings that has been seen for the alert in question. If we
  // see a ping while we're waiting, we want to stop immediately since we won't be able to
  // decipher the resulting alert.
  int unsigned ping_count = alert_cfg.ping_count;

  // The alert may have been triggered already. Assuming it is not fatal, wait long enough
  // for any such alert to be acknowledged and cleared. This would normally be a known
  // number of cycles, but asynchronous alerts make it a bit trickier. Look at the interface
  // itself and wait for any ack to complete.
  cfg.clk_rst_vif.wait_clks(max_alert_handshake_cycles);
  `DV_SPINWAIT(alert_cfg.vif.wait_ack_complete();)

  // Now wait for a while to make sure that the alert is not triggered.
  fork begin : isolation_fork
    fork
      begin
        cfg.clk_rst_vif.wait_clks(check_cycles);
      end
      wait(alert_cfg.vif.alert_tx_final.alert_p && !alert_cfg.vif.alert_tx_final.alert_n);
    join_any
    disable fork;
  end join

  // If there's alert visible through alert_tx_final, we must have stopped early. This must mean
  // that an unexpected alert was generated.
  if (alert_cfg.vif.alert_tx_final.alert_p && !alert_cfg.vif.alert_tx_final.alert_n) begin
    // If ping_count has changed, the alert was probably due to the ping and we should
    // ignore it (but print a debug message). If ping_count is unchanged, the alert fired
    // when we didn't expect it to.
    if (alert_cfg.ping_count == ping_count)
      `uvm_error("Alert %0s fired unexpectedly.", alert_name)
    else
      `uvm_info(`gfn,
                $sformatf("Unexpected alert %0s, but this may have a ping response.",
                          alert_name),
                UVM_DEBUG)
  end
endtask

task cip_base_vseq::check_no_fatal_alerts();
  fork begin : isolation_fork
    fork
      wait(cfg.under_reset);

      fork begin : isolation_fork
        foreach(cfg.m_alert_agent_cfgs[alert_name]) begin
          fork
            check_not_fatal_alert(alert_name, cfg.m_alert_agent_cfgs[alert_name]);
          join_none
        end
        wait fork;
      end join
    join_any
    disable fork;
  end join
endtask

task cip_base_vseq::run_alert_test_vseq(int num_times = 1);
  int num_alerts = cfg.list_of_alerts.size();
  dv_base_reg alert_test_csr = ral.get_dv_base_reg_by_name("alert_test");
  `DV_CHECK_FATAL(num_alerts > 0, "Please declare `list_of_alerts` under cfg!")

  for (int trans = 1; trans <= num_times; trans++) begin
    `uvm_info(`gfn, $sformatf("Running alert test iteration %0d/%0d", trans, num_times), UVM_LOW)

    repeat ($urandom_range(num_alerts, num_alerts * 10)) begin
      bit [BUS_DW-1:0] alert_req = $urandom_range(0, (1'b1 << num_alerts) - 1);
      // Write random value to alert_test register.
      csr_wr(.ptr(alert_test_csr), .value(alert_req));
      `uvm_info(`gfn, $sformatf("Write alert_test with val %0h", alert_req), UVM_HIGH)
      for (int i = 0; i < num_alerts; i++) begin
        string alert_name = cfg.list_of_alerts[i];

        // If the field has already been written, check if the corresponding alert fires
        // correctly and check if writing to this alert_test field again won't corrupt the
        // current alert mechanism.
        if (alert_req[i]) begin
          // if previous alert_handler just finish, there is a max of two clock_cycle
          // pause in between
          wait_alert_trigger(alert_name, .max_wait_cycle(4));

          // write alert_test during alert handshake will be ignored
          if ($urandom_range(1, 10) == 10) begin
            csr_wr(.ptr(alert_test_csr), .value(1'b1 << i));
            `uvm_info(`gfn, "Write alert_test again during alert handshake", UVM_HIGH)
          end

          // drive alert response sequence
          drive_alert_rsp_and_check_handshake(alert_name, i);

       // If the field has not been written, check if the corresponding alert does not fire.
       // Randomly decide to write this field and check if the alert fires.
       end else begin
         cfg.clk_rst_vif.wait_clks($urandom_range(0, 3));
         `DV_CHECK_EQ(cfg.m_alert_agent_cfgs[alert_name].vif.get_alert(), 0,
                      $sformatf("alert_test did not set alert:%0s", alert_name))

          // write alert_test field when there is ongoing alert handshake
          if ($urandom_range(1, 10) == 10) begin
            `uvm_info(`gfn,
                      $sformatf("Write alert_test with val %0h during alert_handshake",
                      1'b1 << i), UVM_HIGH)
            csr_wr(.ptr(alert_test_csr), .value(1'b1 << i));
            `DV_SPINWAIT_EXIT(while (!cfg.m_alert_agent_cfgs[alert_name].vif.get_alert())
                              cfg.clk_rst_vif.wait_clks(1);,
                              cfg.clk_rst_vif.wait_clks(2);,
                              $sformatf("expect alert_%0d:%0s to fire",
                                        i, alert_name))
            drive_alert_rsp_and_check_handshake(alert_name, i);
          end
        end
      end // end for loop

      // check no alert triggers continuously
      foreach (cfg.list_of_alerts[i]) begin
        `DV_CHECK_EQ(cfg.m_alert_agent_cfgs[cfg.list_of_alerts[i]].vif.get_alert(), 0,
                     $sformatf("expect alert:%0s to stay low", cfg.list_of_alerts[i]))
      end
    end // end repeat
  end
endtask

task cip_base_vseq::wait_until_ping_is_finished(alert_esc_agent_cfg alert_agent_cfg);

  if (alert_agent_cfg.vif.in_ping_st()) begin
    // There's a 2-cycle sampling delay in the monitor, so if the VIF has already seen the ping then
    // wait for it. Otherwise there may be scenarios where the `active_ping` is not yet set
    // in the monitor due to the 2-cycle delay. Which causes issues predicting the value in
    // `fatal_alert_cause`
    wait (alert_agent_cfg.active_ping == 1);
  end
  wait (alert_agent_cfg.active_ping == 0);
endtask

task cip_base_vseq::wait_alert_trigger(string alert_name,
                                       int    max_wait_cycle = 7,
                                       bit    wait_complete = 0);
  // wait until ping finishes before the dv_spinwait in case
  // m_alert_agent_cfgs[alert_name].vif.is_alert_handshaking() is true due to a ping
  wait_until_ping_is_finished(cfg.m_alert_agent_cfgs[alert_name]);
  `DV_SPINWAIT_EXIT(while (!cfg.m_alert_agent_cfgs[alert_name].vif.is_alert_handshaking()) begin
                      cfg.clk_rst_vif.wait_clks(1);
                      wait_until_ping_is_finished(cfg.m_alert_agent_cfgs[alert_name]);
                    end,
                    // another thread to wait for given cycles. If timeout, report an error.
                    cfg.clk_rst_vif.wait_clks(max_wait_cycle);
                    `uvm_error(`gfn, $sformatf("expect alert:%0s to fire", alert_name)))
  if (wait_complete) begin
    `DV_SPINWAIT(cfg.m_alert_agent_cfgs[alert_name].vif.wait_ack_complete();,
                 $sformatf("timeout wait for alert handshake:%0s", alert_name))
  end
endtask

task cip_base_vseq::drive_alert_rsp_and_check_handshake(string alert_name, int alert_index);
  alert_receiver_alert_rsp_seq ack_seq =
      alert_receiver_alert_rsp_seq::type_id::create("ack_seq");
  `DV_CHECK_RANDOMIZE_FATAL(ack_seq);
  ack_seq.start(p_sequencer.alert_esc_sequencer_h[alert_name]);

  `DV_SPINWAIT(cfg.m_alert_agent_cfgs[alert_name].vif.wait_ack_complete();,
               $sformatf("timeout wait for alert_%0d handshake:%0s", alert_index, alert_name))

  if (cfg.m_alert_agent_cfgs[alert_name].is_async) cfg.clk_rst_vif.wait_clks(2);
endtask

task cip_base_vseq::run_csr_vseq(string            csr_test_type,
                                 int               num_test_csrs = 0,
                                 bit               do_rand_wr_and_reset = 1,
                                 dv_base_reg_block models[$] = {},
                                 string            ral_name = "");
  bit has_shadow_reg;
  dv_base_reg regs[$];

  // if there is any shadow reg, we shouldn't abort TL access, otherwise, it may do only one
  // write to the shadow reg, which may cause an unexpected recoverable error.
  foreach (cfg.ral_models[i]) cfg.ral_models[i].get_dv_base_regs(regs);
  foreach (regs[i]) begin
    if (regs[i].get_is_shadowed()) begin
      has_shadow_reg = 1;
      break;
    end
  end
  if (!has_shadow_reg && csr_access_abort_pct.rand_mode()) begin
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


task cip_base_vseq::run_plusarg_vseq_with_rand_reset(int num_times);
  string stress_seq_name;
  int had_stress_seq_plusarg = $value$plusargs("stress_seq=%0s", stress_seq_name);
  `DV_CHECK_FATAL(had_stress_seq_plusarg)

  run_seq_with_rand_reset_vseq(.seq(create_seq_by_name(stress_seq_name)),
                               .num_times(num_times),
                               .reset_delay_bound(100_000));
endtask

task cip_base_vseq::rand_reset_eor_clean_up(); endtask

task cip_base_vseq::run_seq_with_rand_reset_vseq(uvm_sequence seq,
                                                 int          num_times,
                                                 uint         reset_delay_bound);
  `DV_CHECK_FATAL(seq != null)
  `uvm_info(`gfn, $sformatf("running run_seq_with_rand_reset_vseq for sequence %s",
                             seq.get_full_name()), UVM_MEDIUM)

  for (int i = 1; i <= num_times; i++) begin
    bit ongoing_reset;
    bit do_read_and_check_all_csrs;
    bit vseq_done = 1'b0;

    `uvm_info(`gfn, $sformatf("running run_seq_with_rand_reset_vseq iteration %0d/%0d",
                              i, num_times), UVM_LOW)
    // Arbitration: requests at highest priority granted in FIFO order, so that we can predict
    // results for many non-blocking accesses
    p_sequencer.tl_sequencer_h.set_arbitration(UVM_SEQ_ARB_STRICT_FIFO);
    fork
      begin: isolation_fork
        fork : run_test_seqs
          begin : seq_wo_reset
            fork
              begin : tl_err_seq
                run_tl_errors_vseq(.num_times($urandom_range(10, 1000)), .do_wait_clk(1'b1));
              end
              begin : run_stress_seq
                dv_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T) dv_vseq;
                `downcast(dv_vseq, seq.clone())

                dv_vseq.do_apply_reset = 0;
                dv_vseq.set_sequencer(p_sequencer);
                `DV_CHECK_RANDOMIZE_FATAL(dv_vseq)
                `uvm_info(`gfn, $sformatf("Starting sequence %s", dv_vseq.get_full_name()),
                          UVM_MEDIUM)
                dv_vseq.start(p_sequencer);
              end
            join
            vseq_done = 1'b1;
            wait(ongoing_reset == 0);
            `uvm_info(`gfn, $sformatf("\nFinished run %0d/%0d w/o reset", i, num_times), UVM_LOW)
          end
          // This process waits a random time (until it's safe to issue a reset) and then issues a
          // reset for a short time, ending when we leave reset again. If the dut goes into reset
          // for another reason while we are waiting, this waits until that reset is finished.
          begin : issue_rand_reset
            wait_to_issue_reset(reset_delay_bound);

            if (!cfg.clk_rst_vif.rst_n) begin
              // If we are in reset at this point then someone else must have put us there! Wait
              // until we leave reset, at which point our job is done.
              @(cfg.clk_rst_vif.rst_n);
            end else begin
              // If we aren't in reset for some other reason then we want to inject one ourselves
              // now. Unless can_reset_with_csr_accesses is true, check that there are no CSR
              // requests in flight as we trigger the reset. If any exist, they won't manage to
              // complete (because apply_resets_concurrently will kill the task that is driving
              // them) and everything will end up out of sync.
              `DV_CHECK(cfg.can_reset_with_csr_accesses || !has_outstanding_access(),
                        "Trying to trigger a reset with outstanding CSR items.")

              ongoing_reset = 1'b1;
              `uvm_info(`gfn, $sformatf("\nIssuing reset for run %0d/%0d", i, num_times), UVM_LOW)
              apply_resets_concurrently();
              do_read_and_check_all_csrs = 1'b1;
              ongoing_reset = 1'b0;
            end
          end
        join_any

        // If vseq_done is false then we have issued a reset (the second process in the fork) but
        // the vseq that we were racing against hasn't noticed the reset and stopped. Killing that
        // process will cause confusing errors (because there will be some sequence that's waiting
        // for a sequencer, but gets killed in the meantime). We tolerate that confusion when
        // can_reset_with_csr_accesses is false (since that's the way the
        // stress_all_with_rand_reset vseq was designed), but want to avoid it happening if
        // can_reset_with_csr_accesses=1: we expect the vseq to run to completion before the reset
        // signal is de-asserted. To make things easier to debug if it hasn't done, fail in an
        // understandable way here.
        if (cfg.can_reset_with_csr_accesses) `DV_CHECK_FATAL(vseq_done)

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

function int cip_base_vseq::wait_cycles_with_no_outstanding_accesses();
  return 10_000;
endfunction

task cip_base_vseq::wait_to_issue_reset(uint reset_delay_bound);
  int cycles_with_no_accesses = 0;
  int cycles_waited;

  int wait_cycles = wait_cycles_with_no_outstanding_accesses();

  `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(
      rand_reset_delay,
      rand_reset_delay inside {[1:reset_delay_bound]};
  )

  // Wait a random number of cycles (up to reset_delay_bound) before triggering the reset.
  `uvm_info(`gfn, $sformatf("Want to issue reset in %0d cycles", rand_reset_delay),
            UVM_MEDIUM)
  cfg.clk_rst_vif.wait_clks(rand_reset_delay);
  cfg.set_intention_to_reset();

  // If we are not happy to apply a reset when a CSR access in flight, we now have to wait until
  // there has been a period with no CSR accesses.
  if (!cfg.can_reset_with_csr_accesses) begin
    `uvm_info(`gfn, $sformatf(
              "Waiting up to %0d cycles for a long enough run of no accesses", wait_cycles),
              UVM_MEDIUM)
    for (cycles_waited = 0;
         cycles_waited < wait_cycles || cycles_with_no_accesses > 0;
         ++cycles_waited) begin
      // If we are actually in reset then there's no need to do any more waiting: the caller can
      // "apply a reset now" (a no-op)
      if (!cfg.clk_rst_vif.rst_n) return;

      if (!has_outstanding_access()) begin
        ++cycles_with_no_accesses;
        if (cycles_with_no_accesses > CyclesWithNoAccessesThreshold) begin
          `uvm_info(`gfn, $sformatf(
                    "Finally no outstanding accesses after %d cycles", cycles_waited),
                    UVM_MEDIUM)
          break;
        end
      end else begin
        // And reset the count if there are outstanding accesses to count only consecutive
        // cycles with no accesses. This will also break out of the loop if the wait has been
        // too long.
        cycles_with_no_accesses = 0;
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
    `DV_CHECK(!has_outstanding_access(), $sformatf(
              "Waited %0d cycles to issue a reset with no outstanding accesses.", cycles_waited))
  end

  // Wait a portion of the clock period, to avoid the reset being synchronised with an edge of the
  // clock.
  #($urandom_range(0, cfg.clk_rst_vif.clk_period_ps) * 1ps);
endtask

task cip_base_vseq::read_and_check_all_csrs_after_reset();
  `uvm_info(`gfn, "running csr hw_reset vseq", UVM_HIGH)

  run_csr_vseq(.csr_test_type("hw_reset"), .do_rand_wr_and_reset(0));
  // abort should not occur after this, as the following is normal seq
  foreach (cfg.m_tl_agent_cfgs[i]) begin
    cfg.m_tl_agent_cfgs[i].csr_access_abort_pct_in_adapter = 0;
  end
  csr_utils_pkg::default_csr_check = UVM_CHECK;
endtask

task cip_base_vseq::run_same_csr_outstanding_vseq(int num_times);
  csr_test_type_e csr_test_type = CsrRwTest; // share the same exclusion as csr_rw_test

  for (int trans = 1; trans <= num_times; trans++) begin
    `uvm_info(`gfn, $sformatf("Running same CSR outstanding test iteration %0d/%0d",
                               trans, num_times), UVM_LOW)

    // first iteration already issued dut_init in pre_start
    if (trans != 1 && $urandom_range(0, 1)) dut_init();

    foreach (cfg.ral_models[ral_name]) begin
      dv_base_reg csrs[$];
      cfg.ral_models[ral_name].get_dv_base_regs(csrs);
      csrs.shuffle();

      foreach (csrs[i]) begin
        uvm_reg_data_t exp_data = csrs[i].get_mirrored_value();
        uvm_reg_data_t rd_data, wr_data, rd_mask, wr_mask;
        csr_excl_item  csr_excl = get_excl_item(csrs[i]);

        rd_mask = get_mask_excl_fields(csrs[i], CsrExclWriteCheck, csr_test_type);
        wr_mask = get_mask_excl_fields(csrs[i], CsrExclWrite, csr_test_type);

        repeat ($urandom_range(2, 20)) begin
          if (cfg.stop_transaction_generators()) break;
          // do read, exclude CsrExclWriteCheck, CsrExclCheck
          if ($urandom_range(0, 1) &&
              !csr_excl.is_excl(csrs[i], CsrExclWriteCheck, csr_test_type)) begin
            tl_access(.addr(csrs[i].get_address()), .write(0), .data(rd_data),
                      .check_exp_data(1), .exp_data(exp_data), .compare_mask(rd_mask),
                      .blocking(0), .tl_sequencer_h(p_sequencer.tl_sequencer_hs[ral_name]));
          end
          // do write, exclude CsrExclWrite
          if ($urandom_range(0, 1) &&
              !csr_excl.is_excl(csrs[i], CsrExclWrite, csr_test_type)) begin
            // Shadowed register requires two writes and thus call predict function twice.
            int num_write = csrs[i].get_is_shadowed() ? 2 : 1;

            `DV_CHECK_STD_RANDOMIZE_FATAL(wr_data)
            wr_data &= wr_mask;
            repeat (num_write) begin
              tl_access(.addr(csrs[i].get_address()), .write(1), .data(wr_data), .blocking(0),
                        .tl_sequencer_h(p_sequencer.tl_sequencer_hs[ral_name]));
              void'(csrs[i].predict(.value(wr_data), .kind(UVM_PREDICT_WRITE)));
            end
            exp_data = csrs[i].get_mirrored_value();
          end
        end
        csr_utils_pkg::wait_no_outstanding_access();

        // Manually lock lockable flds because we use tl_access() instead of csr_wr().
        if (csrs[i].is_wen_reg()) csrs[i].lock_lockable_flds(`gmv(csrs[i]), UVM_PREDICT_WRITE);
      end
    end
  end
endtask

task cip_base_vseq::check_fatal_alert_nonblocking(string alert_name);
  fork
    `DV_SPINWAIT_EXIT(
        forever begin
          // 1 extra cycle to make sure no race condition
          // Plus 2 extra cycles due to alert sampling delay of 2 cycles at the VIF
          for (int i = 0; i <  (alert_esc_agent_pkg::ALERT_B2B_DELAY + 1 + 2); i++) begin
            if (cfg.m_alert_agent_cfgs[alert_name].active_ping) begin
              wait (cfg.m_alert_agent_cfgs[alert_name].active_ping==0);
              i = 0; // restart the delay, since alert may take longer now ping is happening
            end
            cfg.clk_rst_vif.wait_n_clks(1);
            if (cfg.m_alert_agent_cfgs[alert_name].vif.get_alert() == 1) break;
          end
          `DV_CHECK_EQ(cfg.m_alert_agent_cfgs[alert_name].vif.get_alert(), 1,
                       $sformatf("fatal error %0s does not trigger!", alert_name))
          cfg.m_alert_agent_cfgs[alert_name].vif.wait_ack_complete();
        end,
        wait(cfg.under_reset);)
  join_none
endtask

task cip_base_vseq::run_mem_partial_access_vseq(int num_times);
  `loop_ral_models_to_create_threads(
      if (cfg.ral_models[ral_name].mem_ranges.size() > 0) begin
        run_mem_partial_access_vseq_sub(num_times, ral_name);
      end)
endtask

task cip_base_vseq::run_mem_partial_access_vseq_sub(int num_times, string ral_name);
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
    if (cfg.stop_transaction_generators()) break;
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
              // set check_err_rsp to 0 to skip checking rsp in sequence, as there could be a mem
              // which always returns d_error = 1. scb will be overridden to handle it and check
              // the d_error.
              tl_access_w_abort(.addr(addr), .write(1), .data(data),
                                .completed(write_completed), .saw_err(write_error),
                                .check_err_rsp(0), .mask(mask), .blocking(1),
                                .req_abort_pct($urandom_range(0, 100)),
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
              // set check_err_rsp to 0 due to a reason above (in the write section)
              tl_access_w_abort(.addr(addr), .write(0), .data(data),
                                .completed(completed), .saw_err(saw_err),
                                .mask(mask), .blocking(1), .check_err_rsp(0),
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

task cip_base_vseq::run_csr_mem_rw_vseq(int num_times);
  fork
    run_csr_vseq(.csr_test_type("rw"), .do_rand_wr_and_reset(0));
    run_mem_partial_access_vseq(num_times);
  join
endtask

task cip_base_vseq::run_csr_mem_rw_with_rand_reset_vseq(int num_times);
  cip_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T) cip_seq;
  `downcast(cip_seq, this.clone())
  cip_seq.common_seq_type = "csr_mem_rw";
  `uvm_info(`gfn, "Running run_csr_mem_rw_with_rand_reset_vseq", UVM_HIGH)

  // The reset_delay_bound of 1000 here ensures that we don't pick an enormous delay before
  // injecting a reset. Since the IP block is otherwise quiescent, we only really care about what
  // point in a TL transaction the reset occurs. Each TL transaction takes roughly 10 cycles, so
  // there's no need to wait longer than 1000 cycles (which would be ~100 TL transactions).
  run_seq_with_rand_reset_vseq(.seq(cip_seq), .num_times(num_times), .reset_delay_bound(1000));
endtask

function bit[BUS_DBW-1:0]
    cip_base_vseq::get_rand_contiguous_mask(bit [BUS_DBW-1:0] valid_mask = '1);

  bit [BUS_DBW-1:0] mask;
  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask,
                                     $countones(mask ^ {mask[BUS_DBW-2:0], 1'b0}) <= 2;
                                     // for data bits aren't valid (unknown), mask bit should be 0
                                     foreach (valid_mask[i]) {
                                       !valid_mask[i] -> !mask[i];
                                     })
  return mask;
endfunction

function void cip_base_vseq::set_tl_assert_en(bit enable, string path = "*");
  uvm_config_db#(bit)::set(null, path, "tlul_assert_en", enable);
endfunction

`undef loop_ral_models_to_create_threads
