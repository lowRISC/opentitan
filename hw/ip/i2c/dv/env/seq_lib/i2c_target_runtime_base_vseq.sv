// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Base sequence for i2c target-mode tests that creates a framework to be
// used for directed-tests which involve dropping data.
//
// Without precise modelling, random datapath drop events make it difficult to
// predict the values of sent/rcvd item counts in the scoreboard, and to tie
// up obs items against the correct exp.
// This base sequence is a framework that generates stimulus for 'seq_runtime_us'
// microseconds, intended for any test execution that can't rely on the
// the scoreboard's sent / rcvd counters. (This framework overrides the framework
// defined in 'i2c_target_smoke_vseq::body()'). Hook-methods are defined which
// allow vseq's to set-up and tear-down directed test cases, returning the checking
// machinery to a good known state for the next iteration.
//
class i2c_target_runtime_base_vseq extends i2c_target_smoke_vseq;
  `uvm_object_utils(i2c_target_runtime_base_vseq)
  `uvm_object_new

  ///////////////////
  // CONTROL KNOBS //
  ///////////////////

  // Stimulus is generated until either of the following two conditions are met:
  // - The runtime 'seq_runtime_us' is reached.
  // - The stimulus sequence has been run to completion 'stim_cnt_limit' times.
  // Setting either control knob to 0 will disable it.

  // Sequence run time in us.
  // Derived sequences should set this to an appropriate value in 'pre_start'.
  int seq_runtime_us = 0;

  // Curtail the stimulus after the following number of iterations.
  uint stim_cnt_limit = 0;

  /////////////////////
  // CLASS VARIABLES //
  /////////////////////

  // Increment this counter for each controller stimulus sequence that is run on the agent.
  protected uint stim_cnt = 0;

  // This bit is set when a timer that runs for 'seq_runtime_us' expires.
  // When this occurs, the test is about to end.
  protected bit timer_expired = 0;

  typedef enum int {
    StIdle,
    StStimGen,
    StPreHook,
    StStim,
    StPostHook,
    StComplete
  } runtime_state_t;
  // This state variable controls the test execution between the agent
  // stimulus-generation loop inside body(), and the test_event() loop which
  // derived tests can hook-into to drive stimulus and check state at certain
  // controlled times throughout the test.
  protected runtime_state_t runtime_state = StIdle;

  // The stimulus sequence that will be run on the agent.
  // Derived testcases can observe the generated stimulus before it is driven by the agent
  // by examining the items in 'm_i2c_host_seq.req_q' during the start_of_stim_hook().
  protected i2c_target_base_seq m_i2c_host_seq;

  ///////////////////
  // CLASS METHODS //
  ///////////////////

  // Common routine to advance the runtime state machine.
  // This is used to synchronize the test runtime between generate_stimulus() and
  // test_event().
  //
  // Small delays around the state change are added, to prevent races between waiting on
  // state changes and advancing to a new state.
  virtual task advance_runtime_state(runtime_state_t to);
    #1ns;
    `uvm_info(`gfn, $sformatf("Advancing runtime state to %0s", to.name()), UVM_MEDIUM)
    runtime_state = to;
    #1ns;
  endtask: advance_runtime_state

  virtual task wait_for_runtime_state(runtime_state_t await);
    `uvm_info(`gfn, $sformatf("Waiting for runtime state %0s", await.name()), UVM_MEDIUM)
    wait(runtime_state == await);
  endtask: wait_for_runtime_state

  virtual task body();
    `DV_CHECK(seq_runtime_us > 0 || stim_cnt_limit > 0)

    initialization();

    fork
      while (!timer_expired) begin
        fork
          generate_stimulus();
          test_event();
        join
        if (timer_expired) advance_runtime_state(.to(StComplete));
      end
      while (!cfg.stop_intr_handler) process_target_interrupts();
      begin
        // Count out the time delay specified by 'seq_runtime_us', then bring the stimulus to
        // a close.
        fork
          if (seq_runtime_us) #(seq_runtime_us * 1us);
          if (stim_cnt_limit) wait(stim_cnt == stim_cnt_limit);
        join_any
        timer_expired = 1;
        `uvm_info(`gfn, "Runtime_base_vseq timer expired", UVM_MEDIUM)
        // Only stop the interrupt handler once the stimulus generation and checking routines
        // have completed. The 'StComplete' state is used to synchronize on this event.
        wait_for_runtime_state(.await(StComplete));
        `uvm_info(`gfn, "Stopping interrupt handlers.", UVM_MEDIUM)
        cfg.stop_intr_handler = 1; // Stop the process_target_interrupts() irq-handler routine.
      end
    join
  endtask

  virtual task generate_stimulus();
    wait_for_runtime_state(.await(StStimGen));

    // Construct the I2C Controller sequence that defines the agent stimulus
    // for this test.
    begin
      i2c_item txn_q[$];
      `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
      create_txn(txn_q);
      fetch_txn(txn_q, m_i2c_host_seq.req_q);
    end

    advance_runtime_state(.to(StPreHook));
    wait_for_runtime_state(.await(StStim));

    // Run the stimulus sequence on the agent
    m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
    stim_cnt++;
  endtask

  // Child vseq's should implement these routines to perform checks before and
  // after the transaction generated by the agent.
  virtual task setup_hook; endtask
  virtual task start_of_stim_hook; endtask
  virtual task end_of_stim_hook; endtask

  virtual task test_event();
    setup_hook();

    advance_runtime_state(.to(StStimGen));
    wait_for_runtime_state(.await(StPreHook));

    start_of_stim_hook();

    advance_runtime_state(.to(StStim));
    // Wait until the end of the stimulus transaction.
    wait(cfg.m_i2c_agent_cfg.got_stop);

    advance_runtime_state(.to(StPostHook));

    // Reset 'got_stop' for the next iteration, which is used by
    // the timer process to end gracefully.
    cfg.m_i2c_agent_cfg.got_stop = 0;

    end_of_stim_hook();
  endtask


  // The TB's interrupt handler should call this routine whenever the "tx_stretch"
  // interrupt is pending.
  // (This definition overrides the base_vseq implementation)
  //
  // Desc:
  //   If txfifo is not full, write more data into it.
  //   (The scoreboard captures these writes to form its expectations)
  virtual task proc_intr_txstretch();
    uvm_reg_data_t curr_txlvl;
    int num_writes, max_writes;

    // One acqfifo entry can be popped every 9 bit cycles (8bit + ack),
    // where a cycle takes (thigh + tlow) cycles of the underlying clock.
    int acq_rd_cyc = 9 * (thigh + tlow);
    int delay = $urandom_range(0, 10);
    `uvm_info(`gfn, "proc_intr_txstretch()", UVM_MEDIUM)
    cfg.clk_rst_vif.wait_clks(delay * acq_rd_cyc);

    // Determine how many writes we are going to make to the txfifo.
    // This algorithm is fairly crude.
    csr_rd(.ptr(ral.target_fifo_status.txlvl), .value(curr_txlvl));
    max_writes = I2C_TX_FIFO_DEPTH - curr_txlvl;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_writes,
      num_writes dist {[ 1:               16] := 7,
                       [17:I2C_TX_FIFO_DEPTH] := 1,
                            I2C_TX_FIFO_DEPTH := 2};
    )
    if (num_writes > max_writes) num_writes = max_writes;

    repeat (num_writes) begin
      bit [7:0] wdata = $urandom();
      csr_wr(.ptr(ral.txdata), .value(wdata));
      `uvm_info(`gfn, $sformatf("proc_intr_txstretch(): wrote 0x%2x to TXFIFO.", wdata), UVM_MEDIUM)
    end
  endtask: proc_intr_txstretch

  // ACQFIFO handler routine
  // - Random delay before reading, of between 0 and 10*(9*t_bit) cycles
  // - 25% chance to pop all entries each time, otherwise just pop one.
  //
  task process_acq();

    // One acqfifo entry can be popped every 9 bit cycles (8bit + ack),
    // where a cycle takes (thigh + tlow) cycles of the underlying clock.
    int acq_rd_cyc = 9 * (thigh + tlow);

    while (!cfg.stop_intr_handler) begin
      bit fifo_empty;
      bit pop_all = ($urandom_range(0,3) > 0);
      int delay = $urandom_range(0, 10);
      cfg.clk_rst_vif.wait_clks(delay * acq_rd_cyc);
      if (runtime_state == StStim) read_acq_fifo(~pop_all, fifo_empty);
    end

    `uvm_info(`gfn, "End of process_acq().", UVM_MEDIUM)
  endtask: process_acq

endclass
