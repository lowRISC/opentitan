// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_disable_auto_req_mode_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_disable_auto_req_mode_vseq)
  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)
      m_endpoint_pull_seq[MAX_NUM_ENDPOINTS];

  mailbox #(bit) mbox_kill_endpoint_reqs, mbox_kill_edn_init;
  bit edn_reenable_done;
  bit [MAX_NUM_ENDPOINTS-1:0] endpoint_reqs_done;

  task await_random_main_sm_auto_state();
    string state_path;
    state_e exp_state;
    state_path = cfg.edn_vif.sm_err_path("edn_main_sm");

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(exp_state,
                                       exp_state inside {AutoLoadIns, AutoFirstAckWait, AutoAckWait,
                                                         AutoDispatch, AutoCaptGenCnt,
                                                         AutoSendGenCmd, AutoCaptReseedCnt,
                                                         AutoSendReseedCmd};)

    `uvm_info(`gfn, $sformatf("Waiting for main_sm to reach state %s.", exp_state.name()), UVM_LOW)
    `DV_SPINWAIT(
      forever begin
        uvm_hdl_data_t val;
        state_e act_state;
        cfg.clk_rst_vif.wait_n_clks(1);
        `DV_CHECK(uvm_hdl_read(state_path, val))
        act_state = state_e'(val);
        if (act_state == exp_state) break;
      end
    )
  endtask

  task disable_edn(bit backdoor);
    bit [TL_DW-1:0] ctrl_val;

    // Write EDN's control CSR.
    ctrl_val = {MuBi4False, MuBi4True, MuBi4False, MuBi4False};

    if (!backdoor) begin
      wait_no_outstanding_access();
    end else begin
      cfg.backdoor_disable = 1'b1; // Notify scoreboard of backdoor disable
    end

    csr_wr(.ptr(ral.ctrl), .value(ctrl_val), .backdoor(backdoor), .predict(backdoor));

    // Let CSRNG agent know that EDN is disabled.
    cfg.edn_vif.drive_edn_disable(1);
  endtask

  task randomly_disable_edn();
    if ($urandom_range(1, 10) > 8) begin
      uint wait_disable;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wait_disable, wait_disable inside { [1:300] };)
      `uvm_info(`gfn, $sformatf("Waiting %0d clock cycles before disabling EDN.", wait_disable),
                UVM_LOW)
      cfg.clk_rst_vif.wait_n_clks(wait_disable);
    end else begin
      await_random_main_sm_auto_state();
    end

    `uvm_info(`gfn, $sformatf("Wait complete, disabling EDN."), UVM_LOW)
    disable_edn(.backdoor(1));
  endtask

  virtual task pre_start();
    // Initialize variables for inter-thread communication.
    mbox_kill_endpoint_reqs = new();
    mbox_kill_edn_init = new();
    edn_reenable_done = 0;

    // Create background thread that randomly disables EDN and later re-enables it.
    fork
      begin
        bit unused;
        // Wait for EDN to come out of reset.
        wait(cfg.clk_rst_vif.rst_n);
        // Disable EDN after a random number of cycles or in a random state.
        randomly_disable_edn();
        // Abort any open SW commands and wait for CSR accesses to complete, as simply killing their
        // thread would create problems later due to unterminated accesses.
        cfg.abort_sw_cmd = 1;
        wait_no_outstanding_access();
        // Kill EDN initialization and endpoint requests if necessary.
        mbox_kill_edn_init.put(1'b1);
        mbox_kill_endpoint_reqs.put(1'b1);
        // Wait before re-enabling EDN.
        `uvm_info(`gfn, $sformatf("Waiting before re-enabling EDN"), UVM_LOW)
        cfg.clk_rst_vif.wait_n_clks($urandom_range(1, 1000));
        `uvm_info(`gfn, $sformatf("Wait complete"), UVM_LOW)
        // Empty mailbox (necessary in case the previous EDN initialization completed before we
        // killed it).
        void'(mbox_kill_edn_init.try_get(unused));
        cfg.abort_sw_cmd = 0;
        // Let CSRNG know that we're re-enabling EDN.
        device_init();
        // Initialize EDN again -- this time without randomly disabling EDN.
        `uvm_info(`gfn, $sformatf("Re-enabling EDN"), UVM_LOW)
        edn_init();
        endpoint_reqs();
        edn_reenable_done = 1;
      end
    join_none

    super.pre_start();
  endtask

  virtual task edn_init(string reset_kind = "HARD");
    `DV_SPINWAIT_EXIT(
        // Main thread: Initialize EDN, write Instantiate command, and set the maximum number of
        // requests between reseeds to 1 (to maximize coverage over time).
        super.edn_init();
        cfg.clk_rst_vif.wait_clks(1);
        instantiate_csrng(.mode("auto_mode"));
        csr_wr(.ptr(ral.max_num_reqs_between_reseeds), .value(1));
      ,
        // Exit thread: Wait for a signal from the thread that randomly disables EDN.
        bit unused;
        mbox_kill_edn_init.get(unused);
      , "Killed edn_init thread."
    )
  endtask

  task endpoint_reqs();
    bit [MAX_NUM_ENDPOINTS-1:0] edn_reqs;
    uint num_cs_reqs, num_ep_reqs;
    num_cs_reqs    = cfg.num_endpoints;
    num_ep_reqs    = num_cs_reqs * csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(edn_reqs, $countones(edn_reqs) == cfg.num_endpoints;)

    endpoint_reqs_done = '0;

    for (int i = 0; i < MAX_NUM_ENDPOINTS; i++) begin
      automatic int j = i;
      if (edn_reqs[j]) begin
        fork begin
          // Create/Configure/Start endpoint_pull_seq
          m_endpoint_pull_seq[j] = push_pull_host_seq#(FIPS_ENDPOINT_BUS_WIDTH)::
              type_id::create($sformatf("m_endpoint_pull_seq[%0d]", j));
          m_endpoint_pull_seq[j].num_trans = num_ep_reqs;

          // Start endpoint_pull sequences
          m_endpoint_pull_seq[j].start
              (p_sequencer.endpoint_sequencer_h[j]);

          endpoint_reqs_done[j] = 1;
        end join_none;
      end else begin
        endpoint_reqs_done[j] = 1;
      end
    end
  endtask

  task body();
    super.body();

    `DV_SPINWAIT_EXIT(
        // Thread 1: Start EDN endpoint requests, which is non-blocking, and keep the thread running
        // until it gets killed.
        endpoint_reqs();
        wait(0);
      ,
        // Thread 2: Wait for signal to kill the other thread.
        bit unused;
        mbox_kill_endpoint_reqs.get(unused);
      , "Killed endpoint_reqs in body"
    )

    `DV_WAIT(edn_reenable_done)
    `uvm_info(`gfn, $sformatf("EDN re-enable done"), UVM_LOW)
    `DV_WAIT(endpoint_reqs_done == '1)
    `uvm_info(`gfn, $sformatf("endpoint reqs done"), UVM_LOW)
  endtask

  virtual task post_start();
    super.post_start();
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
    // Disable EDN to terminate all the pending transactions in auto_req_mode.
    cfg.edn_vif.drive_edn_disable(1);
    csr_wr(.ptr(ral.ctrl.edn_enable), .value(MuBi4False));
  endtask

endclass
