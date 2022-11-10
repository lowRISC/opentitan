// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_disable_auto_req_mode_vseq extends edn_base_vseq;
  `uvm_object_utils(edn_disable_auto_req_mode_vseq)
  `uvm_object_new

  push_pull_host_seq#(edn_pkg::FIPS_ENDPOINT_BUS_WIDTH)
      m_endpoint_pull_seq[MAX_NUM_ENDPOINTS];

  uint   num_ep_reqs, num_cs_reqs, wait_disable;
  bit    csrng_init_done;

  virtual task rand_toggle_edn_enable();
    bit [TL_DW-1:0] ctrl_val;
    string main_sm_d_path = "tb.dut.u_edn_core.u_edn_main_sm.state_d";
    // TODO: modify wr_cmd and add back AutoLoadIns.
    state_e auto_req_sts[$] = {AutoFirstAckWait, AutoAckWait, AutoDispatch,
            AutoCaptGenCnt, AutoSendGenCmd, AutoCaptReseedCnt, AutoSendReseedCmd};

    // CSRNG requests will drop if disablement is sent.
    $assertoff(0, "tb.csrng_if.cmd_push_if.H_DataStableWhenValidAndNotReady_A");
    $assertoff(0, "tb.csrng_if.cmd_push_if.ValidHighUntilReady_A");

    // Random delay, disable edn
    if ($urandom_range(0, 1)) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wait_disable,
                                         wait_disable inside
                                         { [20:300] };)
      cfg.clk_rst_vif.wait_clks(wait_disable);
      `uvm_info(`gfn, $sformatf("Wait %0d clk cycles then issue edn disablement",
                 wait_disable), UVM_HIGH)
    end else begin
      bit [8:0] state_val;
      int rand_st_idx = $urandom_range(0, auto_req_sts.size()-1);
      `uvm_info(`gfn, $sformatf("Wait until %0s state then issue edn disablement",
                auto_req_sts[rand_st_idx].name), UVM_HIGH)
      `DV_SPINWAIT(
          while (state_val != auto_req_sts[rand_st_idx]) begin
            uvm_hdl_read(main_sm_d_path, state_val);
            cfg.clk_rst_vif.wait_clks(1);
          end)
    end

    `DV_WAIT(csrng_init_done);
    wait_no_outstanding_access();
    ctrl_val = {MuBi4False, MuBi4True, MuBi4False, MuBi4False};
    csr_wr(.ptr(ral.ctrl), .value(ctrl_val));
    cfg.edn_vif.drive_edn_disable(1);
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 50));

    // Reset EDN fifos
    csr_wr(.ptr(ral.ctrl.cmd_fifo_rst), .value(MuBi4True));
    csr_wr(.ptr(ral.ctrl.cmd_fifo_rst), .value(MuBi4False));

    // Enable edn
    wait_no_outstanding_access();
    cfg.edn_vif.drive_edn_disable(0);
    edn_init();

    // Send instantiate cmd after EDN is re-abled for auto_req_mode.
    instantiate_csrng();
    `uvm_info(`gfn, "EDN toggle enable field task done", UVM_HIGH);
  endtask

  task body();
    bit edn_enable_toggle_done;
    bit [MAX_NUM_ENDPOINTS-1:0] edn_reqs, edn_done;
    super.body();
    num_cs_reqs    = cfg.num_endpoints;
    num_ep_reqs    = num_cs_reqs * csrng_pkg::GENBITS_BUS_WIDTH/ENDPOINT_BUS_WIDTH;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(edn_reqs, $countones(edn_reqs) == cfg.num_endpoints;)

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
          edn_done[j] = 1;
          `uvm_info(`gfn, $sformatf("EDN requesters %0h, current status %0h", edn_reqs, edn_done),
                    UVM_HIGH)
        end join_none;
      end
    end

    // Instantiated CSRNG to enable EDN auto_req_mode.
    fork begin
      // Reseed as frequently as possible so we can hit more FSM coverage.
      csr_wr(.ptr(ral.max_num_reqs_between_reseeds), .value(1));
      instantiate_csrng();
      csrng_init_done = 1;
    end join_none;

    fork begin
      rand_toggle_edn_enable();
      edn_enable_toggle_done = 1;
    end join_none;

    // Wait for EDN disablement/enablement done, and wait for EDN request done,
    // then disable csrng_device_driver to exit the sequence.
    // Otherwise the testbench will hanging at waiting for more EDN requests.
    `DV_WAIT(edn_enable_toggle_done == 1);
    `DV_WAIT(edn_done == edn_reqs);
    cfg.edn_vif.drive_edn_disable(1);
  endtask

endclass
