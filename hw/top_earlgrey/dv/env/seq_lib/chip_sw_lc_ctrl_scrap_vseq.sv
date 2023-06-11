// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
class chip_sw_lc_ctrl_scrap_vseq extends chip_sw_lc_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_scrap_vseq)
  `uvm_object_new

  rand lc_ctrl_state_pkg::dec_lc_state_e src_state;
  rand bit perform_transition_via_sw;

  constraint valid_src_state_c {
    !(src_state inside {DecLcStScrap, DecLcStInvalid, DecLcStPostTrans, DecLcStEscalate});
    solve src_state before perform_transition_via_sw;
  }

  // don't try to perform transition via SW for the following states
  constraint transition_via_sw_c {
    src_state inside {DecLcStRaw,
                      DecLcStTestLocked0,
                      DecLcStTestLocked1,
                      DecLcStTestLocked2,
                      DecLcStTestLocked3,
                      DecLcStTestLocked4,
                      DecLcStTestLocked5,
                      DecLcStTestLocked6} ->
    perform_transition_via_sw == 0;
  }

  function void pre_randomize();
    super.pre_randomize();

    // disable source state randomization if it's set by the command line
    // and set the source state value
    if ($test$plusargs("src_dec_state")) begin
      this.valid_src_state_c.constraint_mode(0);
      this.src_state.rand_mode(0);

      // source state is randomized by default,
      // but if a plusarg is supplied, assign the given value
      `DV_GET_ENUM_PLUSARG(lc_ctrl_state_pkg::dec_lc_state_e, src_state, src_dec_state)
      `uvm_info(`gfn, $sformatf("Source state is %0s", src_state.name), UVM_MEDIUM)
    end
  endfunction : pre_randomize

  function void post_randomize();
    super.post_randomize();

    // a guard to check we didn't screw up
    `DV_CHECK_FATAL(src_state != DecLcStScrap)
  endfunction : post_randomize

  virtual function void backdoor_override_otp();
    // Override the LC partition to TestLocked1 state.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(
        lc_ctrl_dv_utils_pkg::encode_lc_state(src_state));
  endfunction : backdoor_override_otp

  protected task sync_with_sw();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusBooted)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
  endtask : sync_with_sw

  protected task perform_transition_to_scrap();
    // perform transition through JTAG if we're not using SW transition
    // or if SW transition isn't allowed (RAW/TEST_LOCKED*)
    if (!perform_transition_via_sw) begin : jtag_transition
      // Change to the external clock and
      // acquire the LC controller access to registers
      switch_to_external_clock();

      // perform a LC state transition
      jtag_lc_state_transition(src_state, DecLcStScrap);
    end : jtag_transition

    // else, we're performing the transition though SW
    else begin : sw_transition
      // sync with SW, and let perform the transition
      sync_with_sw();
    end : sw_transition

    // wait for transition to end
    wait_lc_transition_successful();

    // LC state transition requires a chip reset.
    `uvm_info(`gfn, $sformatf("Applying reset after lc transition from %s state", src_state.name),
              UVM_MEDIUM)
    apply_reset();
  endtask : perform_transition_to_scrap

  virtual task body();
    bit [BUS_DW-1:0] state;
    super.body();
    // tell SW whether the transition is done by JTAG or SW
    sw_symbol_backdoor_overwrite("kPerformTransitionBySW", {perform_transition_via_sw});

    // perform the transition to SCRAP state
    perform_transition_to_scrap();

    // acquire again access to LC controller
    // this now can only be done by JTAG, as we're in SCRAP state
    wait_lc_initialized(.allow_err(1));

    // read the LC state from the LC controller and
    // check LC state is indeed in SCRAP
    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.lc_state.get_offset(),
                                        p_sequencer.jtag_sequencer_h, state);
    `DV_CHECK_EQ(state, {DecLcStateNumRep{DecLcStScrap}})
  endtask : body

  task post_start();
    // post-transition reset is performed via SV
    // however, as it's the last step of the test
    // and SW can't execute (SCRAP state),
    // we'll need to override the SW test status
    // from there
    override_test_status_and_finish(.passed(1));

    super.post_start();
  endtask : post_start
endclass : chip_sw_lc_ctrl_scrap_vseq
