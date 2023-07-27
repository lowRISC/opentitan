// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test hand shake sequence between sv and c
// 1. sv: `write_test_phase`(PHASE)
//    and waiting for test status change from c
// 2. c: check kTestPhase in switch
// 3. c: `wait_next_test_phase`
//    set test status and write all 1 to flash and wait for
//    backdoor update from sv
// 4. sv: Move to next routine and repeat #1 with the next PHASE
class chip_sw_sysrst_ctrl_ulp_z3_wakeup_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sysrst_ctrl_ulp_z3_wakeup_vseq)
  `uvm_object_new

  // The value of configured debounce value
  localparam uint DEBOUNCE_SW_VALUE = 20;

  typedef enum bit [7:0] {
    PHASE_INIT                  = 0,
    PHASE_DRIVE_ZERO            = 1,
    PHASE_WAIT_NO_WAKEUP        = 2,
    PHASE_GLITCH_LID_OPEN       = 3,
    PHASE_WAIT_WAKEUP           = 4,
    PHASE_DONE                  = 5
  } test_phases_e;

  virtual task pre_start();
    super.pre_start();
    // Initialize the pad input to 0 to avoid having X values in the initial test phase.
    // The following correspond to IOR13, IOC7, IOC9 respectively
    cfg.chip_vif.pwrb_in_if.pins_pd[0] = 1;
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[4] = 1;
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[5] = 1;
  endtask

  virtual task post_start();
    //cfg.chip_vif.pwrb_in_if.disconnect();
    //cfg.chip_vif.sysrst_ctrl_if.disconnect();
    cfg.chip_vif.pwrb_in_if.pins_pd[0] = 1;
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[4] = 1;
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[5] = 1;
    super.post_start();
  endtask

  virtual function void drive_zero_pads();
    // PAD_PWRB_PATH <-> IOR13
    cfg.chip_vif.pwrb_in_if.drive_pin(0, 1'b0);
    // PAD_ACPRESENT_PATH <-> IOC7
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(4, 1'b0);
    // PAD_LIDOPEN_PATH <-> IOC9
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(5, 1'b0);
  endfunction

  virtual task glitch_lid_open();
    uint glitch_loop_cnt = $urandom_range(1, DEBOUNCE_SW_VALUE - 1);
    bit glitchy_bit = 1'b1;
    // The following loop ends before the second sampling of debounce happens
    for (int i = 0; i < glitch_loop_cnt ; i++) begin
      // PAD_LIDOPEN_PATH <- glitchy_bit;
      cfg.chip_vif.sysrst_ctrl_if.drive_pin(5, glitchy_bit);
      cfg.chip_vif.aon_clk_por_rst_if.wait_clks(1);
      glitchy_bit = ~glitchy_bit;
    end
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(5, 1'b1);
  endtask

  virtual function void write_test_phase(test_phases_e phase);
    bit [7:0] test_phase[1];
    test_phase[0] = phase;
    `uvm_info(`gfn, $sformatf("Writing test phase %0d", phase), UVM_MEDIUM)
    sw_symbol_backdoor_overwrite("kTestPhase", test_phase);
  endfunction

  virtual function void check_wakeup_pin();
    logic wakeup_result;
    // Read PAD_Z3WAKEUP_PATH <-> IOB7
    wakeup_result = cfg.chip_vif.pinmux_wkup_if.sample_pin(0);
    `DV_CHECK_EQ_FATAL(wakeup_result, 1'b1);
  endfunction

  virtual task wait_wakeup_time();
    // Wait until we are sure that we passed the second sampling of debounce logic
    cfg.chip_vif.aon_clk_por_rst_if.wait_clks(DEBOUNCE_SW_VALUE);
  endtask

  virtual task sync_with_sw();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    #(cfg.flash_write_latency_in_us * 1us);
  endtask

  virtual task body();
    super.body();

    // Add status sync at the beginning of the test
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest,
             "wait for initial test state",
             5_000_000)

    // TODO(lowRISC/opentitan:#13373): Revisit pad assignments.
    // pinmux_wkup_vif (at Iob7) is re-used for PinZ3WakeupOut
    // due to lack of unused pins. Disable the default drive
    // to this pin.
    cfg.chip_vif.pinmux_wkup_if.drive_en_pin(0, 0);

    write_test_phase(PHASE_INIT);
    sync_with_sw();

    drive_zero_pads();
    write_test_phase(PHASE_DRIVE_ZERO);
    sync_with_sw();

    wait_wakeup_time();
    write_test_phase(PHASE_WAIT_NO_WAKEUP);
    // Skip sync_with_sw, because SW starts sleeping after Wfi
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)

    glitch_lid_open();
    write_test_phase(PHASE_GLITCH_LID_OPEN);
    sync_with_sw();

    wait_wakeup_time();
    write_test_phase(PHASE_WAIT_WAKEUP);
    check_wakeup_pin();
    sync_with_sw();

    write_test_phase(PHASE_DONE);
  endtask

endclass : chip_sw_sysrst_ctrl_ulp_z3_wakeup_vseq
