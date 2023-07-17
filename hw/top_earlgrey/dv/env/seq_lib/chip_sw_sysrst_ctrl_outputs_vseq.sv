// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sysrst_ctrl_outputs_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sysrst_ctrl_outputs_vseq)

  `uvm_object_new

  localparam time AON_CYCLE_PERIOD = 5us;
  localparam bit [7:0] OUTPUT_ALL_SET = 8'b11111111;
  localparam bit [7:0] OUTPUT_NONE_SET = 8'b00000000;
  localparam bit [3:0] LOOPBACK_ALL_SET = 4'b1111;
  localparam bit [3:0] LOOPBACK_PARTIAL_SET = 4'b1010;
  localparam uint LOOPBACK_PATTERN_LENGTH = 16;

  typedef enum bit [7:0] {
    PHASE_INITIAL               = 0,
    PHASE_LOOPBACK              = 1,
    PHASE_OVERRIDE_SETUP        = 2,
    PHASE_OVERRIDE_ZEROS        = 3,
    PHASE_OVERRIDE_ONES         = 4,
    PHASE_OVERRIDE_RELEASE      = 5,
    PHASE_OVERRIDE_AND_LOOPBACK = 6,
    PHASE_DONE                  = 7
  } test_phases_e;

  logic [3:0] loopback_pad_read_values;
  logic [7:0] output_pad_read_values;

  virtual task pre_start();
    super.pre_start();
    // Initialize the pad input to 0 to avoid having X values in the initial test phase.
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[SysrstCtrlPadKey0] = 1;
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[SysrstCtrlPadKey1] = 1;
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[SysrstCtrlPadKey2] = 1;
    cfg.chip_vif.pwrb_in_if.pins_pd[0] = 1;
  endtask

  virtual function void write_test_phase(input test_phases_e phase);
    sw_symbol_backdoor_overwrite("kTestPhase", {<<8{phase}});
  endfunction

  virtual function void set_loopback_pads(input bit [3:0] pad_values);
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(0, pad_values[0]);
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(1, pad_values[1]);
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(2, pad_values[2]);
    cfg.chip_vif.pwrb_in_if.drive_pin(0, pad_values[3]);
  endfunction

  virtual function void read_loopback_pads();
    loopback_pad_read_values[0] = cfg.chip_vif.sysrst_ctrl_if.sample_pin(3);
    loopback_pad_read_values[1] = cfg.chip_vif.sysrst_ctrl_if.sample_pin(6);
    loopback_pad_read_values[2] = cfg.chip_vif.sysrst_ctrl_if.sample_pin(7);
    loopback_pad_read_values[3] = cfg.chip_vif.sysrst_ctrl_if.sample_pin(4);
  endfunction

  virtual task read_output_pads();
    #(3 * AON_CYCLE_PERIOD);
    output_pad_read_values[0] = cfg.chip_vif.sysrst_ctrl_if.sample_pin(3);
    output_pad_read_values[1] = cfg.chip_vif.sysrst_ctrl_if.sample_pin(6);
    output_pad_read_values[2] = cfg.chip_vif.sysrst_ctrl_if.sample_pin(7);
    output_pad_read_values[3] = cfg.chip_vif.sysrst_ctrl_if.sample_pin(4);
    output_pad_read_values[4] = cfg.chip_vif.sysrst_ctrl_if.sample_pin(5);
    output_pad_read_values[5] = cfg.chip_vif.pinmux_wkup_if.sample_pin(0);
    output_pad_read_values[6] = cfg.chip_vif.ec_rst_l_if.sample_pin(0);
    output_pad_read_values[7] = cfg.chip_vif.flash_wp_l_if.sample_pin(0);
  endtask

  virtual task sync_with_sw();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    // Wait some additional aon cycles for the synchronizers.
    cfg.chip_vif.aon_clk_por_rst_if.wait_clks(3);
  endtask

  virtual task check_loopback_pattern();
    for (int i = 0; i < LOOPBACK_PATTERN_LENGTH; i++) begin
      set_loopback_pads(i);
      #5ns;
      read_loopback_pads();
      `DV_CHECK_EQ_FATAL(loopback_pad_read_values, i);
    end
  endtask

  virtual task check_loopback_single();
    set_loopback_pads(LOOPBACK_PARTIAL_SET);
    #5ns;
    read_loopback_pads();
    `DV_CHECK_EQ_FATAL(loopback_pad_read_values, LOOPBACK_PARTIAL_SET);
  endtask

  virtual task body();
    super.body();

    // TODO(lowRISC/opentitan:#13373): Revisit pad assignments.
    // pinmux_wkup_if (at Iob7) is re-used for PinZ3WakeupOut
    // due to lack of unused pins. Disable the default drive
    // to this pin.
    cfg.chip_vif.pinmux_wkup_if.drive_en_pin(0, 0);

    write_test_phase(PHASE_INITIAL);
    sync_with_sw();

    write_test_phase(PHASE_LOOPBACK);
    sync_with_sw();
    check_loopback_pattern();

    write_test_phase(PHASE_OVERRIDE_SETUP);
    sync_with_sw();

    write_test_phase(PHASE_OVERRIDE_ZEROS);
    sync_with_sw();
    read_output_pads();
    `DV_CHECK_EQ_FATAL(output_pad_read_values, OUTPUT_NONE_SET);

    write_test_phase(PHASE_OVERRIDE_ONES);
    sync_with_sw();
    read_output_pads();
    `DV_CHECK_EQ_FATAL(output_pad_read_values, OUTPUT_ALL_SET);

    write_test_phase(PHASE_OVERRIDE_RELEASE);
    sync_with_sw();
    check_loopback_single();

    write_test_phase(PHASE_OVERRIDE_AND_LOOPBACK);
    sync_with_sw();
    read_loopback_pads();
    `DV_CHECK_EQ_FATAL(loopback_pad_read_values, LOOPBACK_ALL_SET);

    write_test_phase(PHASE_DONE);
  endtask

endclass
