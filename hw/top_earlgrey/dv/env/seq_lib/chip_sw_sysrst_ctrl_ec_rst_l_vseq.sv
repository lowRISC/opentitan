// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sysrst_ctrl_ec_rst_l_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sysrst_ctrl_ec_rst_l_vseq)

  `uvm_object_new

  localparam time AON_CYCLE_PERIOD = 5us;
  localparam bit [1:0] OUTPUT_ALL_SET = 2'b11;
  localparam bit [1:0] OUTPUT_NONE_SET = 2'b00;
  localparam uint TIMEOUT_VALUE = 5000000;
  localparam uint EC_RST_TIMER = 2000 + 1; // Default value of sysrst_ctrl.EC_RST_CTL

  localparam string PWRMGR_RSTREQ_PATH = "tb.dut.top_earlgrey.u_pwrmgr_aon.rstreqs_i[0]";
  localparam string RST_AON_NI_PATH = "tb.dut.top_earlgrey.u_sysrst_ctrl_aon.rst_aon_ni";

  typedef enum {
    PhaseSetup           = 0,
    PhaseCheckComboReset = 1,
    PhaseOverrideSetup   = 2,
    PhaseOverrideZeros   = 3,
    PhaseOverrideOnes    = 4,
    PhaseDone            = 5
  } test_phases_e;

  logic [1:0] output_pad_read_values;
  logic       output_ec_rst_read_values;
  logic       ec_rst_timer_over;

  virtual task pre_start();
    super.pre_start();
    // Initialize the pad input to 0 to avoid having X values in the initial test phase.
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[SysrstCtrlPadKey0] = 1;
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[SysrstCtrlPadKey1] = 1;
    cfg.chip_vif.sysrst_ctrl_if.pins_pd[SysrstCtrlPadKey2] = 1;
    cfg.chip_vif.pwrb_in_if.pins_pd[0] = 1;
  endtask

  virtual function void write_test_phase(input test_phases_e phase);
    `uvm_info(`gfn, $sformatf("Writing test phase %0d", phase), UVM_MEDIUM)
    sw_symbol_backdoor_overwrite("kTestPhase", {<<8{phase}});
  endfunction

  virtual task set_combo0_pads_low();
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(SysrstCtrlPadKey0, 0);
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(SysrstCtrlPadKey1, 0);
  endtask

  virtual task set_combo0_pads_high();
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(SysrstCtrlPadKey0, 1);
    cfg.chip_vif.sysrst_ctrl_if.drive_pin(SysrstCtrlPadKey1, 1);
  endtask

  virtual task check_ec_rst_pads(bit exp_ec_rst_l);
    #(3 * AON_CYCLE_PERIOD);
    `DV_CHECK_EQ_FATAL(cfg.chip_vif.ec_rst_l_if.sample_pin(0), exp_ec_rst_l)
  endtask

  virtual task check_output_pads(bit exp_ec_rst_l, bit exp_flash_wp_l);
    #(3 * AON_CYCLE_PERIOD);
    `DV_CHECK_EQ_FATAL(cfg.chip_vif.ec_rst_l_if.sample_pin(0), exp_ec_rst_l)
    `DV_CHECK_EQ_FATAL(cfg.chip_vif.flash_wp_l_if.sample_pin(0), exp_flash_wp_l)
  endtask

  virtual task sync_with_sw();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    // Wait some additional aon cycles for the effects of CSR writes to get past
    // synchronizers.
    cfg.chip_vif.aon_clk_por_rst_if.wait_clks(3);
  endtask

  virtual task control_ec_rst_low(int min_exp_cycles);
    int timeout_count = 0;
    `DV_WAIT(cfg.chip_vif.ec_rst_l_if.pins[0] === 0)
    // Count the number of cycles before ec_rst_l is inactive.
    forever begin
      if (cfg.chip_vif.ec_rst_l_if.sample_pin(0) == 0) begin
        timeout_count++;
      end else begin
        break;
      end
      // Use 1 cycle delay (AON CLK) between samples of ec_rst.
      cfg.chip_vif.aon_clk_por_rst_if.wait_clks(1);
    end
    // Check that the active ec_rst_l cycles exceeds the expected minimum.
    `DV_CHECK(timeout_count > min_exp_cycles)
    ec_rst_timer_over = 1; // set this for the other thread to continue
  endtask

  virtual task check_ec_rst_with_transition(string path, int exp_value);
    bit retval = 0;
    int timeout_count = 0;
    forever begin
      `DV_CHECK(uvm_hdl_read(path, retval));
      if (retval == exp_value) begin
        timeout_count++;
        if (timeout_count >= TIMEOUT_VALUE) begin
          `uvm_error(`gfn, $sformatf("Timed out waiting for %0s to go to %d \n",
              path, exp_value))
        end
      end else begin
        break;
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
    // Check that ec_rst is low.
    cfg.clk_rst_vif.wait_clks(1);
    if (cfg.chip_vif.ec_rst_l_if.sample_pin(0) == 1) begin
      `uvm_error(`gfn, "Unexpected ec_rst high after reset request.")
    end
  endtask

  virtual task body();
    super.body();

    // TODO(lowRISC/opentitan:#13373): Revisit pad assignments.
    // pinmux_wkup_vif (at Iob7) is re-used for PinZ3WakeupOut
    // due to lack of unused pins. Disable the default drive
    // to this pin.
    cfg.chip_vif.pinmux_wkup_if.drive_en_pin(0, 0);
    set_combo0_pads_high();

    // At this point WP_L and EC_RST_L have not been released yet after reset.
    `DV_CHECK_EQ(cfg.chip_vif.flash_wp_l_if.pins, 0)
    `DV_CHECK_EQ(cfg.chip_vif.ec_rst_l_if.pins, 0)

    write_test_phase(PhaseSetup);

    // The sysrst_ctrl initialization in PhaseSetup releases
    // both flash_wp and ec_rst. Wait for them to go high here.
    fork
      `DV_WAIT(cfg.chip_vif.flash_wp_l_if.pins,
               "Timed out waiting for flash_wp to go high.",
               TIMEOUT_VALUE /* ns */)
      `DV_WAIT(cfg.chip_vif.ec_rst_l_if.pins,
               "Timed out waiting for ec_rst to go high.",
               TIMEOUT_VALUE /* ns */)
    join

    // Make sure software is waiting for a reset.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    set_combo0_pads_low();
    ec_rst_timer_over = 0;

    fork
      begin
        control_ec_rst_low(EC_RST_TIMER);
      end
      begin
        check_ec_rst_with_transition(PWRMGR_RSTREQ_PATH, 1'b0);
        check_ec_rst_with_transition(RST_AON_NI_PATH , 1'b0);
        sync_with_sw();
        write_test_phase(PhaseCheckComboReset);
        sync_with_sw();
        `DV_WAIT(ec_rst_timer_over)
        // Wait some additional aon cycles for the synchronizers.
        cfg.chip_vif.aon_clk_por_rst_if.wait_clks(3);

        write_test_phase(PhaseOverrideSetup);
        sync_with_sw();
        check_ec_rst_pads(1'b0);

        write_test_phase(PhaseOverrideZeros);
        sync_with_sw();
        check_output_pads(1'b0, 1'b0);

        write_test_phase(PhaseOverrideOnes);
        sync_with_sw();
        check_output_pads(1'b1, 1'b1);

        write_test_phase(PhaseDone);
      end
    join
  endtask
endclass
