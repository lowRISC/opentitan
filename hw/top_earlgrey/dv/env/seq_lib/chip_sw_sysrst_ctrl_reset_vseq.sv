// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sysrst_ctrl_reset_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sysrst_ctrl_reset_vseq)

  `uvm_object_new

  localparam string PAD_KEY0_PATH = "tb.dut.IOB3";
  localparam string PAD_KEY1_PATH = "tb.dut.IOB6";
  localparam string PAD_KEY2_PATH = "tb.dut.IOB8";
  localparam string PAD_PWRB_PATH = "tb.dut.IOB9";
  localparam string PAD_ACPRES_PATH = "tb.dut.IOC7";
  localparam string PAD_LIDOPEN_PATH = "tb.dut.IOC9";
  localparam string PAD_ECRST_PATH = "tb.dut.IOR8";
  localparam string PAD_FLASHWP_PATH = "tb.dut.IOR9";
  localparam string PWRMGR_RSTREQ_PATH = "tb.dut.top_earlgrey.u_pwrmgr_aon.rstreqs_i[0]";
  localparam string RST_AON_NI_PATH = "tb.dut.top_earlgrey.u_sysrst_ctrl_aon.rst_aon_ni";

  localparam uint TIMEOUT_VALUE = 5000000;

  localparam uint COMBO_RESET_PHASE = 0;
  localparam uint DEEP_SLEEP_WAKEUP_PHASE = 1;
  localparam uint DEEP_SLEEP_RESET_PHASE = 2;
  localparam uint FINAL_CHECK_PHASE = 3;

  virtual task set_combo0_pads_low();
    `DV_CHECK(uvm_hdl_force(PAD_KEY0_PATH, 0));
    `DV_CHECK(uvm_hdl_force(PAD_KEY1_PATH, 0));
  endtask

  virtual task set_combo1_pads_low();
    `DV_CHECK(uvm_hdl_force(PAD_KEY2_PATH, 0));
    `DV_CHECK(uvm_hdl_force(PAD_PWRB_PATH, 0));
  endtask

  virtual task set_all_pads_high();
    `DV_CHECK(uvm_hdl_force(PAD_KEY0_PATH, 1));
    `DV_CHECK(uvm_hdl_force(PAD_KEY1_PATH, 1));
    `DV_CHECK(uvm_hdl_force(PAD_KEY2_PATH, 1));
    `DV_CHECK(uvm_hdl_force(PAD_PWRB_PATH, 1));
    `DV_CHECK(uvm_hdl_force(PAD_ACPRES_PATH, 1));
    `DV_CHECK(uvm_hdl_force(PAD_LIDOPEN_PATH, 1));
  endtask

  virtual task set_ulp_pads_deassert();
    `DV_CHECK(uvm_hdl_force(PAD_ACPRES_PATH, 0));
    `DV_CHECK(uvm_hdl_force(PAD_PWRB_PATH, 1));
    `DV_CHECK(uvm_hdl_force(PAD_LIDOPEN_PATH, 0));
  endtask

  virtual task set_ulp_pads_assert();
    // Set the LidOpen Pad to High.
    `DV_CHECK(uvm_hdl_force(PAD_LIDOPEN_PATH, 1));
  endtask

  virtual task wait_for_ec_rst_high();
    bit ec_rst_value = 0;
    int timeout_count = 0;
    forever begin
      `DV_CHECK(uvm_hdl_read(PAD_ECRST_PATH, ec_rst_value));
      if (ec_rst_value == 0) begin
        timeout_count++;
        if (timeout_count >= TIMEOUT_VALUE) begin
          `uvm_error(`gfn, "Timed out waiting for ec_rst to go high.")
        end
      end else begin
        break;
      end
      // Some amount of delay between samples of ec_rst.
      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  virtual task check_ec_rst_when_rstreq_low();
    bit retval = 0;
    int timeout_count = 0;
    forever begin
      `DV_CHECK(uvm_hdl_read(PWRMGR_RSTREQ_PATH, retval));
      if (retval == 0) begin
        timeout_count++;
        if (timeout_count >= TIMEOUT_VALUE) begin
          `uvm_error(`gfn, "Timed out waiting for pwrmgr reset request to go high.")
        end
      end else begin
        break;
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
    // Check that ec_rst is low.
    cfg.clk_rst_vif.wait_clks(1);
    `DV_CHECK(uvm_hdl_read(PAD_ECRST_PATH, retval));
    if (retval == 1) begin
      `uvm_error(`gfn, "Unexpected ec_rst high after reset request.")
    end
  endtask

  virtual task check_ec_rst_when_aon_rst_low();
    bit retval = 0;
    int timeout_count = 0;
    forever begin
      `DV_CHECK(uvm_hdl_read(RST_AON_NI_PATH, retval));
      if (retval == 1) begin
        timeout_count++;
        if (timeout_count >= TIMEOUT_VALUE) begin
          `uvm_error(`gfn, "Timed out waiting for aon reset to go low.")
        end
      end else begin
        break;
      end
      cfg.clk_rst_vif.wait_clks(1);
    end
    // Check that ec_rst is low.
    cfg.clk_rst_vif.wait_clks(1);
    `DV_CHECK(uvm_hdl_read(PAD_ECRST_PATH, retval));
    if (retval == 1) begin
      `uvm_error(`gfn, "Unexpected ec_rst high after aon reset.")
    end
  endtask

  virtual task check_flash_wp_value(input bit level_to_check);
    bit retval = 0;
    `DV_CHECK(uvm_hdl_read(PAD_FLASHWP_PATH, retval));
    if (retval != level_to_check) begin
      `uvm_error(`gfn, $sformatf("Flash write protect signal expected %0d.", level_to_check))
    end
  endtask

  virtual task write_test_phase(input int phase);
    bit [7:0] test_phase[1];
    test_phase[0] = phase;
    sw_symbol_backdoor_overwrite("kTestPhase", test_phase);
  endtask

  virtual task cpu_init();
    super.cpu_init();
    set_all_pads_high();
    write_test_phase(COMBO_RESET_PHASE);
  endtask

  virtual task body();
    super.body();

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    check_flash_wp_value(1);
    wait_for_ec_rst_high();
    set_combo0_pads_low();
    check_ec_rst_when_rstreq_low();
    check_ec_rst_when_aon_rst_low();
    check_flash_wp_value(0);

    write_test_phase(DEEP_SLEEP_WAKEUP_PHASE);
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)
    set_ulp_pads_deassert();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    set_ulp_pads_assert();

    write_test_phase(DEEP_SLEEP_RESET_PHASE);
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRom)
    set_all_pads_high();
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    check_flash_wp_value(1);
    set_combo1_pads_low();
    check_ec_rst_when_rstreq_low();
    check_ec_rst_when_aon_rst_low();
    check_flash_wp_value(0);

    write_test_phase(FINAL_CHECK_PHASE);

  endtask

endclass
