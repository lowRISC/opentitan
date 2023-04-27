// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_sleep_pin_mio_dio_val_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_sleep_pin_mio_dio_val_vseq)
  `uvm_object_new

  typedef enum bit [2:0] {
    Ret0,   // PAD driving 0 while in retention
    Ret1,   // PAD driving 1 while in retention
    HighZ,  // PAD is input mode while in retention
    RetP,   // PAD keeps the prev. value while in retention
    RetSkip // Skip the test
  } pad_ret_t;

  pad_ret_t [top_earlgrey_pkg::MioPadCount-1:0] mio_pad_ret;
  pad_ret_t [top_earlgrey_pkg::DioCount-1:0]    dio_pad_ret;

  // Fetch the pad and retention type under test.
  //
  // The SW test randomizes and writes the pad type, the pad number and the type of the retention
  // being tested in the following format:
  //   {M/D}IO [pad_num]: {0,1,2}
  //
  // For example, "MIO [14]: 2" indicates the MIO 14 will be configured as High-Z mode in deep
  // powerdown.

  // These are written to the log device (sw_logger_if). This task monitors the log events in
  // sw_logger_if and retrieves this information and stores it into d|mio_pad_ret variables.
  //
  // These transfers are wrapped between the logs "BEGIN Chosen Retention Types" and "END Chosen
  // Retention Types", which are trigger events.
  task receive_chosen_values();
    localparam string StartEvent = "BEGIN Chosen Retention Types";
    localparam string EndEvent = "END Chosen Retention Types";

    `DV_WAIT(string'(cfg.sw_logger_vif.printed_log) == StartEvent)
    forever begin
      string printed_log;

      @(cfg.sw_logger_vif.printed_log_event);
      printed_log = string'(cfg.sw_logger_vif.printed_log);

      if (printed_log == EndEvent) break;

      case (printed_log.substr(0, 4))
        "DIO [": begin
          int idx = cfg.sw_logger_vif.printed_arg[0];
          pad_ret_t pad_ret_type = pad_ret_t'(cfg.sw_logger_vif.printed_arg[1]);
          `DV_CHECK(cfg.sw_logger_vif.printed_arg[1] inside {[0:3]})
          dio_pad_ret[idx] = pad_ret_type;
        end
        "MIO [": begin
          int idx = cfg.sw_logger_vif.printed_arg[0];
          pad_ret_t pad_ret_type = pad_ret_t'(cfg.sw_logger_vif.printed_arg[1]);
          `DV_CHECK(cfg.sw_logger_vif.printed_arg[1] inside {[0:3]});
          mio_pad_ret[idx] = pad_ret_type;
        end
        default: begin
          `uvm_info(`gfn, $sformatf("Unexpected SW log: %s",
                                    cfg.sw_logger_vif.printed_log), UVM_LOW)
        end
      endcase
    end

    // Log the chosen pad retention tests.
    begin
      string msg = {"\n", StartEvent, "\n"};
      foreach (dio_pad_ret[i]) msg = {msg, $sformatf("  DIO [%d]: %d\n", i, dio_pad_ret[i])};
      foreach (mio_pad_ret[i]) msg = {msg, $sformatf("  MIO [%d]: %d\n", i, mio_pad_ret[i])};
      msg = {msg, EndEvent, "\n"};
      `uvm_info(`gfn, msg, UVM_LOW)
    end
  endtask : receive_chosen_values

  // Checks the retention values of all eligible MIO and DIO pads.
  //
  // The eligibility for check is determined by the members mio_pad_ret and dio_pad_ret fetched from
  // the SW test.
  function void check_pad_retention_out();
    for (int i = 0; i < top_earlgrey_pkg::MioPadCount; i++) begin
      string msg = $sformatf("for MIO[%0d]", i);

      case (mio_pad_ret[i])
        Ret0: `DV_CHECK_CASE_EQ(cfg.chip_vif.mios_if.pins[i], 1'b0, msg)
        Ret1: `DV_CHECK_CASE_EQ(cfg.chip_vif.mios_if.pins[i], 1'b1, msg)
        HighZ: begin
          logic exp = 1'bz;
          if (cfg.chip_vif.mios_if.pins_pd[i]) exp = 0;
          if (cfg.chip_vif.mios_if.pins_pu[i]) exp = 1;
          `DV_CHECK_CASE_EQ(cfg.chip_vif.mios_if.pins[i], exp, msg)
        end
        RetP, RetSkip: ;
        default: `uvm_fatal(`gfn, "Invalid choice!")
      endcase
    end

    for (int i = 0; i < top_earlgrey_pkg::DioCount; i++) begin
      string msg = $sformatf("for DIO[%0d]", i);
      // Note that dios_if enumerates the DIOs in chip_earlgrey_asic, which is different from the
      // DIOs enumerated in pinmux. The former is provided by top_earlgrey_pkg::dio_pad_e and the
      // latter, by top_earlgrey_pkg::dio_e. The chip_common_pkg::DioToDioPadMap maps the pinmux's
      // enumeration to the chip level's enumeration.
      int mapped_idx = DioToDioPadMap[i];

      case (dio_pad_ret[i])
        Ret0: `DV_CHECK_CASE_EQ(cfg.chip_vif.dios_if.pins[mapped_idx], 1'b0, msg)
        Ret1: `DV_CHECK_CASE_EQ(cfg.chip_vif.dios_if.pins[mapped_idx], 1'b1, msg)
        HighZ: begin
          logic exp = 1'bz;
          if (cfg.chip_vif.dios_if.pins_pd[mapped_idx]) exp = 0;
          if (cfg.chip_vif.dios_if.pins_pu[mapped_idx]) exp = 1;
          `DV_CHECK_CASE_EQ(cfg.chip_vif.dios_if.pins[mapped_idx], exp, msg)
        end
        RetP, RetSkip: ;
        default: `uvm_fatal(`gfn, "Invalid choice!")
      endcase
    end
  endfunction : check_pad_retention_out

  task check_pads_retention_type();
    logic [top_earlgrey_pkg::MioPadCount-1:0] mio_pads;
    logic [top_earlgrey_pkg::DioCount-1:0]    dio_pads;

    // How to check 0, 1, High-Z
    //
    // For 0, 1, DUT drives the PADs. First, let ENV high-Z any PADs interface
    // and capture. The signal should match with the config. Then, repeat with
    // Pull-down mode, then Pull-up mode. The values should same in all cases.
    //
    // For High-Z, DUT is in input mode. In this case, the PAD attributes may
    // affect the signal. To confirm, ENV drives 0 and samples, then drives
    // 1 and samples. In each case, the sampled value should match to the
    // driving value not X or other values.

    // High-Z for all ports
    `uvm_info(`gfn, "Testing Retention Outputs with no pulls", UVM_LOW)
    cfg.chip_vif.dios_if.pins_pd = '0;
    cfg.chip_vif.dios_if.pins_pu = '0;
    cfg.chip_vif.mios_if.pins_pd = '0;
    cfg.chip_vif.mios_if.pins_pu = '0;
    @(cfg.chip_vif.pwrmgr_low_power_if.cb);
    check_pad_retention_out();

    // Pull-down then check
    `uvm_info(`gfn, "Testing Retention Outputs with Pull-down", UVM_LOW)
    cfg.chip_vif.dios_if.pins_pd = '1;
    cfg.chip_vif.dios_if.pins_pu = '0;
    cfg.chip_vif.mios_if.pins_pd = '1;
    cfg.chip_vif.mios_if.pins_pu = '0;
    @(cfg.chip_vif.pwrmgr_low_power_if.cb);
    check_pad_retention_out();

    // Pull-up then check
    `uvm_info(`gfn, "Testing Retention Outputs with Pull-up", UVM_LOW)
    cfg.chip_vif.dios_if.pins_pd = '0;
    cfg.chip_vif.dios_if.pins_pu = '1;
    cfg.chip_vif.mios_if.pins_pd = '0;
    cfg.chip_vif.mios_if.pins_pu = '1;
    @(cfg.chip_vif.pwrmgr_low_power_if.cb);
    check_pad_retention_out();
  endtask : check_pads_retention_type

  virtual task body();
    super.body();

    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    // TODO: Get expected MIO DIO value from SW
    receive_chosen_values();

    // Wait until Chip enters Low Power Mode
    wait (cfg.chip_vif.pwrmgr_low_power_if.in_sleep);
    @(cfg.chip_vif.pwrmgr_low_power_if.cb);

    // Release any driver interfaces.
    cfg.chip_vif.disconnect_all_interfaces(.disconnect_default_pulls(0));

    // The SW test randomizes between deep and light sleep. The SW test also randomizes the
    // retention values of DIOs during sleep. If the SW ends up picking up the CLK or CSB ports of
    // the SPI peripherals (that have dedicated pads) for example, then setting the values
    // ends up triggering unexpected SVA errors. So we disable SVAs in those peripherals for this
    // test. It may also be an artifact of having external weak pulls on DIOs. TODO: revisit this
    // once we eliminate all weak pulls on all IOs (in chip_if.sv).
    // TODO: deassert the below bit to reenable SVAs once we are back in active power.
    cfg.chip_vif.chip_sw_sleep_pin_mio_dio_val_sva_disable = 1;

    @(cfg.chip_vif.pwrmgr_low_power_if.cb);

    `uvm_info(`gfn, "Chip Entered Deep Powerdown mode.", UVM_LOW)

    check_pads_retention_type();

    // If `chech_pad_retention_type()` runs without uvm_error and reach this point, the test passed
    // full check
    // TODO: Cleanly exit the test with idle CPU.
    override_test_status_and_finish(.passed(1'b 1));

  endtask : body

endclass : chip_sw_sleep_pin_mio_dio_val_vseq
