// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_spi_device_pinmux_sleep_retention_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_spi_device_pinmux_sleep_retention_vseq)
  `uvm_object_new

  virtual task pre_start();
    disconnect_sw_straps_if = 0;
    `uvm_info(`gfn, "Unsetting 'disconnect_sw_straps_if' to avoid Zs in IOC0/1/2", UVM_DEBUG)
    super.pre_start();
  endtask

  virtual task body();
    int test_payload_size = 2048;
    bit [7:0] test_opcode = SpiFlashReadQuad;
    spi_flash_cmd_info info = spi_flash_cmd_info::type_id::create("info");
    spi_host_flash_seq m_spi_host_seq;
    super.body();
    // This VSEQ works in conjunction with the SW test spi_device_sleep_test.c
    m_spi_host_seq = spi_host_flash_seq::type_id::create("m_spi_host_seq");

    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    cfg.chip_vif.spi_host_if.disconnected = 1;

    // SW uses IOA7=0 to indicate chip is sleeping
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Setting SPI_DIO1 to high when sleeping")
    // Notifies the SW to go into sleep mode
    cfg.chip_vif.mios_if.drive_pin(top_earlgrey_pkg::MioPadIoa8, 1);

    `DV_WAIT((cfg.chip_vif.pwrmgr_low_power || cfg.chip_vif.pwrmgr_low_power_if.in_sleep));
    @(cfg.chip_vif.pwrmgr_low_power_if.cb);
    #(20000 * 1ns);
    // Notifies pinmux to wake-up
    cfg.chip_vif.mios_if.drive_pin(top_earlgrey_pkg::MioPadIoa8, 0);


    `DV_WAIT(cfg.sw_logger_vif.printed_log == "SYNC: Sleeping")

    // Check chip is sleeping after IOA7 is set low
    `DV_WAIT(cfg.chip_vif.mios_if.sample_pin(top_earlgrey_pkg::MioPadIoa7) == 0)

    // Check the values are 1s
    check_spi_outputs(1);

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "SYNC: Awaked")

    // Same as above but with all outputs to 0s
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Setting SPI_DIO1 to low when sleeping")
    // Request chip to sleep via assertion IOA8
    cfg.chip_vif.mios_if.drive_pin(top_earlgrey_pkg::MioPadIoa8, 1);

    `DV_WAIT((cfg.chip_vif.pwrmgr_low_power || cfg.chip_vif.pwrmgr_low_power_if.in_sleep));
    @(cfg.chip_vif.pwrmgr_low_power_if.cb);
    #(20000 * 1ns);

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "SYNC: Sleeping")

    // Check chip is sleeping after IOA7 is set low
    `DV_WAIT(cfg.chip_vif.mios_if.sample_pin(top_earlgrey_pkg::MioPadIoa7) == 0)

    // Check the values are 0s
    check_spi_outputs(0);

    // Enabling the interface via `chip_vif` function
    cfg.chip_vif.enable_spi_device(.inst_num(0), .enable(1));

    // The following resolves Xs due to multiple IFs driving the same signal
    cfg.chip_vif.dios_if.set_pullup_en_pin(top_earlgrey_pkg::DioPadSpiHostCsL, 1);
    cfg.chip_vif.dios_if.set_pulldown_en_pin(top_earlgrey_pkg::DioPadSpiDevD0, 1);
    cfg.chip_vif.dios_if.set_pulldown_en_pin(top_earlgrey_pkg::DioPadSpiDevD1, 1);
    cfg.chip_vif.dios_if.set_pulldown_en_pin(top_earlgrey_pkg::DioPadSpiDevD2, 1);
    cfg.chip_vif.dios_if.set_pulldown_en_pin(top_earlgrey_pkg::DioPadSpiDevD3, 1);
    // Resolves firing assertion due to Xs
    cfg.chip_vif.mios_if.set_pulldown_en_pin(top_earlgrey_pkg::MioPadIob4, 1);
    cfg.chip_vif.mios_if.set_pulldown_en_pin(top_earlgrey_pkg::MioPadIob2, 1);

    cfg.clk_rst_vif.wait_clks(50);
    // Request chip to wakeup via deassertion of IOA8
    cfg.chip_vif.mios_if.drive_pin(top_earlgrey_pkg::MioPadIoa8, 0);

    // Pinmux then configurded to go to sleep ic CSB changes
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "SYNC: Awaked")

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "SYNC: Flash mode")
    // Send the chip to sleep
    cfg.chip_vif.mios_if.drive_pin(top_earlgrey_pkg::MioPadIoa8, 1);


    `DV_WAIT(cfg.sw_logger_vif.printed_log == "SYNC: Sleeping")
    // Pinmux is now configured so IOA8 doesn't wake up the chip, so we unset it here to
    // Test chip wakes up upon sending a spi_txn (CSB getting set to 0x0)
    cfg.chip_vif.mios_if.drive_pin(top_earlgrey_pkg::MioPadIoa8, 0);

    cfg.clk_rst_vif.wait_clks(5000);

    `uvm_info(`gfn, "Starting 'm_spi_host_seq' on 'spi_device_sequencer_hs[0]'", UVM_DEBUG)
    m_spi_host_seq.opcode = test_opcode;
    if(!std::randomize(test_payload_size) with {
      test_payload_size inside {128, 256, 512, 1024, 2048};
      }) `uvm_fatal(`gfn, "Randomization Failure")
    m_spi_host_seq.read_size = test_payload_size;
    cfg.chip_vif.spi_host_if.disconnect(0);

    // Configuring info slot in agent to ensure the size and direction of the command
    // are generated correctly
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode != SpiFlashAddrDisabled &&
      info.opcode == test_opcode &&
      info.write_command == 0 &&
      info.num_lanes == 4;)
    cfg.m_spi_host_agent_cfg.add_cmd_info(info);

    // Fork--join_none to ensure we don't block here for the entire sequence execution
    // otherwise, we may miss the following DV_WAIT
    fork begin
      m_spi_host_seq.start(p_sequencer.spi_host_sequencer_h);
      cfg.chip_vif.spi_host_if.disconnect(1);
    end join_none

    `DV_WAIT(cfg.sw_logger_vif.printed_log == "PASS!")

    // Check spi transactions work as they should after devide is awoken
  endtask : body

  // Checks the spi_output are set to value
  function void check_spi_outputs(bit value);
    `DV_CHECK_EQ_FATAL(cfg.chip_vif.dios_if.sample_pin(top_earlgrey_pkg::DioPadSpiDevD3), value,
      $sformatf("DioPadSpiDevD3 not %0d",value))
    `DV_CHECK_EQ_FATAL(cfg.chip_vif.dios_if.sample_pin(top_earlgrey_pkg::DioPadSpiDevD2), value,
      $sformatf("DioPadSpiDevD2 not %0d",value))
    `DV_CHECK_EQ_FATAL(cfg.chip_vif.dios_if.sample_pin(top_earlgrey_pkg::DioPadSpiDevD1), value,
      $sformatf("DioPadSpiDevD1 not %0d",value))
    `DV_CHECK_EQ_FATAL(cfg.chip_vif.dios_if.sample_pin(top_earlgrey_pkg::DioPadSpiDevD0), value,
      $sformatf("DioPadSpiDevD0 not %0d",value))
  endfunction

endclass : chip_sw_spi_device_pinmux_sleep_retention_vseq
