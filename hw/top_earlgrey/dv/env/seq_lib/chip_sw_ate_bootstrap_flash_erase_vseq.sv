// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test performs a the first step of a ROM bootstrap operation, i.e.,
// flash erase. It them confirms flash has been erased by reading back a few
// SPI flash frames to check they are all 1s (which matches the erased state).

class chip_sw_ate_bootstrap_flash_erase_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_ate_bootstrap_flash_erase_vseq)
  `uvm_object_new

  local function automatic void _check_flash_data_page(input integer address,
                                                       input integer expected);
    logic [TL_DW-1:0] actual;
    actual = cfg.mem_bkdr_util_h[FlashBank0Data].read32(address);
    `DV_CHECK_EQ(actual, expected)
  endfunction

  virtual task body();
    spi_host_flash_seq m_spi_host_seq;

    super.body();

    // Drive SW straps for bootstrap.
    `uvm_info(`gfn, "Driving SW straps high for bootstrap.", UVM_LOW)
    cfg.chip_vif.sw_straps_if.drive(3'h7);

    // Set CSB inactive times to reasonable values. sys_clk is at 24 MHz, and
    // it needs to capture CSB pulses.
    cfg.m_spi_host_agent_cfg.min_idle_ns_after_csb_drop = 50;
    cfg.m_spi_host_agent_cfg.max_idle_ns_after_csb_drop = 200;

    // Configure the spi_agent for flash mode and add command info.
    `uvm_info(`gfn, "Configuring SPI flash commands.", UVM_LOW)
    spi_agent_configure_flash_cmds(cfg.m_spi_host_agent_cfg);

    // Wait for the SPI flash commands to be configured by the (test) ROM.
    `uvm_info(`gfn, "Waiting for SPI flash cmds on device to load ...", UVM_LOW)
    csr_spinwait(
      .ptr(ral.spi_device.cmd_info[spi_device_pkg::CmdInfoReadSfdp].opcode),
      .exp_data(SpiFlashReadSfdp),
      .backdoor(1),
      .spinwait_delay_ns(5000));
    csr_spinwait(
      .ptr(ral.spi_device.cmd_info[spi_device_pkg::CmdInfoReadStatus1].opcode),
      .exp_data(SpiFlashReadSts1),
      .backdoor(1),
      .spinwait_delay_ns(5000));
    csr_spinwait(
      .ptr(ral.spi_device.cmd_info_wren.opcode),
      .exp_data(SpiFlashWriteEnable),
      .backdoor(1),
      .spinwait_delay_ns(5000));

    // Send the SPI flash erase command.
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h)
    m_spi_host_seq.opcode = SpiFlashChipErase;
    `uvm_info(`gfn, "Sending SPI flash erase command ...", UVM_LOW)
    spi_host_flash_issue_write_cmd(
      .write_command(m_spi_host_seq),
      .busy_timeout_ns(50_000_000),
      .busy_poll_interval_ns(2_000_000));
    `uvm_info(`gfn, "Done.", UVM_LOW)

    // Read first flash data word to confirm they are erased.
    _check_flash_data_page('h0, 32'hFFFF_FFFF);
    `uvm_info(`gfn, "SPI flash erase done.", UVM_LOW)

    // Set test passed.
    cfg.chip_vif.sw_straps_if.drive(3'h0);
    assert_por_reset();
    override_test_status_and_finish(.passed(1'b1));
  endtask

endclass : chip_sw_ate_bootstrap_flash_erase_vseq
