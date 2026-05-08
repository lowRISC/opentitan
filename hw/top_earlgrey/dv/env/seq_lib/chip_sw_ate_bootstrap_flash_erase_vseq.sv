// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test performs a the first step of a ROM bootstrap operation, i.e., flash erase. It then
// confirms flash has been erased by reading back a few SPI flash frames to check they are all 1s
// (which matches the erased state).

class chip_sw_ate_bootstrap_flash_erase_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_ate_bootstrap_flash_erase_vseq)

  function new (string name="");
    super.new(name);
  endfunction

  local function automatic void _check_flash_data_page(input int unsigned address,
                                                       input bit [31:0]   expected);
    logic [TL_DW-1:0] actual;
    actual = cfg.mem_bkdr_util_h[FlashBank0Data].read32(address);
    `DV_CHECK_EQ(actual, expected)
  endfunction

  virtual task body();
    spi_host_flash_seq m_spi_host_seq;

    super.body();

    // Drive SW straps for bootstrap.
    `uvm_info(get_name(), "Driving SW straps high for bootstrap.", UVM_LOW)
    cfg.chip_vif.sw_straps_if.drive(3'h7);

    // Set CSB inactive times to reasonable values. sys_clk is at 24 MHz, and
    // it needs to capture CSB pulses.
    cfg.m_spi_host_agent_cfg.min_idle_ns_after_csb_drop = 50;
    cfg.m_spi_host_agent_cfg.max_idle_ns_after_csb_drop = 200;

    // Configure the spi_agent for flash mode and add command info.
    `uvm_info(get_name(), "Configuring SPI flash commands", UVM_LOW)
    spi_agent_configure_flash_cmds(cfg.m_spi_host_agent_cfg);

    // Wait for the SPI flash commands to be configured by the (test) ROM.
    `uvm_info(get_name(), "Waiting for SPI flash cmds on device to load", UVM_LOW)
    wait_for_flash_command_load();

    `uvm_info(get_name(), "Sending SPI flash erase command", UVM_LOW)
    erase_flash_over_spi();

    // Read first flash data word to confirm they are erased.
    `uvm_info(get_name(), "Checking the first data word was erased", UVM_LOW)
    _check_flash_data_page('h0, 32'hFFFF_FFFF);

    // Set test passed.
    cfg.chip_vif.sw_straps_if.drive(3'h0);
    assert_por_reset();
    override_test_status_and_finish(.passed(1'b1));
  endtask
endclass
