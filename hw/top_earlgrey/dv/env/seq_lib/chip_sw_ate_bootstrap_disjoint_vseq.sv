// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test performs a the first two steps of a ROM bootstrap operation, i.e.,
// flash erase followed by a single page program operation. It them confirms
// flash has been programmed by backdoor reading back the first data page.

class chip_sw_ate_bootstrap_disjoint_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_ate_bootstrap_disjoint_vseq)
  `uvm_object_new

  local function automatic void _check_flash_data_page(input integer address,
                                                       input integer expected);
    logic [TL_DW-1:0] actual;
    actual = cfg.mem_bkdr_util_h[FlashBank0Data].read32(address);
    `DV_CHECK_EQ(actual, expected)
  endfunction

  virtual task body();
    spi_host_flash_seq m_spi_host_seq;
    bit skip_page = 0;
    byte sw_byte_q[$];
    uint bytes_to_write;
    uint byte_cnt = 0;
    uint page_cnt = 0;
    uint SPI_FLASH_PAGE_SIZE = 256;

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

    `uvm_info(`gfn, "Reading SW image frames ...", UVM_LOW)
    `uvm_info(`gfn, $sformatf("SW Image : %0s\n",
      {cfg.sw_images[SwTypeTestSlotA], ".64.vmem"}), UVM_LOW);
    read_sw_frames({cfg.sw_images[SwTypeTestSlotA], ".64.vmem"}, sw_byte_q);
    `uvm_info(`gfn, "Done.", UVM_LOW)

    // Send the SPI flash erase command.
    `uvm_info(`gfn, "Sending SPI flash erase command ...", UVM_LOW)
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h)
    m_spi_host_seq.opcode = SpiFlashChipErase;
    spi_host_flash_issue_write_cmd(
      .write_command(m_spi_host_seq),
      .busy_timeout_ns(50_000_000),
      .busy_poll_interval_ns(2_000_000));
    `uvm_info(`gfn, "Done.", UVM_LOW)

    // Send the SPI flash page program commands.
    `uvm_info(`gfn, "Sending SPI flash page program commands ...", UVM_LOW)
    while (sw_byte_q.size > byte_cnt) begin
      `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h)
      m_spi_host_seq.opcode = SpiFlashPageProgram;
      m_spi_host_seq.address_q = {byte_cnt[23:16], byte_cnt[15:8], byte_cnt[7:0]};
      if (SPI_FLASH_PAGE_SIZE < (sw_byte_q.size() - byte_cnt)) begin
        bytes_to_write = SPI_FLASH_PAGE_SIZE;
      end else begin
        bytes_to_write = sw_byte_q.size() - byte_cnt;
      end
      // Skip page programs for pages that are all 0xFF (i.e., empty).
      skip_page = 1;
      for (int i = 0; i < bytes_to_write; i++) begin
        skip_page &= sw_byte_q[byte_cnt + 1] == 8'hFF;
      end
      if (!skip_page) begin
        for (int i = 0; i < bytes_to_write; i++) begin
          m_spi_host_seq.payload_q.push_back(sw_byte_q[byte_cnt + i]);
        end
        spi_host_flash_issue_write_cmd(m_spi_host_seq);
        `uvm_info(`gfn, $sformatf("Writing page %d ...\n", page_cnt), UVM_LOW);
      end
      byte_cnt += bytes_to_write;
      page_cnt += 1;
    end
    `uvm_info(`gfn, "Done.", UVM_LOW)

    // Read back the programmed flash data page to confirm it has been
    // programmed correctly.
    `uvm_info(`gfn, "Checking page program succeeded ...\n", UVM_LOW);
    for (int a = 0; a < (sw_byte_q.size - 4); a += 4) begin
      logic [TL_DW-1:0] expected_word = {sw_byte_q[a + 3], sw_byte_q[a + 2],
                                         sw_byte_q[a + 1], sw_byte_q[a + 0]};
      `uvm_info(`gfn, $sformatf("  Checking SW image word at address %08x: %08x ...\n",
        a, expected_word), UVM_LOW);
      _check_flash_data_page(a, expected_word);
    end
    `uvm_info(`gfn, "Done.", UVM_LOW)

    // Set test passed.
    cfg.chip_vif.sw_straps_if.drive(3'h0);
    assert_por_reset();
    override_test_status_and_finish(.passed(1'b1));
  endtask

endclass : chip_sw_ate_bootstrap_disjoint_vseq
