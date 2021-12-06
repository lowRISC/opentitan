// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TPM Write Test
class spi_device_tpm_write_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_write_vseq)
  `uvm_object_new

  virtual task body();
    bit [4:0]  tpm_status;
    bit [31:0] device_word_rsp;
    bit [7:0]  device_byte_rsp;
    bit [7:0]  tpm_cmd = 8'hC0; //Write command with 4 bytes payload
    bit [23:0] tpm_addr;
    bit [31:0] address_command;
    byte data_bytes[$];
    int pay_num = 0;
    bit [31:0]  wrfifo_data;

    spi_device_init();

    // randomised tpm configuration.
    tpm_init();
    tpm_configure();

    cfg.clk_rst_vif.wait_clks(100);

    // send cmd_addr
    `DV_CHECK_STD_RANDOMIZE_FATAL(tpm_addr)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_bytes, data_bytes.size() == 5;)
    address_command = {tpm_addr,tpm_cmd};
    `uvm_info(`gfn, $sformatf("Address Command = 0x%0h", address_command), UVM_LOW)
    // send payload
    cfg.m_spi_agent_cfg.consecutive = 1;
    spi_host_xfer_word(address_command, device_word_rsp);
    while (pay_num < 5) begin
      spi_host_xfer_byte(data_bytes[pay_num], device_byte_rsp);
      `uvm_info(`gfn, $sformatf("Device Resp = 0x%0h", device_byte_rsp), UVM_LOW)
      if (pay_num > 0) pay_num++;
      if (pay_num == 0  && device_byte_rsp == 8'h1) pay_num++;
      if (pay_num == 4) cfg.m_spi_agent_cfg.consecutive = 0;
    end

    chk_fifo_contents(address_command, data_bytes);

  endtask : body

endclass : spi_device_tpm_write_vseq