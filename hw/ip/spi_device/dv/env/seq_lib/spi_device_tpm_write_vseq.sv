// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TPM Write Test, issuing Address and Command, issuing payload, checking relevant FIFOs content
class spi_device_tpm_write_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_write_vseq)
  `uvm_object_new

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [7:0]  device_byte_rsp;
    bit [7:0]  tpm_cmd = TPM_WRITE_CMD; //Write command with 4 bytes payload
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
    // Data size will be 5, first byte dummy for polling, remaining 4 for payload
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(data_bytes, data_bytes.size() == 5;)
    address_command = {tpm_addr, tpm_cmd};
    `uvm_info(`gfn, $sformatf("Address Command = 0x%0h", address_command), UVM_LOW)
    // send payload
    cfg.spi_host_agent_cfg.csb_consecutive = 1;
    spi_host_xfer_word(address_command, device_word_rsp);
    fork
      wait_and_check_tpm_cmd_addr(tpm_cmd, tpm_addr);
      begin
        `DV_SPINWAIT(
          while (pay_num < 5) begin
            spi_host_xfer_byte(data_bytes[pay_num], device_byte_rsp);
            `uvm_info(`gfn, $sformatf("Device Resp = 0x%0h", device_byte_rsp), UVM_LOW)
            if (pay_num > 0) pay_num++;
            if (pay_num == 0  && device_byte_rsp == TPM_START) pay_num++;
            if (pay_num == 4) cfg.spi_host_agent_cfg.csb_consecutive = 0;
          end
        )
        check_tpm_write_fifo(data_bytes);
      end
    join
  endtask : body

endclass : spi_device_tpm_write_vseq
