// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Random config of cmd info slots 11 to 23, random commands issued
class spi_device_pass_cmd_info_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_pass_cmd_info_vseq)
  `uvm_object_new

  // Randomize all custom CMD_INFO slots
  virtual task cmd_info_randomize();
    bit [7:0] opcode[$];
    opcode = {READ_STATUS_1, READ_STATUS_2, READ_STATUS_3, READ_JEDEC, READ_SFDP, READ_NORMAL,
              READ_FAST, READ_DUAL, READ_QUAD, READ_DUALIO, READ_QUADIO};
    for (int i = 0; i < 24; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.cmd_info[i])
      if (i < 11) begin
        ral.cmd_info[i].opcode.set(opcode[i]);
        ral.cmd_info[i].payload_dir.set(PayloadOut); // Read commands 0 - 11
      end
      csr_update(.csr(ral.cmd_info[i]));
    end
  endtask : cmd_info_randomize

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [7:0]  pass_cmd;
    bit [23:0] pass_addr;
    bit [31:0] address_command;
    bit [31:0] payload;
    fork
      start_reactive_seq();
    join_none
    spi_device_flash_pass_init(PassthroughMode);
    cmd_info_randomize();

    cfg.clk_rst_vif.wait_clks(100);

    repeat (100) begin

      // Randomize opcode and address
      `DV_CHECK_STD_RANDOMIZE_FATAL(pass_addr)
      `DV_CHECK_STD_RANDOMIZE_FATAL(pass_cmd)
      `DV_CHECK_STD_RANDOMIZE_FATAL(payload)

      // Transfer data without payload swap enabled
      order_cmd_bits(pass_cmd, pass_addr, address_command);
      spi_host_xfer_word(address_command, device_word_rsp);
      // Transfer Payload
      spi_host_xfer_word(payload, device_word_rsp);

      cfg.clk_rst_vif.wait_clks(100);

    end

  endtask : body

endclass : spi_device_pass_cmd_info_vseq
