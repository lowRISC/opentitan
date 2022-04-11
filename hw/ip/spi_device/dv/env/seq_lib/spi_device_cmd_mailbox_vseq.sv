// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Mailbox test scenario
class spi_device_cmd_mailbox_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_cmd_mailbox_vseq)
  `uvm_object_new

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [7:0]  cmd;
    bit [23:0] addr;
    bit [4:0]  cmd_info_idx;
    bit [31:0] address_command;
    bit [31:0] mailbox_payload[$];
    bit [23:0] host_mbox_addr;
    bit [2:0]  lanes_en;
    spi_device_flash_pass_init(FlashMode);
    ral.cfg.mailbox_en.set(1);
    csr_update(.csr(ral.cfg));

    cfg.clk_rst_vif.wait_clks(100);

    repeat (num_trans) begin

      // Randomize opcode and address
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(lanes_en, lanes_en inside {1, 2, 4};)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mailbox_payload, mailbox_payload.size() == 256;)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cmd_info_idx, cmd_info_idx > 4; cmd_info_idx < 11;)
      // Initialize Mailbox Space
      for (int i = 0; i < 256; i=i+1) begin
        mem_wr(.ptr(ral.buffer), .offset(MAILBOX_OFFSET_ADDR+i), .data(mailbox_payload[i]));
      end

      // Configure read command CMD_INFO and enable this opcode
      cmd = READ_NORMAL; // Normal Read
      ral.cmd_info[cmd_info_idx].valid.set(1'b1); // Enable this OPCODE
      ral.cmd_info[cmd_info_idx].payload_dir.set(PayloadOut);
      ral.cmd_info[cmd_info_idx].opcode.set(cmd);
      ral.cmd_info[cmd_info_idx].addr_mode.set(Addr3B); //  3B address for this scenario
      ral.cmd_info[cmd_info_idx].payload_en.set(2 ** lanes_en - 1);
      csr_update(.csr(ral.cmd_info[cmd_info_idx]));
      // Configure host address for mailbox
      host_mbox_addr = {addr[7:0], addr[15:8], addr[23:16]};
      ral.mailbox_addr.addr.set(host_mbox_addr);
      csr_update(.csr(ral.mailbox_addr));

      // Issue read command targeting mailbox space
      spi_host_xfer_cmd_out(cmd, {addr[7:0], addr[15:8], addr[23:16]},
                                       mailbox_payload.size(), lanes_en);

      cfg.clk_rst_vif.wait_clks(100);

    end

  endtask : body

endclass : spi_device_cmd_mailbox_vseq
