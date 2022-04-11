// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Command upload test scenario
class spi_device_cmd_upload_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_cmd_upload_vseq)
  `uvm_object_new

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [7:0]  cmd;
    bit [23:0] addr;
    bit [31:0] address_command;
    bit [4:0]  cmd_info_idx;
    bit [31:0] upload_payload[$];
    bit [31:0] host_word;
    bit [7:0] up_cmd;
    bit [23:0] up_addr;
    bit [31:0] act_payload[$];
    bit status_bit;
    bit [8:0] status_depth;
    bit set_upload_busy;
    spi_device_flash_pass_init(FlashMode);

    cfg.clk_rst_vif.wait_clks(100);

    repeat (num_trans) begin

      // Randomize opcode and address
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr)
      `DV_CHECK_STD_RANDOMIZE_FATAL(cmd)
      `DV_CHECK_STD_RANDOMIZE_FATAL(set_upload_busy)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cmd_info_idx, cmd_info_idx > 10; cmd_info_idx < 24;)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(upload_payload, upload_payload.size() < 64;
                                           upload_payload.size()%4 == 0;)

      // Configure unused CMD_INFO and enable this opcode
      ral.cmd_info[cmd_info_idx].valid.set(1'b1); // Enable this OPCODE
      ral.cmd_info[cmd_info_idx].upload.set(1'b1); // Enable upload
      ral.cmd_info[cmd_info_idx].busy.set(set_upload_busy); // Set if busy enabled
      ral.cmd_info[cmd_info_idx].payload_dir.set(PayloadIn);
      ral.cmd_info[cmd_info_idx].opcode.set(cmd);
      ral.cmd_info[cmd_info_idx].addr_mode.set(Addr3B); //  3B address for this scenario
      csr_update(.csr(ral.cmd_info[cmd_info_idx]));

      cfg.spi_device_agent_cfg.csb_consecutive = 1;
      // Transfer upload command plus payload
      order_cmd_bits(cmd, addr, address_command);
      spi_host_xfer_word(address_command, device_word_rsp);
      for (int i = 0; i < upload_payload.size(); i=i+1) begin
        if (i == upload_payload.size() - 1) begin // Last data - deassert CSB
          cfg.spi_device_agent_cfg.csb_consecutive = 0;
        end
        host_word = upload_payload[i];
        spi_host_xfer_word(host_word, device_word_rsp);
      end
      csr_rd(.ptr(ral.upload_status.cmdfifo_notempty), .value(status_bit));
      `DV_CHECK_CASE_EQ(status_bit, 1) // Check cmd fifo not empty status
      csr_rd(.ptr(ral.upload_status.addrfifo_notempty), .value(status_bit));
      `DV_CHECK_CASE_EQ(status_bit, 1) // Check addr fifo not empty status
      csr_rd(.ptr(ral.upload_status2.payload_depth), .value(status_depth));
      `DV_CHECK_CASE_EQ(status_depth, upload_payload.size()) // Check payload depth
      csr_rd(.ptr(ral.upload_cmdfifo.data), .value(up_cmd));
      `DV_CHECK_CASE_EQ(up_cmd, cmd) // Check correctly fetched upload cmd
      csr_rd(.ptr(ral.upload_addrfifo.data), .value(up_addr));
       // Check correctly fetched upload addr
      `DV_CHECK_CASE_EQ(up_addr, {addr[7:0], addr[15:8], addr[23:16]})
      cfg.clk_rst_vif.wait_clks(10);
      csr_rd(.ptr(ral.upload_status.cmdfifo_notempty), .value(status_bit));
      `DV_CHECK_CASE_EQ(status_bit, 0) // Check cmd fifo empty after reading cmd
      csr_rd(.ptr(ral.upload_status.addrfifo_notempty), .value(status_bit));
      `DV_CHECK_CASE_EQ(status_bit, 0) // Check addr fifo empty after reading cmd
      for (int i = 0; i < upload_payload.size(); i=i+1) begin
        mem_rd(.ptr(ral.buffer), .offset(UPLOAD_OFFSET_ADDR+i), .data(act_payload[i]));
        `DV_CHECK_CASE_EQ(upload_payload[i], act_payload[i]) // Check payload data
      end
      cfg.clk_rst_vif.wait_clks(100);

    end

  endtask : body

endclass : spi_device_cmd_upload_vseq
