// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthrough mode address translation scenario, addr_swap_en on and off
class spi_device_pass_addr_translation_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_pass_addr_translation_vseq)
  `uvm_object_new

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [7:0]  pass_cmd;
    bit [23:0] pass_addr;
    bit [31:0] address_command;
    bit [31:0] addr_mask;
    bit [31:0] addr_data;
    bit [4:0]  cmd_info_idx;
    spi_device_flash_pass_init(PassthroughMode);

    cfg.clk_rst_vif.wait_clks(100);

    repeat (num_trans) begin

      // Randomize opcode and address
      `DV_CHECK_STD_RANDOMIZE_FATAL(pass_addr)
      `DV_CHECK_STD_RANDOMIZE_FATAL(pass_cmd)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cmd_info_idx, cmd_info_idx > 10; cmd_info_idx < 24;)

      // Configure unused CMD_INFO and enable this opcode
      ral.cmd_info[cmd_info_idx].valid.set(1'b1); // Enable this OPCODE
      ral.cmd_info[cmd_info_idx].opcode.set(pass_cmd);
      ral.cmd_info[cmd_info_idx].addr_mode.set(Addr3B); //  3B address for this scenario
      csr_update(.csr(ral.cmd_info[cmd_info_idx]));
      // Configure address swap mask and data
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr_mask)
      `DV_CHECK_STD_RANDOMIZE_FATAL(addr_data)
      ral.addr_swap_mask.set(addr_mask);
      csr_update(.csr(ral.addr_swap_mask));
      ral.addr_swap_data.set(addr_data);
      csr_update(.csr(ral.addr_swap_data));

      // Transfer data without addr swap enabled
      order_cmd_bits(pass_cmd, pass_addr, address_command);
      spi_host_xfer_word(address_command, device_word_rsp);

      cfg.clk_rst_vif.wait_clks(100);

      // Set address translation for this command
      ral.cmd_info[cmd_info_idx].addr_swap_en.set(1'b1);
      csr_update(.csr(ral.cmd_info[cmd_info_idx]));
      spi_host_xfer_word(address_command, device_word_rsp);

      cfg.clk_rst_vif.wait_clks(100);

      // Unset address translation for this command
      ral.cmd_info[cmd_info_idx].addr_swap_en.set(1'b0);
      csr_update(.csr(ral.cmd_info[cmd_info_idx]));
      spi_host_xfer_word(address_command, device_word_rsp);

      cfg.clk_rst_vif.wait_clks(100);
    end

  endtask : body

endclass : spi_device_pass_addr_translation_vseq
