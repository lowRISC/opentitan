// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthrough mode filtering of commands scenario, filter on and off
class spi_device_pass_cmd_filtering_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_pass_cmd_filtering_vseq)
  `uvm_object_new

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [7:0]  pass_cmd;
    bit [23:0] pass_addr;
    bit [31:0] address_command;
    bit [4:0]  cmd_info_idx;
    spi_device_flash_pass_init(PassthroughMode);

    cfg.clk_rst_vif.wait_clks(100);

    repeat (num_trans) begin

      // Randomize opcode and address
      `DV_CHECK_STD_RANDOMIZE_FATAL(pass_addr)
      `DV_CHECK_STD_RANDOMIZE_FATAL(pass_cmd)

      // Configure unused CMD_INFO and enable this opcode
      ral.cmd_info[cmd_info_idx].valid.set(1'b1); // Enable this OPCODE
      ral.cmd_info[cmd_info_idx].opcode.set(pass_cmd);
      ral.cmd_info[cmd_info_idx].addr_mode.set(Addr3B); //  3B address for this scenario
      csr_update(.csr(ral.cmd_info[cmd_info_idx]));

      // Make sure filter is not blocking command opcode
      cfg_cmd_filter(0, pass_cmd);

      // Prepare data for transfer
      order_cmd_bits(pass_cmd, pass_addr, address_command);
      spi_host_xfer_word(address_command, device_word_rsp);

      cfg.clk_rst_vif.wait_clks(100);

      // Set filtering of this command
      cfg_cmd_filter(1, pass_cmd);
      spi_host_xfer_word(address_command, device_word_rsp);

      cfg.clk_rst_vif.wait_clks(100);

      // Unset filtering and check if pass works again
      cfg_cmd_filter(0, pass_cmd);
      spi_host_xfer_word(address_command, device_word_rsp);

      cfg.clk_rst_vif.wait_clks(100);
    end

  endtask : body

endclass : spi_device_pass_cmd_filtering_vseq
