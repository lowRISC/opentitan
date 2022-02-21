// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthrough mode filtering of commands scenario, filter on and off
class spi_device_pass_cmd_filtering_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_pass_cmd_filtering_vseq)
  `uvm_object_new

  virtual task cfg_cmd_filter(bit not_enable, bit[7:0] cmd);
    bit [7:0] cmd_position;
    bit [7:0] cmd_offset;
    // Calculate filter bit position
    cmd_position = cmd / 32;
    cmd_offset = cmd % 32;
    ral.cmd_filter[cmd_position].filter[cmd_offset].set(not_enable);
    csr_update(.csr(ral.cmd_filter[cmd_position]));
  endtask

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [7:0]  pass_cmd;
    bit [23:0] pass_addr;
    bit [31:0] address_command;

    bit [31:0] host_data;
    bit [31:0] device_data;
    bit [31:0] device_data_exp;
    uint       avail_bytes;
    bit [31:0] host_data_exp_q[$];
    fork
      start_reactive_seq();
    join_none

    spi_device_init();

    // Fixed config for this scenario
    cfg.m_spi_agent_cfg.sck_polarity[0] = 0;
    cfg.m_spi_agent_cfg.sck_phase[0] = 0;
    cfg.m_spi_agent_cfg.host_bit_dir = 1;
    cfg.m_spi_agent_cfg.device_bit_dir = 1;
    ral.cfg.tx_order.set(1);
    ral.cfg.rx_order.set(1);
    ral.cfg.cpol.set(1'b0);
    ral.cfg.cpha.set(1'b0);
    csr_update(.csr(ral.cfg)); // TODO check if randomization possible

    repeat (num_trans) begin
      // Set the passthrough mode
      ral.control.mode.set(PassthroughMode);
      csr_update(.csr(ral.control));

      // Randomize opcode and address
      `DV_CHECK_STD_RANDOMIZE_FATAL(pass_addr)
      `DV_CHECK_STD_RANDOMIZE_FATAL(pass_cmd)

      // Configure unused CMD_INFO and enable this opcode
      ral.cmd_info[11].valid.set(1'b1); // Enable this OPCODE
      ral.cmd_info[11].opcode.set(pass_cmd);
      ral.cmd_info[11].addr_mode.set(Addr3B); //  3B address for this scenario
      csr_update(.csr(ral.cmd_info[11]));

      // Make sure filter is not blocking command opcode
      cfg_cmd_filter(0, pass_cmd);

      // Prepare data for transfer
      pass_cmd = {<<1{pass_cmd}};
      pass_addr = {<<1{pass_addr}};
      address_command = {pass_addr, pass_cmd};
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
