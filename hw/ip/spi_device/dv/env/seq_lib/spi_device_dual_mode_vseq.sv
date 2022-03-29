// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Output command in dual mode test
class spi_device_dual_mode_vseq extends spi_device_pass_base_vseq;
  `uvm_object_utils(spi_device_dual_mode_vseq)
  `uvm_object_new
  rand bit [7:0]  op_cmd;
  rand bit [2:0]  num_lanes;
  constraint op_cmd_c {
    op_cmd == READ_DUAL;
  };
  constraint num_lanes_c {
    num_lanes == 3'h2;
  };

  virtual task body();
    bit [31:0] device_word_rsp;
    bit [31:0] cmd_addr;
    bit [31:0] address_command;
    bit [7:0] read_size;
    bit rx_order;
    bit [7:0] addr [$];
    bit [4:0]  cmd_slot;
    addr_mode_e addr_size;
    spi_device_flash_pass_init(FlashMode);
    cfg.clk_rst_vif.wait_clks(100);
    prepare_buffer(); // Randomize buffer data

    repeat (num_trans) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(read_size, read_size%4 == 0 && read_size < 65;)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(addr_size, addr_size >= Addr3B;)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cmd_slot, cmd_slot >= 5 && cmd_slot <= 10;)
      config_cmd_info(op_cmd, cmd_slot, addr_size, num_lanes); // Configure dual read in slot 5 - 10
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(cmd_addr, cmd_addr[15:0] == 0;)
      // Prepare data for transfer
      csr_rd(.ptr(ral.cfg.rx_order), .value(rx_order));
      if (rx_order == 0) begin
        op_cmd = {<<1{op_cmd}};
        cmd_addr = {<<1{cmd_addr}};
      end
      for (int i = 0; i < addr_size; i++) begin
        addr[i] = cmd_addr[i*8 + 7 -: 8];
      end
      // Issue command - opcode - address 3B - read size in bytes - 2 lanes
      spi_host_xfer_cmd_out(op_cmd, addr, read_size, num_lanes);
      cfg.clk_rst_vif.wait_clks(1000);
    end

  endtask : body

endclass : spi_device_dual_mode_vseq
