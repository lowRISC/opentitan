// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthrough base sequence
class spi_device_pass_base_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_pass_base_vseq)
  `uvm_object_new

  // Task for flash or pass init
  virtual task spi_device_flash_pass_init(device_mode_e mode);
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
    // Set the passthrough or flash mode mode
    `DV_CHECK(mode inside {FlashMode, PassthroughMode});
    if (mode == FlashMode) begin
      ral.control.mode.set(FlashMode);
    end
    if (mode == PassthroughMode) begin
      ral.control.mode.set(PassthroughMode);
    end
    csr_update(.csr(ral.control));
  endtask : spi_device_flash_pass_init

  // Task for configuring enable/disable of command opcode
  virtual task cfg_cmd_filter(bit not_enable, bit [7:0] cmd);
    bit [7:0] cmd_position;
    bit [7:0] cmd_offset;
    // Calculate filter bit position
    cmd_position = cmd / 32;
    cmd_offset = cmd % 32;
    ral.cmd_filter[cmd_position].filter[cmd_offset].set(not_enable);
    csr_update(.csr(ral.cmd_filter[cmd_position]));
  endtask : cfg_cmd_filter

  // Task for keeping opcode integrity regardless of rx_order config
  virtual task order_cmd_bits(bit [7:0] pass_cmd, bit[23:0] pass_addr, ref bit [31:0] addr_cmd);
    bit rx_order;
    csr_rd(.ptr(ral.cfg.rx_order), .value(rx_order));
    if (rx_order == 0) begin
      pass_cmd = {<<1{pass_cmd}};
      pass_addr = {<<1{pass_addr}};
      addr_cmd = {pass_addr, pass_cmd};
    end else begin
      addr_cmd = {pass_addr, pass_cmd};
    end
  endtask : order_cmd_bits

  // Task for preparing memory buffer for read commands
  virtual task prepare_buffer();
    bit [31:0] buffer_data [1024];
    `DV_CHECK_STD_RANDOMIZE_FATAL(buffer_data)
    // Prepare Buffer
    for (int i = 0; i < 1024; i++) begin // Fill buffer with random data
      mem_wr(.ptr(ral.buffer), .offset(i), .data(buffer_data[i]));
    end
  endtask : prepare_buffer

  // Task for configuring cmd info slot
  virtual task config_cmd_info(bit [7:0] opcode, bit [4:0] idx, addr_mode_e addr_size,
                                     bit [2:0] num_lanes);
    bit [3:0] lanes_en;
    case (num_lanes)
      1 : lanes_en = 4'h2;
      2 : lanes_en = 4'h3;
      4 : lanes_en = 4'hF;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported lanes num 0x%0h", num_lanes))
    endcase
    ral.cmd_info[idx].valid.set(1'b1); // Enable this OPCODE
    ral.cmd_info[idx].opcode.set(opcode);// Read Dual
    ral.cmd_info[idx].addr_mode.set(addr_size);
    ral.cmd_info[idx].payload_en.set(lanes_en);
    ral.cmd_info[idx].payload_dir.set(PayloadOut);
    csr_update(.csr(ral.cmd_info[idx]));
  endtask : config_cmd_info

endclass : spi_device_pass_base_vseq
