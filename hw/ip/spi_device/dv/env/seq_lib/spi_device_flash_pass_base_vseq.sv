// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthrough base sequence
class spi_device_flash_pass_base_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_flash_pass_base_vseq)
  `uvm_object_new

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
    `DV_CHECK_GE(mode, FlashMode);
    if (mode == FlashMode) begin
      ral.control.mode.set(FlashMode);
    end
    if (mode == PassthroughMode) begin
      ral.control.mode.set(PassthroughMode);
    end
    csr_update(.csr(ral.control));
  endtask : spi_device_flash_pass_init

  // Task for basic read operation
  virtual task do_flash_pass_read(bit [7:0] opcode);
    bit [7:0]  pass_cmd;
    bit [23:0] pass_addr;
    bit [31:0] address_command;
    bit [31:0] device_word_rsp;
    bit [7:0]  device_byte_rsp;

    // Read command
    pass_cmd = opcode;

    //Switch to passthrough mode and configure slot for read command
    //TODO Consider randomizing other fields
    case (opcode)
      READ_STATUS_1 : begin
        ral.cmd_info[0].valid.set(1'b1); // Enable this OPCODE
        ral.cmd_info[0].opcode.set(opcode);
        ral.cmd_info[0].payload_dir.set(PayloadOut);
        ral.cmd_info[0].payload_en.set(4'h2);
        csr_update(.csr(ral.cmd_info[0]));
      end
      READ_STATUS_2 : begin
        ral.cmd_info[1].valid.set(1'b1); // Enable this OPCODE
        ral.cmd_info[1].opcode.set(opcode);
        ral.cmd_info[1].payload_dir.set(PayloadOut);
        ral.cmd_info[1].payload_en.set(4'h2);
        csr_update(.csr(ral.cmd_info[1]));
      end
      READ_STATUS_3 : begin
        ral.cmd_info[2].valid.set(1'b1); // Enable this OPCODE
        ral.cmd_info[2].opcode.set(opcode);
        ral.cmd_info[2].payload_dir.set(PayloadOut);
        ral.cmd_info[2].payload_en.set(4'h2);
        csr_update(.csr(ral.cmd_info[2]));
      end
      READ_JEDEC : begin
        ral.cmd_info[3].valid.set(1'b1); // Enable this OPCODE
        ral.cmd_info[3].opcode.set(opcode);
        ral.cmd_info[3].payload_dir.set(PayloadOut);
        ral.cmd_info[3].payload_en.set(4'h2);
        csr_update(.csr(ral.cmd_info[3]));
      end
      READ_SFDP : begin
        ral.cmd_info[4].valid.set(1'b1); // Enable this OPCODE
        ral.cmd_info[4].opcode.set(opcode);
        ral.cmd_info[4].payload_dir.set(PayloadOut);
        ral.cmd_info[4].payload_en.set(4'h2);
        csr_update(.csr(ral.cmd_info[4]));
      end
      default : begin
      end
    endcase
    // Randomize address
    `DV_CHECK_STD_RANDOMIZE_FATAL(pass_addr)

    // Prepare data for transfer
    order_cmd_bits(pass_cmd, pass_addr, address_command);
    spi_host_xfer_byte(address_command[7:0], device_byte_rsp);

    cfg.clk_rst_vif.wait_clks(100);
  endtask : do_flash_pass_read

endclass : spi_device_flash_pass_base_vseq
