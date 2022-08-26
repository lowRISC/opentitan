// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// direct test to verify read buffer related CSRs
//  - readbuf_watermark, readbuf_flip and last_read_addr
class spi_device_read_buffer_direct_vseq extends spi_device_flash_mode_vseq;
  `uvm_object_utils(spi_device_read_buffer_direct_vseq)
  `uvm_object_new

  task body();
    int start_addr = 0;
    int payload_size;
    spi_device_flash_pass_init();

    // disable watermark event
    ral.read_threshold.set(0);
    csr_update(ral.read_threshold);

    `uvm_info(`gfn, "reading from 0 to half size", UVM_MEDIUM)
    payload_size = READ_BUFFER_SIZE / 2;
    send_read_cmd(start_addr, payload_size);
    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));
    start_addr += payload_size;

    `uvm_info(`gfn, "reading from half size to max size", UVM_MEDIUM)
    // start_addr need to be kept increasing which is how we track the flip bit event
    send_read_cmd(start_addr, payload_size);
    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));
    start_addr += payload_size;

    start_addr += READ_BUFFER_SIZE / 2 - 1;
    `uvm_info(`gfn, $sformatf("reading only the last byte of the 1st half at 0x%0x", start_addr),
              UVM_MEDIUM)
    send_read_cmd(.start_addr(start_addr), .payload_size(1));
    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));
    start_addr += 1;

    start_addr += READ_BUFFER_SIZE / 2 - 1;
    `uvm_info(`gfn, $sformatf("reading only the last byte of the 2nd half at 0x%0x", start_addr),
              UVM_MEDIUM)
    send_read_cmd(.start_addr(start_addr), .payload_size(1));
    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));
    start_addr += 1;

    // no watermark event as threshold is 0
    check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(0));

    // testing ReadbufWatermark
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(read_threshold_val, read_threshold_val > 0;)
    ral.read_threshold.set(read_threshold_val);
    csr_update(ral.read_threshold);

    if (read_threshold_val > 1) begin
      `uvm_info(`gfn, "reading from 0 to read_threshold_val - 2", UVM_MEDIUM)
      payload_size = read_threshold_val - 1;
      send_read_cmd(.start_addr(start_addr), .payload_size(payload_size));
      check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(0));
      start_addr += payload_size;
    end

    `uvm_info(`gfn, "reading 1 more byte at read_threshold_val - 1", UVM_MEDIUM)
    send_read_cmd(.start_addr(start_addr), .payload_size(1));
    check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(1));
    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(0));
    start_addr += 1;

    payload_size = READ_BUFFER_SIZE / 2 - 1;
    `uvm_info(`gfn, "reading from read_threshold_val for 1k", UVM_MEDIUM)
    send_read_cmd(.start_addr(start_addr), .payload_size(payload_size));
    // no watermark as watermark event isn't sticky
    check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(0));
    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));
    start_addr += payload_size;

    `uvm_info(`gfn, "reading 1 more byte at read_threshold_val - 1 in 2nd half", UVM_MEDIUM)
    send_read_cmd(.start_addr(start_addr), .payload_size(1));
    check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(1));
    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(0));
  endtask

  task send_read_cmd(bit[31:0] start_addr, int payload_size);
    bit [7:0] opcode;

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(opcode,
        opcode inside {READ_CMD_LIST} && opcode inside {valid_opcode_q};)

    spi_host_xfer_flash_item(opcode, payload_size, start_addr);
    cfg.clk_rst_vif.wait_clks(10);

    csr_rd_check(.ptr(ral.last_read_addr), .compare_value(start_addr + payload_size - 1));
  endtask
endclass : spi_device_read_buffer_direct_vseq
