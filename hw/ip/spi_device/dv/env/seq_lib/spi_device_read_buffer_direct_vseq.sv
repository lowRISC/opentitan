// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// direct test to verify read buffer related CSRs
//  - readbuf_watermark, readbuf_flip and last_read_addr
class spi_device_read_buffer_direct_vseq extends spi_device_flash_mode_vseq;
  `uvm_object_utils(spi_device_read_buffer_direct_vseq)
  `uvm_object_new

  // Needed in order to track when a given read command will raise the watermark
  // depending on whether the previous command had the read pipeline enabled, and
  // whether the command may have finished just crossing the threshold but never
  // output due to the pipeline delay
  bit [31:0] computed_last_addr;
  bit [31:0] last_cmd_computed_last_addr;
  bit        watermark_set_last;

  task body();
    int start_addr = 0;
    int payload_size;
    bit [1:0] readpipeline;
    bit [2:0] num_lanes;
    // scb is off for this test. Enable CSR auto_predict, otherwise, csr_update doesn't work
    // correctly as `needs_update` may be wrong due to the incorrect mirrored value.
    ral.default_map.set_auto_predict(1);
    spi_device_flash_pass_init();

    // disable watermark event
    ral.read_threshold.set(0);
    csr_update(ral.read_threshold);

    `uvm_info(`gfn, "reading from 0 to half size", UVM_MEDIUM)
    payload_size = READ_BUFFER_SIZE / 2;
    send_read_cmd(start_addr, payload_size, readpipeline, num_lanes);

    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));
    start_addr += payload_size;

    `uvm_info(`gfn, "reading from half size to max size", UVM_MEDIUM)
    // start_addr need to be kept increasing which is how we track the flip bit event
    send_read_cmd(start_addr, payload_size, readpipeline, num_lanes);

    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));
    start_addr += payload_size;

    start_addr += READ_BUFFER_SIZE / 2 - 1;
    `uvm_info(`gfn, $sformatf("reading only the last byte of the 1st half at 0x%0x", start_addr),
              UVM_MEDIUM)
    payload_size = 1;
    send_read_cmd(start_addr, payload_size, readpipeline, num_lanes);

    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));
    start_addr += 1;

    start_addr += READ_BUFFER_SIZE / 2 - 1;
    `uvm_info(`gfn, $sformatf("reading only the last byte of the 2nd half at 0x%0x", start_addr),
              UVM_MEDIUM)
    payload_size = 1;
    send_read_cmd(start_addr, payload_size, readpipeline, num_lanes);

    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));
    start_addr += 1;

    // no watermark event as threshold is 0 (disabled)
    check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(0));

    // testing ReadbufWatermark
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.read_threshold.threshold, value > 0;)
    csr_update(ral.read_threshold);
    read_threshold_val = ral.read_threshold.get();

    if (read_threshold_val > 1) begin
      `uvm_info(`gfn, "reading from 0 to read_threshold_val - 2", UVM_MEDIUM)
      payload_size = read_threshold_val - 2;
      send_read_cmd(start_addr, payload_size, readpipeline, num_lanes);

      watermark_set_last = 0;
      // Start address before the threshold but after all payload we've gone over threshold
      if (is_read_overlap_threshold(num_lanes, readpipeline, start_addr[9:0],
                                    ral.read_threshold.get(), payload_size)) begin
        check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(1));
        watermark_set_last = 1;
      end
      else
        check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(0));

      start_addr += payload_size;
    end // if (read_threshold_val > 1)

    `uvm_info(`gfn, "reading 1 more byte at read_threshold_val - 1", UVM_MEDIUM)
    payload_size = 1;
    send_read_cmd(start_addr, payload_size, readpipeline, num_lanes);
    // Only check for watermark set if the previous read didn't set the watermark
    // If it did, reading one more byte won't set the watermark again
    if (watermark_set_last == 0 &&
        is_read_overlap_threshold(num_lanes, readpipeline, start_addr[9:0],
                                  ral.read_threshold.get(), payload_size)) begin
      check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(1));
      watermark_set_last = 1;
    end
    else begin
      check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(0));
      // Reset the flag - the next read command may go over the threshold next
      watermark_set_last = 0;
    end
    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(0));
    start_addr += 1;

    payload_size = READ_BUFFER_SIZE / 2 - 1;
    `uvm_info(`gfn, "reading from read_threshold_val for 1k", UVM_MEDIUM)
    send_read_cmd(start_addr, payload_size, readpipeline, num_lanes);
    if (watermark_set_last == 0 &&
        is_read_overlap_threshold(num_lanes, readpipeline, start_addr[9:0],
                                  ral.read_threshold.get(), payload_size)) begin
      check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(1));
    end
    else
      check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(0));
    // Clearing the flag since we just went over the half buffer side
    watermark_set_last = 0;
    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(1));

    start_addr += payload_size;

    `uvm_info(`gfn, $sformatf("reading 1 more byte at addr=0x%0x",start_addr), UVM_MEDIUM)
    payload_size = 1;
    send_read_cmd(start_addr, payload_size, readpipeline, num_lanes);

    // Only reading 1-byte: if the watermark was set it won't be set now
    if (watermark_set_last == 0 &&
        is_read_overlap_threshold(num_lanes, readpipeline, start_addr[9:0],
                                  ral.read_threshold.get(), payload_size)) begin
      check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(1));
    end
    else
      check_interrupts(.interrupts((1 << ReadbufWatermark)), .check_set(0));

    check_interrupts(.interrupts((1 << ReadbufFlip)), .check_set(0));
  endtask

  function bit is_read_overlap_threshold(bit [2:0] num_lanes, bit [1:0] readpipeline,
                                         bit [9:0] start_addr, bit [9:0] threshold,
                                         int       payload_size);

    bit extra_due_to_pipeline = num_lanes==4 && readpipeline>0;

    if ( (start_addr[9:0] <= ral.read_threshold.get()) &&
         (start_addr[9:0] + payload_size + extra_due_to_pipeline) >= (ral.read_threshold.get()))
      return 1;
    else
      return 0;
  endfunction

  task send_read_cmd(input bit [31:0] start_addr, input int payload_size,
                     output bit [1:0] readpipeline, output bit [2:0] num_lanes);
    bit [7:0] opcode;
    bit [2:0] num_addr_bytes;
    bit       write_command;
    int dummy_cycles;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(opcode,
        opcode inside {READ_CMD_LIST} && opcode inside {valid_opcode_q};)

    spi_host_xfer_flash_item(opcode, payload_size, start_addr);
    cfg.clk_rst_vif.wait_clks(10);

    cfg.spi_host_agent_cfg.extract_cmd_info_from_opcode(opcode,
                                     // output
                                     num_addr_bytes, write_command, num_lanes,
                                     dummy_cycles, readpipeline);

    last_cmd_computed_last_addr = computed_last_addr;
    computed_last_addr = start_addr + payload_size - 1;
    if (readpipeline > 0 && num_lanes == 4)
      computed_last_addr++;
    csr_rd_check(.ptr(ral.last_read_addr), .compare_value(computed_last_addr));
    `uvm_info(`gfn, $sformatf("Updated last_read_addr = 0x%0x",computed_last_addr[9:0]), UVM_DEBUG)
  endtask
endclass : spi_device_read_buffer_direct_vseq
