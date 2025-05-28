// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_flash_seq extends dv_base_seq #(
    .REQ         (spi_item),
    .CFG_T       (spi_agent_cfg),
    .SEQUENCER_T (spi_sequencer)
  );
  `uvm_object_utils(spi_device_flash_seq)
  `uvm_object_new

  // indicate which CSB is for this seq to respond
  bit [CSB_WIDTH-1:0] csb_sel = 0;

  // return the data in this queue if it's provided, otherwise, random data will be used
  bit[7:0] byte_data_q[$];
  // allow user to have forever loop to auto respond the req
  bit is_forever_rsp_seq;

  task body();
    cfg.spi_func_mode = SpiModeFlash;
    do begin
      // It takes the sequence item from the monitor after the opcode and address (plus
      // Dummy cycles+read_pipeline delay if it applies for a given command).
      p_sequencer.req_analysis_fifo.peek(req);
      if (req.csb_sel == csb_sel) begin
        `DV_CHECK(p_sequencer.req_analysis_fifo.try_get(req))
      end else begin
        // expect the req is handled by other mode sequence like TPM seq
        // After a small delay, try_get should fail
        #1ps `DV_CHECK(!p_sequencer.req_analysis_fifo.try_get(req))
        continue;
      end
      `downcast(rsp, req.clone());
      rsp.payload_q = byte_data_q;
      start_item(rsp);
      finish_item(rsp);
      get_response(rsp);
    end while (is_forever_rsp_seq);
  endtask

endclass
