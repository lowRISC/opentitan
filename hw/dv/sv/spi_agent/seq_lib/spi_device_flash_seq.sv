// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_flash_seq extends dv_base_seq #(
    .REQ         (spi_item),
    .CFG_T       (spi_agent_cfg),
    .SEQUENCER_T (spi_sequencer)
  );
  `uvm_object_utils(spi_device_flash_seq)
  `uvm_object_new

  // return the data in this queue if it's provided, otherwise, random data will be used
  bit[7:0] byte_data_q[$];
  // allow user to have forever loop to auto respond the req
  bit is_forever_rsp_seq;

  task body();
    do begin
      spi_item req;
      p_sequencer.req_analysis_fifo.get(req);
      `downcast(rsp, req.clone());
      rsp.payload_q = byte_data_q;
      start_item(rsp);
      finish_item(rsp);
    end while (is_forever_rsp_seq);
  endtask

endclass
