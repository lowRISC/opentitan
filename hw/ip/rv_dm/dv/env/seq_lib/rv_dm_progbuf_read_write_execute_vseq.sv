// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_progbuf_read_write_execute_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_progbuf_read_write_execute_vseq)
  `uvm_object_new

  task body();
    uvm_status_e reg_status;
    bit[31:0]    words[8];

    `DV_CHECK_STD_RANDOMIZE_FATAL(words)

    // Ask the debug module to send a halt request, then respond as the hart to say that we are
    // halted.
    request_halt();

    // Fill the program buffer by writing the words to the PROGBUF multiregister. We expect these
    // writes to be refected on the TL side in PROGRAM_BUFFER, so predict the values there to match.
    for (int i = 0; i < 8; i++) begin
      jtag_dmi_ral.progbuf[i].write(.status(reg_status), .value(words[i]));
      `DV_CHECK_EQ(reg_status, UVM_IS_OK)
      `DV_CHECK(tl_mem_ral.program_buffer[i].predict(.value(words[i]), .kind(UVM_PREDICT_DIRECT)))
    end

    // Now read the program buffer back, this time over TL from the PROGRAM_BUFFER multiregister
    for (int i = 0; i < 8; i++) begin
      tl_mem_ral.program_buffer[i].mirror(.status(reg_status), .check(UVM_CHECK));
      `DV_CHECK_EQ(reg_status, UVM_IS_OK)
    end
  endtask

endclass : rv_dm_progbuf_read_write_execute_vseq
