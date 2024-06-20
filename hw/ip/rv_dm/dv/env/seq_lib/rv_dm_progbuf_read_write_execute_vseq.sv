// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_progbuf_read_write_execute_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_progbuf_read_write_execute_vseq)
  `uvm_object_new

  task progbuf_rw(int idx);
    uvm_reg_data_t data = $urandom;
    uvm_reg_data_t r_data;
    csr_wr(.ptr(jtag_dmi_ral.progbuf[idx]), .value(data));
    csr_rd(.ptr(tl_mem_ral.program_buffer[idx]), .value(r_data));
    `DV_CHECK_EQ(data, r_data)
  endtask

  task body();
    // Call the task from base_vseq to halt the hart.
    request_halt();
    for (int i = 0; i < 8; i++) progbuf_rw(i);
  endtask

endclass : rv_dm_progbuf_read_write_execute_vseq
