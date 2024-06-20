// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_progbuf_busy_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_progbuf_busy_vseq)
  `uvm_object_new

  task body();
    uvm_reg_data_t data;
    uvm_reg_data_t r_data;
    repeat ($urandom_range(1, 10)) begin
      data = $urandom_range(0,31);
      request_halt();
      // Access Register command with postexec bit set.
      csr_wr(.ptr(jtag_dmi_ral.command), .value('h00250000));
      csr_wr(.ptr(jtag_dmi_ral.progbuf[0]), .value(data));
      csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(r_data));
      `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.abstractcs.busy, r_data));
    end
  endtask

endclass:rv_dm_progbuf_busy_vseq
