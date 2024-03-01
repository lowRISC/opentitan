// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_progbuf_exception_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_progbuf_exception_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }
  task body();
    uvm_reg_data_t data;
    uvm_reg_data_t r_data;
    repeat (2) begin
      data = $urandom;
      request_halt();
      csr_wr(.ptr(jtag_dmi_ral.command), .value(data));
      csr_wr(.ptr(tl_mem_ral.exception), .value(data));
      csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(r_data));
      `DV_CHECK_EQ(AbstractCmdErrException, get_field_val(jtag_dmi_ral.abstractcs.cmderr,
                                                          r_data));
    end
  endtask

endclass:rv_dm_progbuf_exception_vseq
