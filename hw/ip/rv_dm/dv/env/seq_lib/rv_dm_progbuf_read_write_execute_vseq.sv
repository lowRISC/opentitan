// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_progbuf_read_write_execute_vseq extends rv_dm_base_vseq;

  `uvm_object_utils(rv_dm_progbuf_read_write_execute_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    Progbuf (.index(0));
    Progbuf (.index(1));
    Progbuf (.index(2));
    Progbuf (.index(3));
    Progbuf (.index(4));
    Progbuf (.index(5));
    Progbuf (.index(6));
    Progbuf (.index(7));
  endtask

  task Progbuf (input int index );
    uvm_reg_data_t data;
    uvm_reg_data_t r_data;
    data = $urandom;
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(1));
      `DV_CHECK_EQ(cfg.rv_dm_vif.cb.debug_req, 1)
      csr_wr(.ptr(tl_mem_ral.halted), .value(0));
      csr_wr(.ptr(jtag_dmi_ral.progbuf[index]), .value(data));
      // The value in 'command' is access register command with postexec bit set.
      csr_wr(.ptr(jtag_dmi_ral.command), .value('h002D0000));
      csr_rd(.ptr(tl_mem_ral.program_buffer[index]), .value(r_data));
      `DV_CHECK_EQ(data, r_data)
  endtask

endclass : rv_dm_progbuf_read_write_execute_vseq
