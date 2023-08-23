// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class rv_dm_cmderr_busy_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_cmderr_busy_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }
  task body();
    write_chk(.ptr(jtag_dmi_ral.progbuf[0]),.cmderr(1),.command(32'h00231000));
    write_chk(.ptr(jtag_dmi_ral.abstractdata[0]),.cmderr(1),.command(32'h00231000));
    write_chk(.ptr(jtag_dmi_ral.abstractcs),.cmderr(1),.command(32'h00231000));
    write_chk(.ptr(jtag_dmi_ral.abstractauto),.cmderr(1),.command(32'h00231000));
    write_chk(.ptr(jtag_dmi_ral.command),.cmderr(1),.command(32'h00231000));
    read_chk(.ptr(jtag_dmi_ral.progbuf[0]),.cmderr(1),.command(32'h00231000));
    read_chk(.ptr(jtag_dmi_ral.abstractdata[0]),.cmderr(1),.command(32'h00231000));
  endtask

endclass : rv_dm_cmderr_busy_vseq
