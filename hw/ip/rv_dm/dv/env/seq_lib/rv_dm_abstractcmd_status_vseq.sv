// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_abstractcmd_status_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_abstractcmd_status_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }

  task body();
    // The values in 'cmd_val' are instructions in abstractcmd registers which hart execute.
    abstract_cmd(.index(0),.cmd_val('h7b351073));
    abstract_cmd(.index(1),.cmd_val('h00000517));
    abstract_cmd(.index(2),.cmd_val('h00c55513));
    abstract_cmd(.index(3),.cmd_val('h00c51513));
    abstract_cmd(.index(4),.cmd_val('h7b241073));
    abstract_cmd(.index(5),.cmd_val('h38052403));
    abstract_cmd(.index(6),.cmd_val('h00041073));
    abstract_cmd(.index(7),.cmd_val('h7b202473));
    abstract_cmd(.index(8),.cmd_val('h7b302573));
    abstract_cmd(.index(9),.cmd_val('h00100073));
  endtask

  task abstract_cmd (input int index, input int cmd_val);
    uvm_reg_data_t r_data;
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(1));
    `DV_CHECK_EQ(cfg.rv_dm_vif.cb.debug_req, 1)
    csr_wr(.ptr(tl_mem_ral.halted), .value(0));
    // The value in 'command' is access register command to send valid abstract command.
    csr_wr(.ptr(jtag_dmi_ral.command), .value('h00AB0000));
    csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(r_data));
    `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.abstractcs.busy, r_data));
    csr_rd(.ptr(tl_mem_ral.abstractcmd[index]), .value(r_data));
    `DV_CHECK_EQ(cmd_val, r_data)
  endtask

endclass : rv_dm_abstractcmd_status_vseq
