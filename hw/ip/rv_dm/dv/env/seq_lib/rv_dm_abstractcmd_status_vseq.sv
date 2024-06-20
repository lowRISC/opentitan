// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_abstractcmd_status_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_abstractcmd_status_vseq)
  `uvm_object_new

  // The expected contents of the debug ROM that we will read through the abstract command
  // interface.
  bit [31:0] exp_debug_rom[10] = { 'h7b351073, 'h00000517, 'h00c55513, 'h00c51513, 'h7b241073,
                                   'h38052403, 'h00041073, 'h7b202473, 'h7b302573, 'h00100073 };
  task body();
    uvm_reg_data_t r_data;
    request_halt();
    // The value in 'command' is access register command to send valid abstract command.
    csr_wr(.ptr(jtag_dmi_ral.command), .value('h00AB0000));
    csr_rd(.ptr(jtag_dmi_ral.abstractcs), .value(r_data));
    `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.abstractcs.busy, r_data));

    for (int i = 0; i < 10; i++) begin
      csr_rd(.ptr(tl_mem_ral.abstractcmd[i]), .value(r_data));
      `DV_CHECK_EQ(exp_debug_rom[i], r_data)
    end
  endtask

endclass : rv_dm_abstractcmd_status_vseq
