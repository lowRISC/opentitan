// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// HALTED test vseq
class rv_dm_mem_tl_access_halted_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_mem_tl_access_halted_vseq)
  `uvm_object_new

  task body();
    uvm_reg_data_t r_data;
    // Disable unavailable signal to make sure that hart should be in known state. if hart
    // is unavailable then it could not halted.
    cfg.rv_dm_vif.unavailable <= 0;

    // Make sure that the ndmreset signal is not currently asserted. If it is asserted then DMI
    // operations work but the TLUL connection is blocked by u_tlul_lc_gate_rom, which is held in
    // the flush state.
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.ndmreset), .value(0));

    // Write to HALTED, which should cause anyhalted and allhalted to be set.
    request_halt();
    csr_rd(.ptr(jtag_dmi_ral.dmstatus), .value(r_data));

    // Assuming that we haven't entered reset (in which case r_data could be anything), check that
    // anyhalted and allhalted are indeed set.
    if (cfg.clk_rst_vif.rst_n) begin
      `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.dmstatus.anyhalted, r_data))
      `DV_CHECK_EQ(1, get_field_val(jtag_dmi_ral.dmstatus.allhalted, r_data))
    end
  endtask : body

endclass : rv_dm_mem_tl_access_halted_vseq
