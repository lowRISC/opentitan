// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_hartsel_warl_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_hartsel_warl_vseq)
  `uvm_object_new

  task body();
    bit [19:0] hartsel;

    // Write '1 to the hartsel fields
    jtag_dmi_ral.dmcontrol.hartselhi.set(1023);
    jtag_dmi_ral.dmcontrol.hartsello.set(1023);
    csr_update(.csr(jtag_dmi_ral.dmcontrol));

    // Now read back the dmcontrol register, which should be clipped to NrHarts-1
    begin
      uvm_reg_data_t rdata;
      csr_rd(.ptr(jtag_dmi_ral.dmcontrol), .value(rdata));
    end

    hartsel = {`gmv(jtag_dmi_ral.dmcontrol.hartselhi), `gmv(jtag_dmi_ral.dmcontrol.hartsello)};

    // Check that we got the clipped value that we expect. This should be NrHarts - 1
    `DV_CHECK_EQ(hartsel, rv_dm_reg_pkg::NrHarts - 1)
  endtask : body

endclass
