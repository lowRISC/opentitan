// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_jtag_base_vseq extends chip_common_vseq;
  uvm_mem test_mems[$];
  `uvm_object_utils(chip_jtag_base_vseq)

  `uvm_object_new
  jtag_dmi_reg_block jtag_dmi_ral;

  virtual function void set_handles();
    super.set_handles();
    jtag_dmi_ral = cfg.jtag_dmi_ral;
  endfunction // set_handles

  virtual task pre_start();
    select_jtag = SelectRVJtagTap;
    super.pre_start();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    // TODO: Randomize the contents of the debug ROM & the program buffer once out of reset.

    // "Activate" the DM to facilitate ease of testing.
    csr_wr(.ptr(jtag_dmi_ral.dmcontrol.dmactive), .value(1), .blocking(1), .predict(1));
  endtask

  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind inside {"HARD", "TRST"}) begin
        jtag_dmi_ral.reset("HARD");
      end
      super.apply_reset(kind);
    join
  endtask
endclass
