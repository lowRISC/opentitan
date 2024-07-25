// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_dataaddr_rw_access_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_dataaddr_rw_access_vseq)
  `uvm_object_new

  task test_reg(int unsigned reg_idx);
    uvm_status_e   reg_status;
    uvm_reg_data_t value = $urandom;

    `DV_CHECK_FATAL(reg_idx <= 1)

    // Write the random value on the TL side
    tl_mem_ral.dataaddr[reg_idx].write(.status(reg_status), .value(value));
    `DV_CHECK_EQ(reg_status, UVM_IS_OK)

    // The scoreboard doesn't know about the connection between the two registers, so we perform it
    // on the RAL side by hand.
    `DV_CHECK(jtag_dmi_ral.abstractdata[reg_idx].predict(.value(value), .kind(UVM_PREDICT_DIRECT)))

    // Now read the DMI register and check it matches the prediction we just made.
    jtag_dmi_ral.abstractdata[reg_idx].mirror(.status(reg_status), .check(UVM_CHECK));
  endtask

  task body();
    test_reg(0);
    test_reg(1);
  endtask

endclass : rv_dm_dataaddr_rw_access_vseq
