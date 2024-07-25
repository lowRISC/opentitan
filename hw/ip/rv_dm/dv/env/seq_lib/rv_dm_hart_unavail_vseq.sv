// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_hart_unavail_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_hart_unavail_vseq)
  `uvm_object_new

  task check_unavailable(bit req_unavailable);
    uvm_status_e reg_status;

    // Set the unavailable pin for the one and only hart to match req_unavailable.
    cfg.rv_dm_vif.cb.unavailable <= req_unavailable;

    // Now update the RAL model of the dmstatus register. Do not check that the RAL matches: it
    // won't do if we have just changed the unavailable status.
    jtag_dmi_ral.dmstatus.mirror(.status(reg_status), .check(UVM_NO_CHECK));
    `DV_CHECK_EQ(reg_status, UVM_IS_OK)

    // Since there is just one hart, the anyunavail and allunavail fields should both equal the
    // unavailable flag that we have set. Check they do.
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.anyunavail), req_unavailable)
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.allunavail), req_unavailable)
  endtask

  task body();
    repeat (10) begin
      check_unavailable($urandom_range(0, 1));
      cfg.clk_rst_vif.wait_clks(10);
    end
  endtask

endclass : rv_dm_hart_unavail_vseq
