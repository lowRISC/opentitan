// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_mem_tl_access_resuming_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_mem_tl_access_resuming_vseq)
  `uvm_object_new

  task mirror_dmstatus();
    uvm_status_e dmi_status;
    jtag_dmi_ral.dmstatus.mirror(.status(dmi_status), .check(UVM_NO_CHECK));
    `DV_CHECK_EQ(dmi_status, UVM_IS_OK)
  endtask

  // Write to the resumereq field in dmcontrol to ask the (only) hart to resume. Check that the
  // resume request is reflected in RESUME (bit 1) of the FLAGS register. Then respond as the hart
  // to acknowledge the request.
  task request_resume();
    uvm_status_e reg_status;
    uvm_reg_data_t mirrored_flags;

    jtag_dmi_ral.dmcontrol.resumereq.set(1'b1);
    jtag_dmi_ral.dmcontrol.update(.status(reg_status));
    `DV_CHECK_EQ(reg_status, UVM_IS_OK)

    // Make sure that the FLAGS register reflects the resume request that we just made, because the
    // RESUME bit (at index 1) should be set.
    tl_mem_ral.flags[0].mirror(.status(reg_status), .check(UVM_NO_CHECK));
    `DV_CHECK_EQ(reg_status, UVM_IS_OK)
    mirrored_flags = `gmv(tl_mem_ral.flags[0]);
    `DV_CHECK_EQ(mirrored_flags[1], 1'b1)

    // As the hart, we should respond to the resume request by writing the hart id the RESUMING flag
    tl_mem_ral.resuming.write(.status(reg_status), .value(0));
    `DV_CHECK_EQ(reg_status, UVM_IS_OK)
  endtask

  task body();
    uvm_status_e dmi_status;

    // Disable unavailable signal to make sure that hart should be in known
    // state. If hart is unavailable then it could not halted.
    cfg.rv_dm_vif.unavailable <= 0;

    // Request a halt as the debugger and then acknowledge it as the hart.
    request_halt();

    // At this point, dmstatus should reflect the fact that the one and only hart has halted. Read
    // it back and check this is true.
    mirror_dmstatus();
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.anyhalted), 1'b1)
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.allhalted), 1'b1)

    // Clear the halt request
    jtag_dmi_ral.dmcontrol.haltreq.set(1'b0);
    jtag_dmi_ral.dmcontrol.update(.status(dmi_status));
    `DV_CHECK_EQ(dmi_status, UVM_IS_OK)

    // Now tell the hart to resume, and acknowledge the request as the hart.
    request_resume();

    // At this point, reading dmstatus from debug module should show that the one and only hart has
    // acknowledged the resume request. It should also show that the hart is running.
    mirror_dmstatus();
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.anyresumeack), 1'b1)
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.allresumeack), 1'b1)
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.anyrunning), 1'b1)
    `DV_CHECK_EQ(`gmv(jtag_dmi_ral.dmstatus.allrunning), 1'b1)
  endtask
endclass
