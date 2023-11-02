// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class keymgr_dpe_smoke_vseq extends keymgr_dpe_base_vseq;
  `uvm_object_utils(keymgr_dpe_smoke_vseq)
  `uvm_object_new

  rand int num_ops;

  // limit to SW operations
  constraint gen_operation_c {
    gen_operation inside {
      keymgr_dpe_pkg::OpDpeGenHwOut,
      keymgr_dpe_pkg::OpDpeGenSwOut
    };
  }
  constraint num_ops_c {
    num_ops inside {[2:3]};
  }

  task body();
    `uvm_info(`gfn, "Key Manager DPE Smoke Start", UVM_HIGH)
    /* 1. Advance from StWorkDpeReset to StWorkDpeAvailable state (latching OTP)
         - Check OTP key
         - Check dst slot values
       2. Make further advance calls 
         - Generate SW/HW identity's 
         - Check SW/HW output
         - Check dst slot values
    */
    repeat (2) begin
      keymgr_dpe_operations(.advance_state(1), .num_gen_op(0), .clr_output(1));
    end

  endtask : body

endclass : keymgr_dpe_smoke_vseq
