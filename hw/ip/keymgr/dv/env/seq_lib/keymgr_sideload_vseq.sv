// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable OpGenHwOut to test side load interface
class keymgr_sideload_vseq extends keymgr_smoke_vseq;
  `uvm_object_utils(keymgr_sideload_vseq)
  `uvm_object_new

  rand bit do_clear_sideload;
  rand bit [2:0] clear_dest;

  // also test HW sideload
  constraint gen_operation_c {
    gen_operation inside {keymgr_pkg::OpGenId, keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut};
  }

  constraint clear_dest_c {
    clear_dest dist {[0:3] :/ 4,
                     // reserved value, clear all sideload
                     [4:$] :/ 2};
  }

  virtual task keymgr_operations(bit advance_state = $urandom_range(0, 1),
                                 int num_gen_op    = $urandom_range(1, 4),
                                 bit clr_output    = $urandom_range(0, 1),
                                 bit wait_done     = 1);
    super.keymgr_operations(advance_state, num_gen_op, clr_output, wait_done);
    randomly_clear_sideload();
  endtask : keymgr_operations

  virtual task randomly_clear_sideload();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(do_clear_sideload)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(clear_dest)
    if (do_clear_sideload) begin
      `uvm_info(`gfn, $sformatf("Clear sideload with value %0d", clear_dest), UVM_MEDIUM)
      csr_wr(.ptr(ral.sideload_clear), .value(clear_dest));
    end
  endtask : randomly_clear_sideload
endclass : keymgr_sideload_vseq
