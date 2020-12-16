// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Enable OpGenHwOut to test side load interface
class keymgr_sideload_vseq extends keymgr_smoke_vseq;
  `uvm_object_utils(keymgr_sideload_vseq)
  `uvm_object_new

  // also test HW sideload
  constraint gen_operation_c {
    gen_operation inside {keymgr_pkg::OpGenId, keymgr_pkg::OpGenSwOut, keymgr_pkg::OpGenHwOut};
  }
endclass : keymgr_sideload_vseq
