// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Testing inactive_level feature of pattgen
class pattgen_inactive_level_vseq extends pattgen_base_vseq;
  `uvm_object_utils(pattgen_inactive_level_vseq)
  `uvm_object_new

  virtual task pre_start();
    // Enable inactive_level feature (subject to randomization).
    inactive_level_en = 1'b1;
    cfg.en_scb = 1'b0; // TODO(#23219): Remove this when the scoreboard supports the inactive_level
                       // feature.
    super.pre_start();
  endtask

endclass : pattgen_inactive_level_vseq
