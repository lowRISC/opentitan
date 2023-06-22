// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO(#19028): add CSR supports in scb so we can apply randomize `set_regwen` in any test.
// Currently this randomization will fail in stress_all tests.
class edn_regwen_vseq extends edn_smoke_vseq;
  `uvm_object_utils(edn_regwen_vseq)

  `uvm_object_new

  constraint regwen_c {
    set_regwen == 1;
  }

endclass
