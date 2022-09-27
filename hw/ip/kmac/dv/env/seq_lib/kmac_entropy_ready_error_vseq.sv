// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_entropy_ready_error_vseq extends kmac_app_vseq;

  `uvm_object_utils(kmac_entropy_ready_error_vseq)
  `uvm_object_new

  // Issue #15140, currently only confirmed the app interface behavior.
  constraint en_app_c {
    en_app == 1;
  }

  constraint entropy_ready_c {
    entropy_ready == 0;
  }

endclass
