// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run the JTAG DMT CSRs through our standard CSR suite via JTAG.
class rv_dm_jtag_dtm_csr_vseq extends rv_dm_common_vseq;
  `uvm_object_utils(rv_dm_jtag_dtm_csr_vseq)
  `uvm_object_new

  virtual task body();
    // Clear the jtag_dtm_ral.dmi.op field before starting the CSR suite of tests to ensure its
    // mirrored value reflects 0 (nop) instead of the value from previous accesses.
    csr_wr(.ptr(jtag_dtm_ral.dmi.op), .value(0), .blocking(1), .predict(1));
    run_csr_vseq_wrapper(.num_times(num_trans), .models({jtag_dtm_ral}));
  endtask : body

endclass
