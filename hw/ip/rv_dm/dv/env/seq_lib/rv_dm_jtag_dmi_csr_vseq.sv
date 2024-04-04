// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run the JTAG DMT CSRs through our standard CSR suite via JTAG.
class rv_dm_jtag_dmi_csr_vseq extends rv_dm_common_vseq;
  `uvm_object_utils(rv_dm_jtag_dmi_csr_vseq)
  `uvm_object_new

  virtual task body();
    run_csr_vseq_wrapper(.num_times(num_trans), .models({jtag_dmi_ral}));
  endtask : body

endclass
