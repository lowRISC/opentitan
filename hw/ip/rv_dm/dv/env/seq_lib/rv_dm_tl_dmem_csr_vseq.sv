// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run the debug memory CSRs through our standard CSR suite via TL device interface.
class rv_dm_tl_dmem_csr_vseq extends rv_dm_common_vseq;
  `uvm_object_utils(rv_dm_tl_dmem_csr_vseq)
  `uvm_object_new

  virtual task body();
    run_csr_vseq_wrapper(.num_times(num_trans), .models({tl_mem_ral}));
  endtask : body

endclass : rv_dm_tl_dmem_csr_vseq
