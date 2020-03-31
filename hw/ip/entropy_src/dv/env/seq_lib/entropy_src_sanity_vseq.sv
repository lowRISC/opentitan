// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// basic sanity test vseq
class entropy_src_sanity_vseq extends entropy_src_base_vseq;
  `uvm_object_utils(entropy_src_sanity_vseq)

  `uvm_object_new

  task body();
    bit [TL_DW-1:0] rdata, es_conf;

    // initialize config register
    es_conf[0] = 1; // set master enable

//    csr_wr(.csr(ral.es_conf), .value(es_conf));
    csr_rd(.ptr(ral.es_rev), .value(rdata));
    `uvm_info(`gfn, $sformatf("chip_type = %0d, hw_rev = %0d, abi_rev = %0d", rdata[23:16], rdata[15:8], rdata[7:0]), UVM_NONE)
  endtask : body

endclass : entropy_src_sanity_vseq
