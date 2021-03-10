// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class spi_host_smoke_vseq extends spi_host_base_vseq;
  `uvm_object_utils(spi_host_smoke_vseq)

  `uvm_object_new

  task body();
    `uvm_info(`gfn, "\n--> start of spi_host_smoke_vseq", UVM_DEBUG)
    // TODO: host sends transactions to spi_agent
    for (uint i = 0; i < 10; i++) begin
      program_command();
    end
    `uvm_info(`gfn, "\n--> end of spi_host_smoke_vseq", UVM_DEBUG)
  endtask : body

endclass : spi_host_smoke_vseq
