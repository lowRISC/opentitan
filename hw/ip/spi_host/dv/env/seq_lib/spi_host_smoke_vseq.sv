// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class spi_host_smoke_vseq extends spi_host_base_vseq;
  `uvm_object_utils(spi_host_smoke_vseq)

  `uvm_object_new

  task body();
    `uvm_error(`gfn, "FIXME")
  endtask : body

endclass : spi_host_smoke_vseq
