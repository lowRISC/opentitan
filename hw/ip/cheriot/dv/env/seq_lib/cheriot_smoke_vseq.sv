// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class cheriot_smoke_vseq extends cheriot_base_vseq;
  `uvm_object_utils(cheriot_smoke_vseq)

  `uvm_object_new

  task body();
  endtask : body

endclass : cheriot_smoke_vseq
