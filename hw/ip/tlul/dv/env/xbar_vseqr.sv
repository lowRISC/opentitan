// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Xbar environment virtual sequencer
// ---------------------------------------------
class xbar_vseqr extends uvm_sequencer;

  tl_sequencer host_seqr[];
  tl_sequencer device_seqr[];

  `uvm_component_utils(xbar_vseqr)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

endclass
