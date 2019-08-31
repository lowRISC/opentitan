// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Core ibex environment virtual sequencer
// ---------------------------------------------
class core_ibex_vseqr extends uvm_sequencer;

  tl_sequencer data_if_seqr;
  tl_sequencer instr_if_seqr;

  `uvm_component_utils(core_ibex_vseqr)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

endclass
