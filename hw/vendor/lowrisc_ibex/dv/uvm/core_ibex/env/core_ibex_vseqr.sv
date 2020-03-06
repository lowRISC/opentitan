// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Core ibex environment virtual sequencer
// ---------------------------------------------
class core_ibex_vseqr extends uvm_sequencer;

  ibex_mem_intf_slave_sequencer                   data_if_seqr;
  ibex_mem_intf_slave_sequencer                   instr_if_seqr;
  irq_master_sequencer                            irq_seqr;

  `uvm_component_utils(core_ibex_vseqr)
  `uvm_component_new

endclass
