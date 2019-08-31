// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Ibex core virtual sequence
// ---------------------------------------------

class core_ibex_vseq extends uvm_sequence;

  tl_device_seq             instr_intf_seq;
  tl_device_seq             data_intf_seq;
  mem_model_pkg::mem_model  mem;

  `uvm_object_utils(core_ibex_vseq)
  `uvm_declare_p_sequencer(core_ibex_vseqr)
  `uvm_object_new

  virtual task body();
    instr_intf_seq = tl_device_seq::type_id::create("instr_intf_seq");
    data_intf_seq  = tl_device_seq::type_id::create("data_intf_seq");
    instr_intf_seq.mem = mem;
    data_intf_seq.mem  = mem;
    fork
      instr_intf_seq.start(p_sequencer.instr_if_seqr);
      data_intf_seq.start(p_sequencer.data_if_seqr);
    join_none
  endtask

endclass
