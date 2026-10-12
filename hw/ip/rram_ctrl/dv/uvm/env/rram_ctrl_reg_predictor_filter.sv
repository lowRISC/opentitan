// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Forwards only non-erroring TL data-channel items to a uvm_reg_predictor. This has to happen
// upstream of the predictor: uvm_reg_predictor::write() calls do_predict() unconditionally and
// never checks rw.status, so a tl_reg_adapter::bus2reg() fix alone can't prevent prediction.
//
// Without this, rejected writes (e.g. cip_base_vseq__tl_errors.svh's
// tl_write_less_than_csr_width) get mispredicted as successful, and errored reads (d_data is
// undefined on d_error=1) corrupt the mirror via UVM_PREDICT_READ, which ignores access policy.
class rram_ctrl_reg_predictor_filter extends uvm_subscriber #(tl_seq_item);
  `uvm_component_utils(rram_ctrl_reg_predictor_filter)

  uvm_analysis_port #(tl_seq_item) ap;

  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void write(tl_seq_item t);
endclass : rram_ctrl_reg_predictor_filter

function rram_ctrl_reg_predictor_filter::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

function void rram_ctrl_reg_predictor_filter::build_phase(uvm_phase phase);
  super.build_phase(phase);
  ap = new("ap", this);
endfunction : build_phase

function void rram_ctrl_reg_predictor_filter::write(tl_seq_item t);
  if (!t.d_error) ap.write(t);
endfunction : write
