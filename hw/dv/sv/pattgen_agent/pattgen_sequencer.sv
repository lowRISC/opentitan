// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_sequencer extends dv_base_sequencer#(pattgen_item, pattgen_agent_cfg);
  `uvm_component_utils(pattgen_sequencer)
  `uvm_component_new

  // pattgen DUT does not require reponses from pattgen_agent thus no need extension
endclass : pattgen_sequencer
