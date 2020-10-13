// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_scoreboard extends cip_base_scoreboard #(
    .CFG_T(otbn_env_cfg),
    .RAL_T(otbn_reg_block),
    .COV_T(otbn_env_cov)
  );
  `uvm_component_utils(otbn_scoreboard)

  // local variables

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
    join_none
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

  task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    case (channel)
      AddrChannel: process_tl_addr(item);
      DataChannel: process_tl_data(item);
      default: `uvm_fatal(`gfn, $sformatf("Invalid channel: %0h", channel))
    endcase
  endtask

  task process_tl_addr(tl_seq_item item);
    // TODO: Fill this out to update the register model on TL accesses (addr channel)
  endtask

  task process_tl_data(tl_seq_item item);
    // TODO: Fill this out to update the register model on TL accesses (data channel)
  endtask

endclass
