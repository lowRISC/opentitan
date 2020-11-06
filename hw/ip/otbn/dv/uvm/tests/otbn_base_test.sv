// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_base_test extends dv_base_test #(
    .CFG_T(otbn_env_cfg),
    .ENV_T(otbn_env)
  );

  `uvm_component_utils(otbn_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // otbn_env_cfg: cfg
  // otbn_env:     env

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!$value$plusargs("otbn_elf_dir=%0s", cfg.otbn_elf_dir)) begin
      `uvm_fatal(`gfn, "Missing required plusarg: otbn_elf_dir.")
    end
  endfunction

endclass : otbn_base_test
