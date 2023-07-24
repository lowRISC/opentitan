// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_base_test extends cip_base_test #(
  .CFG_T(dma_env_cfg),
  .ENV_T(dma_env)
);

  `uvm_component_utils(dma_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction: build_phase

endclass
