// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_virtual_sequencer extends cip_base_virtual_sequencer #(
  .CFG_T(dma_env_cfg),
  .COV_T(dma_env_cov)
);

  tl_sequencer tl_sequencer_dma_host_h;
  tl_sequencer tl_sequencer_dma_ctn_h;
  tl_sequencer tl_sequencer_dma_sys_h;

`uvm_component_utils(dma_virtual_sequencer)
`uvm_component_new

endclass
