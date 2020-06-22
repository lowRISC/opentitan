// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_virtual_sequencer
  extends dv_base_virtual_sequencer #(.CFG_T(ibex_icache_env_cfg), .COV_T(ibex_icache_env_cov));
  `uvm_component_utils(ibex_icache_virtual_sequencer)

  ibex_icache_core_sequencer core_sequencer_h;
  ibex_icache_mem_sequencer  mem_sequencer_h;

  ibex_icache_ecc_sequencer  ecc_tag_sequencers[];
  ibex_icache_ecc_sequencer  ecc_data_sequencers[];

  `uvm_component_new

endclass
