// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_base_vseq
  extends dv_base_vseq #(
    .CFG_T               (ibex_icache_env_cfg),
    .COV_T               (ibex_icache_env_cov),
    .VIRTUAL_SEQUENCER_T (ibex_icache_virtual_sequencer)
  );
  `uvm_object_utils(ibex_icache_base_vseq)
  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
  endtask

  virtual task dut_shutdown();
    // check for pending ibex_icache operations and wait for them to complete
    // TODO
  endtask

endclass : ibex_icache_base_vseq
