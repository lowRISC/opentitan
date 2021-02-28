// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_base_vseq extends cip_base_vseq #(
    .RAL_T               (spi_host_reg_block),
    .CFG_T               (spi_host_env_cfg),
    .COV_T               (spi_host_env_cov),
    .VIRTUAL_SEQUENCER_T (spi_host_virtual_sequencer)
  );
  `uvm_object_utils(spi_host_base_vseq)

  // various knobs to enable certain routines
  bit do_spi_host_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_spi_host_init) spi_host_init();
  endtask

  virtual task dut_shutdown();
    // check for pending spi_host operations and wait for them to complete
    // TODO
  endtask

  // setup basic spi_host features
  virtual task spi_host_init();
    `uvm_error(`gfn, "FIXME")
  endtask

endclass : spi_host_base_vseq
