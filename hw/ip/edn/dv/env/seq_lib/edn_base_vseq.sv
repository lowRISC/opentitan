// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class edn_base_vseq extends cip_base_vseq #(
    .RAL_T               (edn_reg_block),
    .CFG_T               (edn_env_cfg),
    .COV_T               (edn_env_cov),
    .VIRTUAL_SEQUENCER_T (edn_virtual_sequencer)
  );
  `uvm_object_utils(edn_base_vseq)

  `uvm_object_new

  task body();
    // Start csrng_device_seq
    device_init();
    // Initialize DUT
    dut_init();
  endtask

  virtual task device_init();
    csrng_device_seq   m_dev_seq;

    m_dev_seq = csrng_device_seq::type_id::create("m_dev_seq");
    `uvm_info(`gfn, "Start csrng_device sequence", UVM_DEBUG)

    fork
      m_dev_seq.start(p_sequencer.csrng_sequencer_h);
    join_none
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
  endtask

  virtual task dut_shutdown();
    // check for pending edn operations and wait for them to complete
    // TODO
  endtask

endclass : edn_base_vseq
