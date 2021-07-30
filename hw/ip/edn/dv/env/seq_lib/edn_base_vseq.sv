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

  bit do_edn_init = 1'b1;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    `uvm_info("SEN:00", $sformatf("Base sequence body, do_edn_init = %0d", do_edn_init), UVM_NONE)
    if (do_edn_init) begin
      // Initialize DUT and start device sequence
      edn_init();
      device_init();
    end
  endtask

  virtual task device_init();
    csrng_device_seq   m_dev_seq;

    m_dev_seq = csrng_device_seq::type_id::create("m_dev_seq");
    `uvm_info(`gfn, "Start csrng_device sequence", UVM_DEBUG)

    fork
      m_dev_seq.start(p_sequencer.csrng_sequencer_h);
    join_none
  endtask

  virtual task edn_init(string reset_kind = "HARD");
    // Enable edn, set modes
    ral.ctrl.edn_enable.set(cfg.enable);
    ral.ctrl.boot_req_mode.set(cfg.boot_req_mode);
    ral.ctrl.auto_req_mode.set(cfg.auto_req_mode);
    csr_update(.csr(ral.ctrl));
  endtask

  virtual task dut_shutdown();
    // check for pending edn operations and wait for them to complete
    // TODO
  endtask

endclass : edn_base_vseq
