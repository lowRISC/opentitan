// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_base_vseq extends cip_base_vseq #(
    .RAL_T               (entropy_src_reg_block),
    .CFG_T               (entropy_src_env_cfg),
    .COV_T               (entropy_src_env_cov),
    .VIRTUAL_SEQUENCER_T (entropy_src_virtual_sequencer)
  );
  `uvm_object_utils(entropy_src_base_vseq)

  rand bit [3:0]   rng_val;
  rand uint        num_reqs;
  push_pull_host_seq#(entropy_src_pkg::RNG_BUS_WIDTH)          m_rng_push_seq;
  push_pull_host_seq#(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)   m_csrng_pull_seq;

  // various knobs to enable certain routines
  bit  do_entropy_src_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_entropy_src_init) entropy_src_init();
  endtask

  virtual task dut_shutdown();
    // check for pending entropy_src operations and wait for them to complete
    // TODO
  endtask

  // setup basic entropy_src features
  virtual task entropy_src_init();
    // Set fuse
    cfg.efuse_es_sw_reg_en_vif.drive_pin(.idx(0), .val(cfg.efuse_es_sw_reg_en));

    // Set entropy_src controls
    ral.entropy_control.es_type.set(cfg.type_bypass);
    ral.entropy_control.es_route.set(cfg.route_software);
    csr_update(.csr(ral.entropy_control));

    // Enable entropy_src in ptrng or lfsr mode
    ral.conf.enable.set(cfg.mode);
    ral.conf.boot_bypass_disable.set(cfg.boot_bypass_disable);
    csr_update(.csr(ral.conf));

  endtask

endclass : entropy_src_base_vseq
