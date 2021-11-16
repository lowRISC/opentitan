// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests the "execute from SRAM" feature - TL transactions tagged as InstrType are
// allowed to be executed by the SRAM if configured properly.
//
// This sequence fully randomizes this configuration setting and randomly updates the configuration
// in parallel with the main sequence body.
// The scoreboard will handle all checks to ensure that transactions are dropped as necessary.
class sram_ctrl_executable_vseq extends sram_ctrl_multiple_keys_vseq;

  `uvm_object_utils(sram_ctrl_executable_vseq)
  `uvm_object_new

  virtual task pre_start();
    en_ifetch = 1;
    super.pre_start();
  endtask

  task req_mem_init();
    super.req_mem_init();
    randomize_and_drive_ifetch_en();
  endtask

  task randomize_and_drive_ifetch_en();
    mubi8_e en_sram_ifetch = get_rand_mubi8_val();
    mubi4_e en_exec_csr = get_rand_mubi4_val();
    lc_ctrl_pkg::lc_tx_e hw_debug_en = get_rand_lc_tx_val();

    `uvm_info(`gfn, $sformatf("en_exec_csr: 0b%0b", en_exec_csr), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("en_sram_ifetch: 0b%0b", en_sram_ifetch), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("hw_debug_en: 0b%0b",  hw_debug_en), UVM_HIGH)

    csr_wr(ral.exec, en_exec_csr);
    cfg.exec_vif.drive_lc_hw_debug_en(hw_debug_en);
    cfg.exec_vif.drive_otp_en_sram_ifetch(en_sram_ifetch);
  endtask

endclass
