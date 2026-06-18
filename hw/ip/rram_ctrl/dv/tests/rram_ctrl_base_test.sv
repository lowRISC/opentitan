// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_base_test extends cip_base_test #(
    .CFG_T(rram_ctrl_env_cfg),
    .ENV_T(rram_ctrl_env)
  );

  `uvm_component_utils(rram_ctrl_base_test)

  // The base class dv_base_test creates the following instances:
  //   - rram_ctrl_env_cfg: cfg
  //   - rram_ctrl_env:     env

  // The base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in the run_phase.
  // As such, nothing more needs to be done

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);

  // Add rram_ctrl only plusarg
  extern function void build_phase(uvm_phase phase);

endclass : rram_ctrl_base_test


function rram_ctrl_base_test::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void rram_ctrl_base_test::build_phase(uvm_phase phase);
  super.build_phase(phase);

  void'($value$plusargs("scr_en_pct=%0d", cfg.scr_en_pct));
  void'($value$plusargs("reg_en_pct=%0d", cfg.reg_en_pct));
  void'($value$plusargs("wr_en_pct=%0d",  cfg.wr_en_pct));
  void'($value$plusargs("rd_en_pct=%0d",  cfg.rd_en_pct));
  void'($value$plusargs("ecc_en_pct=%0d", cfg.ecc_en_pct));

  void'($value$plusargs("skip_init_data_array=%0b", cfg.skip_init_data_array));
  void'($value$plusargs("skip_init_info_array=%0b", cfg.skip_init_info_array));
  void'($value$plusargs("skip_lc_init=%0b", cfg.skip_lc_init));

endfunction
