// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class cip_base_test #(type CFG_T = cip_base_env_cfg,
                      type ENV_T = cip_base_env) extends dv_base_test #(CFG_T, ENV_T);
  `uvm_component_param_utils(cip_base_test #(CFG_T, ENV_T))

  `uvm_component_new

  virtual function void add_message_demotes(dv_report_catcher catcher);
    string msg;
    bit create_jtag_riscv_map;
    super.add_message_demotes(catcher);

    // Cannot use `cfg` because it has not been created.
    void'($value$plusargs("create_jtag_riscv_map=%0b", create_jtag_riscv_map));
    if (create_jtag_riscv_map) begin
      // Demote address maps warnings
      msg = "\s*map .* does not seem to be initialized correctly.*";
      catcher.add_change_sev("RegModel", msg, UVM_INFO);
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    // Disable random delays in specific `prim_cdc_rand_delay`s even if CDC instrumentation is
    // enabled.  (See `cip_base_env_cfg` for details.)
    foreach (cfg.disabled_prim_cdc_rand_delays[i]) begin
      string path = {cfg.disabled_prim_cdc_rand_delays[i],
                     ".gen_enable.cdc_instrumentation_enabled"};
      `DV_CHECK(uvm_hdl_force(path, 1'b0));
    end
    super.run_phase(phase);
  endtask

endclass : cip_base_test
