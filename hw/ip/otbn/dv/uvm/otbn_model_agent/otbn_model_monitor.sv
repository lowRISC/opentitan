// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// The monitor watches the otbn_model_if and reports responses from the model
//

class otbn_model_monitor extends dv_base_monitor #(
    .ITEM_T (otbn_model_item),
    .CFG_T  (otbn_model_agent_cfg)
  );
  `uvm_component_utils(otbn_model_monitor)

  // the base class provides the following handles for use:
  // otbn_model_agent_cfg: cfg
  // otbn_model_agent_cov: cov
  // uvm_analysis_port #(otbn_model_item): analysis_port

  `uvm_component_new

  protected task collect_trans(uvm_phase phase);
    fork
      collect_status();
      collect_insns();
    join
  endtask

  protected task collect_status();
    otbn_model_item trans;

    forever begin
      trans = otbn_model_item::type_id::create("trans");

      // Wait until vif signals a change in status (or we are in reset)
      cfg.vif.wait_status();

      // Store value of reset before we wait for it to be released (if it is not already).
      trans.rst_n = cfg.vif.rst_ni;

      if (cfg.vif.rst_ni !== 1'b1) begin
        // We are in reset. Wait until we aren't (we need to do this because wait_status() returns
        // immediately in reset)
        wait(cfg.vif.rst_ni);
      end

      trans.item_type = OtbnModelStatus;
      trans.status    = cfg.vif.status;
      trans.err       = cfg.vif.err;
      trans.err_bits  = cfg.vif.err_bits;
      trans.mnemonic  = "";
      analysis_port.write(trans);
    end
  endtask

  protected task collect_insns();
    otbn_model_item trans;

    bit [31:0] insn_addr;
    string     insn_mnemonic;

    // OtbnModelInsn items are only used for coverage collection; disable their detection if
    // coverage is not enabled.
    if (!cfg.en_cov) begin
      return;
    end

    // Collect transactions on each clock edge when we are not in reset
    forever begin
      // Use a clocking block to ensure we sample after the always_ff code in otbn_core_model.sv has
      // run. This means that we'll immediately see any instructions that executed. Without it, we'd
      // be racing against that logic, which might mean we saw the instructions a cycle later. In
      // that case, a final instruction gets spotted after we see the status go back to idle
      // (causing errors in the scoreboard, which doesn't expect to see instructions executing when
      // idle).
      @cfg.vif.cb;

      if (cfg.vif.rst_ni === 1'b1) begin
        // Ask the trace checker for any ISS instruction that has come in since last cycle.
        if (otbn_trace_checker_pop_iss_insn(insn_addr, insn_mnemonic)) begin
          trans = otbn_model_item::type_id::create("trans");
          trans.item_type = OtbnModelInsn;
          trans.status    = 0;
          trans.err       = 0;
          trans.insn_addr = insn_addr;
          trans.mnemonic  = insn_mnemonic;
          analysis_port.write(trans);
        end
      end
    end
  endtask

endclass
