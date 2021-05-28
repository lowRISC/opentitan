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
      collect_start();
      collect_done();
      // TODO: Only run when coverage is enabled.
      collect_insns();
    join
  endtask

  protected task collect_start();
    otbn_model_item trans;

    forever begin
      // Collect transactions on each clock edge when reset is high.
      @(posedge cfg.vif.clk_i);
      if (cfg.vif.rst_ni === 1'b1) begin
        if (cfg.vif.start) begin
          trans = otbn_model_item::type_id::create("trans");
          trans.item_type = OtbnModelStart;
          trans.err       = 0;
          trans.mnemonic  = "";
          analysis_port.write(trans);
        end
      end
    end
  endtask

  protected task collect_done();
    otbn_model_item trans;

    forever begin
      // wait until vif signals done (or we are in reset)
      cfg.vif.wait_done();

      if (cfg.vif.rst_ni === 1'b1) begin
        // We aren't in reset, so we've just seen the done signal go high.
        trans = otbn_model_item::type_id::create("trans");
        trans.item_type = OtbnModelDone;
        trans.err       = cfg.vif.err;
        trans.mnemonic  = "";
        analysis_port.write(trans);
        cfg.vif.wait_not_done();
      end else begin
        // We are in reset. Wait until we aren't (we need to do this because wait_done() returns
        // immediately in reset)
        wait(cfg.vif.rst_ni);
      end
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
      @(posedge cfg.vif.clk_i);
      if (cfg.vif.rst_ni === 1'b1) begin
        // Ask the trace checker for any ISS instruction that has come in since last cycle.
        if (otbn_trace_checker_pop_iss_insn(insn_addr, insn_mnemonic)) begin
          trans = otbn_model_item::type_id::create("trans");
          trans.item_type = OtbnModelInsn;
          trans.err       = 0;
          trans.insn_addr = insn_addr;
          trans.mnemonic  = insn_mnemonic;
          analysis_port.write(trans);
        end
      end
    end
  endtask

endclass
