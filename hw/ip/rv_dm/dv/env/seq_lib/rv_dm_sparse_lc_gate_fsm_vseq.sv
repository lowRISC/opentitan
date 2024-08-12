// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_sparse_lc_gate_fsm_vseq extends rv_dm_base_vseq;
  `uvm_object_utils(rv_dm_sparse_lc_gate_fsm_vseq)
  `uvm_object_new

  typedef enum { Sba, Rom } lc_idx_t;

  rand lc_idx_t tgt_gate;

  function string gate_path(lc_idx_t idx);
    case (idx)
      Sba: return "tb.dut.u_tlul_lc_gate_sba";
      Rom: return "tb.dut.u_tlul_lc_gate_rom";
      default: `uvm_fatal(`gfn, "Unknown enum value")
    endcase
  endfunction

  // Return the path to the FSM state register for the given gate.
  function string gate_fsm_path(lc_idx_t idx);
    return {gate_path(idx), ".state_q"};
  endfunction

  // Inject a fault to try to corrupt the gate FSM. Before this task, it will be at StError. When
  // the task completes, it will be at some invalid state.
  //
  // This uses uvm_hdl_deposit to "set" the FSM state. This will be permanent, as there is no FSM
  // edge from an invalid state to a valid one again.
  task force_fsm();
    logic [8:0] good_value, mask;
    string      path = gate_fsm_path(tgt_gate);

    // Disable some FSM state assertions that fail if we force the value of the FSM state without
    // the associated flop matching.
    $assertoff(0, "tb.dut.u_tlul_lc_gate_rom.u_state_regs_A");
    $assertoff(0, "tb.dut.u_tlul_lc_gate_sba.u_state_regs_A");

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)
    `DV_CHECK(uvm_hdl_read(path, good_value))
    `DV_CHECK(uvm_hdl_deposit(path, good_value ^ mask))

    // Wait a cycle to allow the FSM flop to catch up
    cfg.clk_rst_vif.wait_clks(1);

    // Re-enable the FSM state assertions which would have failed when the state FSM and flop didn't
    // match
    $asserton(0, "tb.dut.u_tlul_lc_gate_sba.u_state_regs_A");
    $asserton(0, "tb.dut.u_tlul_lc_gate_rom.u_state_regs_A");

    // Wait a while to make sure the FSM state stays "bad", to make sure there's no internal state
    // in tlul_lc_gate that might cause us to jump back to a good state.
    repeat (100) begin
      logic [8:0] cur_value;

      `DV_CHECK(uvm_hdl_read(path, cur_value))
      `DV_CHECK(cur_value == good_value ^ mask)

      cfg.clk_rst_vif.wait_clks(1);
    end
  endtask

  task body();
    // We expect forcing the FSM to trigger the "fatal_fault" alert. Tell the base vseq to allow it,
    // and spawn a background process that asserts it will appear.
    expect_fatal_alerts = 1'b1;
    check_fatal_alert_nonblocking("fatal_fault");

    // Force the FSM state
    force_fsm();
  endtask

endclass
