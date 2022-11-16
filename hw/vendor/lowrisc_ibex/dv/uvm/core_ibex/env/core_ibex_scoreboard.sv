// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_scoreboard extends uvm_scoreboard;

  uvm_tlm_analysis_fifo #(ibex_rvfi_seq_item) rvfi_port;
  core_ibex_env_cfg                           cfg;

  // Events for Double-Fault detection
  uvm_event fault_threshold_consecutive_reached, fault_threshold_total_reached;

  `uvm_component_utils(core_ibex_scoreboard)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(core_ibex_env_cfg)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(get_full_name(), "Cannot get cfg")
    end
    rvfi_port  = new("rvfi_port_scoreboard", this);
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      double_fault_detector();
    join_none
  endtask

  task double_fault_detector();
    int unsigned double_fault_cnt_total = 0;
    int unsigned double_fault_cnt_consecutive = 0;
    bit          double_fault_pulse_seen = 1'b0;

    ibex_rvfi_seq_item rvfi_instr;

    fault_threshold_consecutive_reached = new();
    fault_threshold_total_reached = new();

    // There are two observable side-effects of a double fault in the Ibex:
    // - CPUCTRL.double_fault_seen is set to '1
    // - The top-level output double_fault_seen_o is asserted for one cycle

    fork
      // Increment a counter whenever a double_fault was indicated for the last
      // rvfi_seq_item created. When the counter reaches a threshold, create an event.
      begin
        forever begin
          rvfi_port.get(rvfi_instr);
          if (double_fault_pulse_seen) begin
            // There must have been a double_fault during the previous retired insn.
            double_fault_pulse_seen = 1'b0;
            double_fault_cnt_total++;
            double_fault_cnt_consecutive++;
          end else begin
            // Reset the consecutive counter.
            double_fault_cnt_consecutive = 0;
          end

          // Create an event if either counter reaches its threshold value, then reset the counter.
          if (double_fault_cnt_consecutive == cfg.double_fault_threshold_consecutive) begin
            fault_threshold_consecutive_reached.trigger();
            double_fault_cnt_consecutive = 0;
          end
          if (double_fault_cnt_total == cfg.double_fault_threshold_total) begin
            fault_threshold_total_reached.trigger();
            double_fault_cnt_total = 0;
          end

        end
      end
      // Latch the 'double_fault_seen_o' signal to catch the fault.
      // The single pulse may be receieved sometime before the rvfi_seq_item
      // corresponding to the faulting instruction is generated. Hence we
      // latch that pulse when it is seen, and then reset above when the
      // seq_item arrives.
      // https://github.com/lowRISC/ibex/pull/1848#discussion_r995903762
      begin
        forever begin
          @(posedge cfg.ibex_dut_vif.double_fault_seen);
          double_fault_pulse_seen = 1'b1;
          cfg.ibex_clk_vif.wait_clks(1);
        end
      end
    join_none

  endtask // double_fault_detector

  // Helper method which returns if either of the counter thresholds are reached.
  virtual task dfd_wait_for_pass_events();
    fork begin : isolation_fork
      fork
        begin
          fault_threshold_total_reached.wait_trigger();
          `uvm_info(`gfn,
                    $sformatf({"double_fault detector : reached threshold [%0d] ",
                               "for total double faults seen."}, cfg.double_fault_threshold_total),
                    UVM_LOW)
        end
        begin
          fault_threshold_consecutive_reached.wait_trigger();
          `uvm_info(`gfn,
                    $sformatf({"double_fault detector : reached threshold [%0d] ",
                               "for consecutive double faults seen."}, cfg.double_fault_threshold_consecutive),
                    UVM_LOW)
        end
      join_any
      disable fork;
    end join
  endtask

endclass
