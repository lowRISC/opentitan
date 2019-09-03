// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// CSR test class
class core_ibex_csr_test extends core_ibex_base_test;

  `uvm_component_utils(core_ibex_csr_test)
  `uvm_component_new

  virtual task wait_for_test_done();
    bit result;
    fork
    begin
      wait_for_mem_txn(cfg.signature_addr, TEST_RESULT);
      result = signature_data_q.pop_front();
      if (result == TEST_PASS) begin
        `uvm_info(`gfn, "CSR test completed successfully!", UVM_LOW)
      end else if (result == TEST_FAIL) begin
        `uvm_error(`gfn, "CSR TEST_FAILED!")
      end else begin
        `uvm_fatal(`gfn, "CSR test values are not configured properly")
      end
    end
    begin
      clk_vif.wait_clks(timeout_in_cycles);
      `uvm_fatal(`gfn, "TEST TIMEOUT!!")
    end
    join_any
  endtask

endclass

// Debug test class
class core_ibex_debug_intr_test extends core_ibex_base_test;

  `uvm_component_utils(core_ibex_debug_intr_test)
  `uvm_component_new

  virtual task send_stimulus();
    fork
      begin
        vseq.start(env.vseqr);
      end
      begin
        if (cfg.require_signature_addr) begin
          wait_for_core_status(INITIALIZED);
        end else begin
          // If no signature_addr functionality is desired, then the test will
          // simply wait for an adequate number of cycles
          clk_vif.wait_clks(stimulus_delay);
        end
        fork
          begin
            if (cfg.enable_irq_stress_seq) begin
              vseq.start_irq_stress_seq();
            end
          end
          begin
            if (cfg.enable_debug_stress_seq) begin
              vseq.start_debug_stress_seq();
            end
          end
        join_none
      end
    join_none
  endtask

endclass

// Debug WFI test class
class core_ibex_debug_wfi_test extends core_ibex_base_test;

  `uvm_component_utils(core_ibex_debug_wfi_test)
  `uvm_component_new

  virtual task send_stimulus();
    fork
      begin
        vseq.start(env.vseqr);
      end
      begin
        if (!cfg.require_signature_addr) begin
          clk_vif.wait_clks(stimulus_delay);
          fork
            begin
              if (cfg.enable_irq_stress_seq) begin
                vseq.start_irq_stress_seq();
              end
            end
            begin
              if (cfg.enable_debug_stress_seq) begin
                vseq.start_debug_stress_seq();
              end
            end
          join_none
        end else begin
          // Wait for core initialization before starting the wfi stimulus
          // loop - first write to signature address is guaranteed to be core
          // initialization info
          check_next_core_status(INITIALIZED, "Core initialization handshake failure");
          // TODO(udi) - need to check that no other instruction fetches occur
          // after the WFI is detected, and before any stimulus is sent to the
          // core
          forever begin
            wait (dut_vif.wfi === 1'b1);
            clk_vif.wait_clks($urandom_range(100));
            vseq.start_debug_single_seq();
            // After assserting this signal, core should wake up and jump into
            // debug mode from WFI state - next handshake should
            // be a notification that the core is now in debug mode
            check_next_core_status(IN_DEBUG_MODE, "Core did not jump into debug mode from WFI state");
            // We don't want to trigger debug stimulus for any WFI
            // instructions encountered inside the debug rom - those should
            // act as NOP instructions - so we wait until hitting the end of
            // the debug rom
            wait (dut_vif.dret === 1'b1);
          end
        end
      end
    join_none
  endtask

endclass
