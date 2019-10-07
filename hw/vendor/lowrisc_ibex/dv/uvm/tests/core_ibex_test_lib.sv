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

// Performance counter test class
class core_ibex_perf_test extends core_ibex_base_test;

  `uvm_component_utils(core_ibex_perf_test)
  `uvm_component_new

  virtual task check_perf_stats();
    bit [63:0] num_cycles, num_instr_ret, num_cycles_lsu, num_cycles_if, num_loads, num_stores,
               num_jumps, num_branches, num_branches_taken, num_instr_ret_c;
    wait_for_csr_write(CSR_MCYCLE);
    num_cycles[31:0] = signature_data;
    wait_for_csr_write(CSR_MCYCLEH);
    num_cycles[63:32] = signature_data;
    wait_for_csr_write(CSR_MINSTRET);
    num_instr_ret[31:0] = signature_data;
    wait_for_csr_write(CSR_MINSTRETH);
    num_instr_ret[63:32] = signature_data;
    // mhpmcounter3
    wait_for_csr_write(12'hB03);
    num_cycles_lsu[31:0] = signature_data;
    // mhpmcounter4
    wait_for_csr_write(12'hB04);
    num_cycles_if[31:0] = signature_data;
    // mhpmcounter5
    wait_for_csr_write(12'hB05);
    num_loads[31:0] = signature_data;
    // mhpmcounter6
    wait_for_csr_write(12'hB06);
    num_stores[31:0] = signature_data;
    // mhpmcounter7
    wait_for_csr_write(12'hB07);
    num_jumps[31:0] = signature_data;
    // mhpmcounter8
    wait_for_csr_write(12'hB08);
    num_branches[31:0] = signature_data;
    // mhpmcounter9
    wait_for_csr_write(12'hB09);
    num_branches_taken[31:0] = signature_data;
    // mhpmcounter10
    wait_for_csr_write(12'hB0A);
    num_instr_ret_c[31:0] = signature_data;
    // mhpmcounterh3
    wait_for_csr_write(12'hB83);
    num_cycles_lsu[63:32] = signature_data;
    // mhpmcounterh4
    wait_for_csr_write(12'hB84);
    num_cycles_if[63:32] = signature_data;
    // mhpmcounterh5
    wait_for_csr_write(12'hB85);
    num_loads[63:32] = signature_data;
    // mhpmcounterh6
    wait_for_csr_write(12'hB86);
    num_stores[63:32] = signature_data;
    // mhpmcounterh7
    wait_for_csr_write(12'hB87);
    num_jumps[63:32] = signature_data;
    // mhpmcounterh8
    wait_for_csr_write(12'hB88);
    num_branches[63:32] = signature_data;
    // mhpmcounterh9
    wait_for_csr_write(12'hB89);
    num_branches_taken[63:32] = signature_data;
    // mhpmcounterh10
    wait_for_csr_write(12'hB8A);
    num_instr_ret_c[63:32] = signature_data;
    `uvm_info(`gfn, $sformatf("NUM_CYCLES: 0x%0x", num_cycles), UVM_LOW)
    `uvm_info(`gfn, $sformatf("NUM_INSTR_RET: 0x%0x", num_instr_ret), UVM_LOW)
    `uvm_info(`gfn, $sformatf("NUM_CYCLES_LSU: 0x%0x", num_cycles_lsu), UVM_LOW)
    `uvm_info(`gfn, $sformatf("NUM_CYCLES_IF: 0x%0x", num_cycles_if), UVM_LOW)
    `uvm_info(`gfn, $sformatf("NUM_LOADS: 0x%0x", num_loads), UVM_LOW)
    `uvm_info(`gfn, $sformatf("NUM_STORES: 0x%0x", num_stores), UVM_LOW)
    `uvm_info(`gfn, $sformatf("NUM_JUMPS: 0x%0x", num_jumps), UVM_LOW)
    `uvm_info(`gfn, $sformatf("NUM_BRANCHES: 0x%0x", num_branches), UVM_LOW)
    `uvm_info(`gfn, $sformatf("NUM_BRANCHES_TAKEN: 0x%0x", num_branches_taken), UVM_LOW)
    `uvm_info(`gfn, $sformatf("NUM_INSTR_RET_COMPRESSED: 0x%0x", num_instr_ret_c), UVM_LOW)
  endtask

endclass

// Debug test class
class core_ibex_debug_intr_basic_test extends core_ibex_base_test;

  `uvm_component_utils(core_ibex_debug_intr_basic_test)
  `uvm_component_new

  bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] core_init_mstatus;
  bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] core_init_mie;
  bit [$clog2(irq_agent_pkg::DATA_WIDTH)-1:0]   irq_id;

  virtual task send_stimulus();
    fork
      begin
        vseq.start(env.vseqr);
      end
      begin
        if (cfg.require_signature_addr) begin
          wait_for_core_setup();
        end else begin
          // If no signature_addr functionality is desired, then the test will simply wait for an
          // adequate number of cycles
          clk_vif.wait_clks(stimulus_delay);
        end
        fork
          begin
            if (cfg.enable_irq_seq) begin
              forever begin
                send_irq_stimulus();
              end
            end
          end
          begin
            if (cfg.enable_debug_stress_seq) begin
              send_debug_stimulus();
            end
          end
        join_none
      end
    join_none
  endtask

  virtual task wait_for_core_setup();
    wait_for_csr_write(CSR_MSTATUS);
    core_init_mstatus = signature_data;
    wait_for_csr_write(CSR_MIE);
    core_init_mie = signature_data;
    check_next_core_status(INITIALIZED, "Core initialization handshake failure");
  endtask

  // TODO(udi) - much of this checking logic is based on the current design only implementing
  // MACHINE_MODE, the checking will have to be modified once USER_MODE is implemented and merged,
  // e.g. need to also check mideleg for correct privilege mode context switch
  virtual task send_irq_stimulus();
    irq_seq_item                                  irq_txn;
    bit [irq_agent_pkg::DATA_WIDTH-1:0]           irq;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mstatus;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mcause;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mip;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mie;
    // send the interrupt
    vseq.start_irq_single_seq();
    irq_collected_port.get(irq_txn);
    irq = {irq_txn.irq_nm, irq_txn.irq_fast, 4'b0, irq_txn.irq_external, 3'b0,
           irq_txn.irq_timer, 3'b0, irq_txn.irq_software, 3'b0};
    // Get the bit position of the highest priority interrupt - ibex will only handle this one if
    // there are multiple irqs asserted at once
    irq_id = get_max_irq_id(irq);
    // If the interrupt is maskable, and the corresponding bit in MIE is not set, skip the next
    // checks, as it means the interrupt in question is not enabled by Ibex, and drop the interrupt
    // lines to avoid locking up the simulation
    if (!irq_txn.irq_nm && !core_init_mie[irq_id]) begin
      vseq.start_irq_drop_seq();
      irq_collected_port.get(irq_txn);
      irq = {irq_txn.irq_nm, irq_txn.irq_fast, 4'b0, irq_txn.irq_external, 3'b0,
             irq_txn.irq_timer, 3'b0, irq_txn.irq_software, 3'b0};
      `DV_CHECK_EQ_FATAL(irq, 0, "Interrupt lines have not been dropped")
      return;
    end
    check_next_core_status(HANDLING_IRQ, "Core did not jump to vectored interrupt handler");
    // check mstatus
    wait_for_csr_write(CSR_MSTATUS);
    mstatus = signature_data;
    `DV_CHECK_EQ_FATAL(mstatus[12:11], PRIV_LVL_M, "Incorrect privilege mode")
    `DV_CHECK_EQ_FATAL(mstatus[7], 1'b1, "mstatus.mpie was not set to 1'b1 after entering handler")
    `DV_CHECK_EQ_FATAL(mstatus[3], 1'b0, "mstatus.mie was not set to 1'b0 after entering handler")
    // check mcause against the interrupt id
    wait_for_csr_write(CSR_MCAUSE);
    mcause = signature_data;
    // check that mcause.interrupt is set
    `DV_CHECK_EQ_FATAL(mcause[ibex_mem_intf_agent_pkg::DATA_WIDTH-1], 1'b1,
                       "mcause.interrupt is not set to 1'b1")
    // check that mcause.exception_code matches the current interrupt's ID
    `DV_CHECK_EQ_FATAL(mcause[ibex_mem_intf_agent_pkg::DATA_WIDTH-2:0], irq_id,
                       "mcause.exception_code is encoding the wrong interrupt type")
    // Wait for MIE and MIP to be written regardless of what interrupt ibex is dealing with, to
    // prevent the case where MIP/MIE stays at 0 due to a nonmaskable interrupt, which will falsely
    // trigger the following call of check_next_core_status()
    wait_for_csr_write(CSR_MIE);
    mie = signature_data;
    wait_for_csr_write(CSR_MIP);
    mip = signature_data;
    // only check mip, and mie if the interrupt is not irq_nm, as Ibex's implementation of MIP and
    // MIE CSRs do not contain a bit for irq_nm
    if (!irq_txn.irq_nm) begin
      // check that the proper bit in MIE is high
      `DV_CHECK_EQ_FATAL(mie[irq_id], 1'b1,
          $sformatf("mie[%0d] is not set, but core responded to corresponding interrupt", irq_id))
      // check that the proper bit in MIP is high
      `DV_CHECK_EQ_FATAL(mip[irq_id], 1'b1,
          $sformatf("mip[%0d] is not set, but core responded to corresponding interrupt", irq_id))
    end
    // As Ibex interrupts are level sensitive, core must write to memory mapped address to
    // indicate that irq stimulus be dropped
    check_next_core_status(FINISHED_IRQ, "Core did not signal end of interrupt properly");
    // Will receive irq_seq_item indicating that lines have been dropped
    vseq.start_irq_drop_seq();
    irq_collected_port.get(irq_txn);
    irq = {irq_txn.irq_nm, irq_txn.irq_fast, 4'b0, irq_txn.irq_external, 3'b0,
           irq_txn.irq_timer, 3'b0, irq_txn.irq_software, 3'b0};
    `DV_CHECK_EQ_FATAL(irq, 0, "Interrupt lines have not been dropped")
    wait (dut_vif.mret === 1'b1);
  endtask

  function int get_max_irq_id(bit [irq_agent_pkg::DATA_WIDTH-1:0] irq);
    int i;
    for (i = irq_agent_pkg::DATA_WIDTH-1; i >= 0; i = i - 1) begin
      if (irq[i] === 1'b1) begin
        return i;
        break;
      end
    end
  endfunction

  // Basic debug stimulus check for Ibex for debug stimulus stress tests: check that Ibex enters
  // debug mode properly after stimulus is sent and then check that a dret is encountered signifying
  // the end of debug mode.
  virtual task send_debug_stimulus();
    fork
      begin
        vseq.start_debug_stress_seq();
      end
      begin
        forever begin
          wait_for_core_status(IN_DEBUG_MODE);
          wait(dut_vif.dret === 1'b1);
        end
      end
    join_none
  endtask

endclass

// Base class for directed debug and irq test scenarios
class core_ibex_directed_test extends core_ibex_debug_intr_basic_test;

  `uvm_component_utils(core_ibex_directed_test)
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
              if (cfg.enable_irq_seq) begin
                forever begin
                  send_irq_stimulus();
                end
              end
            end
            begin
              if (cfg.enable_debug_stress_seq) begin
                send_debug_stimulus();
              end
            end
          join_none
        end else begin
          // Wait for core initialization before starting the stimulus check loop - first write
          // to signature address is guaranteed to be core initialization info
          wait_for_core_setup();
          // Should be extended by derived classes.
          // DO NOT use this test class directly.
          fork
            begin : stimulus
              check_stimulus();
            end : stimulus
            begin
              wait(dut_vif.ecall === 1'b1);
              disable stimulus;
            end
          join
        end
      end
    join_none
  endtask

  virtual task check_stimulus();
    `uvm_fatal(`gfn, "Base class task should not be used")
  endtask

  //------------------------------------------------------
  // Checker functions/tasks that might be commonly used
  //------------------------------------------------------

  // compares dcsr.ebreak against the privilege mode encoded in dcsr.prv
  virtual function check_dcsr_ebreak();
    // dcsr.prv is the bottom two bits.
    case (signature_data[1:0])
      2'b11: begin
        `DV_CHECK_EQ_FATAL(signature_data[15], 1'b1, "dcsr.ebreakm is not set")
      end
      2'b01: begin
        `DV_CHECK_EQ_FATAL(signature_data[13], 1'b1, "dcsr.ebreaks is not set")
      end
      2'b00: begin
        `DV_CHECK_EQ_FATAL(signature_data[12], 1'b1, "dcsr.ebreaku is not set")
      end
      default: begin
        `uvm_fatal(`gfn, "dcsr.prv is an unsupported privilege mode")
      end
    endcase
  endfunction

  virtual function check_dcsr_cause(dbg_cause_e cause);
    `DV_CHECK_EQ_FATAL(cause, signature_data[8:6], "dcsr.cause has been incorrectly updated")
  endfunction

endclass

// Debug WFI test class
class core_ibex_debug_wfi_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_wfi_test)
  `uvm_component_new

  virtual task check_stimulus();
    // TODO(udi) - need to check that no other instruction fetches occur after after the WFI
    // is detected, and before any stimulus is sent to the core
    forever begin
      wait (dut_vif.wfi === 1'b1);
      wait (dut_vif.core_sleep === 1'b1);
      clk_vif.wait_clks($urandom_range(100));
      vseq.start_debug_single_seq();
      // After assserting this signal, core should wake up and jump into debug mode from WFI state
      // - next handshake should be a notification that the core is now in debug mode
      check_next_core_status(IN_DEBUG_MODE, "Core did not jump into debug mode from WFI state");
      // We don't want to trigger debug stimulus for any WFI instructions encountered inside the
      // debug rom - those should act as NOP instructions - so we wait until hitting the end of the
      // debug rom.
      // We also want to check that dcsr.cause has been set correctly
      wait_for_csr_write(CSR_DCSR);
      check_dcsr_cause(DBG_CAUSE_HALTREQ);
      wait (dut_vif.dret === 1'b1);
    end
  endtask

endclass

// DRET test class
class core_ibex_dret_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_dret_test)
  `uvm_component_new

  virtual task check_stimulus();
    forever begin
      wait (dut_vif.dret === 1'b1);
      // After hitting a dret, the core will jump to the vectored trap handler, which sends a
      // handshake write to the bench
      check_next_core_status(HANDLING_EXCEPTION, "Core did not jump to vectored exception handler");
      // The core will receive an illegal instruction handshake after jumping from the vectored trap
      // handler to the illegal instruction exception handler
      check_next_core_status(ILLEGAL_INSTR_EXCEPTION,
                             "Core did not treat dret like illegal instruction");
    end
  endtask

endclass

// Normal debug ebreak test class
class core_ibex_debug_ebreak_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_ebreak_test)
  `uvm_component_new

  bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] dpc;
  bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] dcsr;

  virtual task check_stimulus();
    forever begin
      wait (dut_vif.ebreak === 1'b1);
      check_next_core_status(HANDLING_EXCEPTION, "Core did not jump to exception handler");
      check_next_core_status(EBREAK_EXCEPTION,
                             "Core did not jump from exception handler to ebreak handler");
      wait (dut_vif.mret === 1'b1);
      // Want to wait until after the ebreak handler has finished to send debug stimulus, to avoid
      // nested trap scenarios
      clk_vif.wait_clks($urandom_range(5, 11));
      vseq.start_debug_single_seq();
      // capture the first write of dcsr
      wait_for_csr_write(CSR_DCSR);
      dcsr = signature_data;
      // We also want to check that dcsr.cause has been set correctly
      check_dcsr_cause(DBG_CAUSE_HALTREQ);
      // capture the first write of dpc
      wait_for_csr_write(CSR_DPC);
      dpc = signature_data;
      check_next_core_status(IN_DEBUG_MODE, "Core did not properly jump into debug mode");
      wait (dut_vif.ebreak === 1'b1);
      // compare the second writes of dcsr and dpc against the captured values
      wait_for_csr_write(CSR_DCSR);
      `DV_CHECK_EQ_FATAL(dcsr, signature_data,
                         "ebreak inside the debug rom has changed the value of DCSR")
      wait_for_csr_write(CSR_DPC);
      `DV_CHECK_EQ_FATAL(dpc, signature_data,
                         "ebreak inside the debug rom has changed the value of DPC")
      wait (dut_vif.dret === 1'b1);
    end
  endtask

endclass

// Debug ebreak test with dcsr.ebreak(m/s/u) set
class core_ibex_debug_ebreakm_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_ebreakm_test)
  `uvm_component_new

  virtual task check_stimulus();
    // send a single debug request after core initialization to configure dcsr
    vseq.start_debug_single_seq();
    check_next_core_status(IN_DEBUG_MODE,
                           "Core did not enter debug mode after debug_req stimulus");
    // Read dcsr and verify the appropriate ebreak(m/s/u) bit has been set based on the prv field,
    // as well as the cause field
    wait_for_csr_write(CSR_DCSR);
    check_dcsr_ebreak();
    check_dcsr_cause(DBG_CAUSE_HALTREQ);
    wait (dut_vif.dret === 1'b1);
    forever begin
      wait (dut_vif.ebreak === 1'b1);
      check_next_core_status(IN_DEBUG_MODE,
                             "Core did not enter debug mode after execution of ebreak");
      // Read dcsr and verify the appropriate ebreak(m/s/u) bit has been set based on the prv field
      wait_for_csr_write(CSR_DCSR);
      check_dcsr_ebreak();
      check_dcsr_cause(DBG_CAUSE_EBREAK);
      wait (dut_vif.dret === 1'b1);
    end
  endtask

endclass

// Debug single step test
class core_ibex_debug_single_step_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_single_step_test)
  `uvm_component_new

  virtual task check_stimulus();
    bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] ret_pc;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] counter = 0;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] next_counter = 0;
    forever begin
      vseq.start_debug_single_seq();
      check_next_core_status(IN_DEBUG_MODE,
                             "Core did not enter debug mode after debug stimulus");
      wait_for_csr_write(CSR_DPC);
      ret_pc = signature_data;
      wait_for_csr_write(CSR_DSCRATCH0);
      next_counter = signature_data;
      wait_for_csr_write(CSR_DCSR);
      check_dcsr_cause(DBG_CAUSE_HALTREQ);
      `DV_CHECK_EQ_FATAL(signature_data[1], 1'b1, "dcsr.step is not set")
      wait(dut_vif.dret === 1'b1);
      // now we loop on the counter until we are done single stepping
      while (counter >= 0) begin
        counter = next_counter;
        check_next_core_status(IN_DEBUG_MODE,
                               "Core did not enter debug mode after debug stimulus");
        wait_for_csr_write(CSR_DPC);
        if (signature_data - ret_pc !== 'h2 &&
            signature_data - ret_pc !== 'h4) begin
          `uvm_fatal(`gfn, $sformatf("DPC value [0x%0x] is not the next instruction after ret_pc [0x%0x]",
                             signature_data, ret_pc))
        end
        ret_pc = signature_data;
        wait_for_csr_write(CSR_DSCRATCH0);
        next_counter = signature_data;
        wait_for_csr_write(CSR_DCSR);
        check_dcsr_cause(DBG_CAUSE_STEP);
        if (counter === 0) begin
          `DV_CHECK_EQ_FATAL(signature_data[2], 1'b0, "dcsr.step is set")
        end else begin
          `DV_CHECK_EQ_FATAL(signature_data[2], 1'b1, "dcsr.step is not set")
        end
        wait(dut_vif.dret === 1'b1);
        if (counter === 0) break;
      end
      clk_vif.wait_clks(2000);
    end
  endtask

endclass

// Memory interface error test class
class core_ibex_mem_error_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_mem_error_test)
  `uvm_component_new

  int err_delay;

  // check memory error inputs and verify that core jumps to correct exception handler
  // TODO(udinator) - add checks for the RVFI interface
  virtual task check_stimulus();
    forever begin
      while (!vseq.data_intf_seq.get_error_synch()) begin
        clk_vif.wait_clks(1);
      end
      vseq.data_intf_seq.inject_error();
      `uvm_info(`gfn, "Injected dmem error", UVM_LOW)
      // Dmem interface error could be either a load or store operation
      check_mem_fault(1'b1);
      // Random delay before injecting instruction fetch fault
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_delay, err_delay inside { [25:100] };)
      clk_vif.wait_clks(err_delay);
      while (!vseq.instr_intf_seq.get_error_synch()) begin
        clk_vif.wait_clks(1);
      end
      `uvm_info(`gfn, "Injecting imem fault", UVM_LOW)
      vseq.instr_intf_seq.inject_error();
      check_mem_fault(1'b0);
      // Random delay before injecting this series of errors again
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_delay, err_delay inside { [250:750] };)
      clk_vif.wait_clks(err_delay);
    end
  endtask

  virtual task check_mem_fault(bit imem_or_dmem);
    bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mcause;
    core_status_t mem_status;
    ibex_pkg::exc_cause_e exc_type;
    check_next_core_status(HANDLING_EXCEPTION, "Core did not jump to exception handler");
    if (imem_or_dmem) begin
      // Next write of CORE_STATUS will be the load/store fault type
      wait_for_mem_txn(cfg.signature_addr, CORE_STATUS);
      mem_status = signature_data_q.pop_front();
      if (mem_status == LOAD_FAULT_EXCEPTION) begin
        exc_type = EXC_CAUSE_LOAD_ACCESS_FAULT;
      end else if (mem_status == STORE_FAULT_EXCEPTION) begin
        exc_type = EXC_CAUSE_STORE_ACCESS_FAULT;
      end
      `uvm_info(`gfn, $sformatf("0x%0x", exc_type), UVM_LOW)
    end else begin
      check_next_core_status(INSTR_FAULT_EXCEPTION, "Core did not register correct memory fault type");
      exc_type = EXC_CAUSE_INSTR_ACCESS_FAULT;
    end
    wait_for_csr_write(CSR_MCAUSE);
    mcause = signature_data;
    `DV_CHECK_EQ_FATAL(mcause[ibex_mem_intf_agent_pkg::DATA_WIDTH-1], 1'b0,
                       "mcause interrupt is not set to 1'b0")
    `DV_CHECK_EQ_FATAL(mcause[ibex_mem_intf_agent_pkg::DATA_WIDTH-2:0],
                       exc_type,
                       "mcause.exception_code is encoding the wrong exception type")
    wait(dut_vif.mret === 1'b1);
    `uvm_info(`gfn, "exiting mem fault checker", UVM_LOW)
  endtask

endclass
