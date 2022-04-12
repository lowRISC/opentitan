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

// Reset test
class core_ibex_reset_test extends core_ibex_base_test;

  `uvm_component_utils(core_ibex_reset_test)
  `uvm_component_new

  bit [5:0] num_reset;

  virtual task send_stimulus();
    vseq.start(env.vseqr);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(num_reset, num_reset > 20;)
    for (int i = 0; i < num_reset; i = i + 1) begin
      // Mid-test reset is possible in a wide range of times
      clk_vif.wait_clks($urandom_range(0, 50000));
      fork
        begin
          dut_vif.dut_cb.fetch_enable <= ibex_pkg::FetchEnableOff;
          clk_vif.apply_reset(.reset_width_clks (100));
        end
        begin
          clk_vif.wait_clks(1);
          // Flush FIFOs
          item_collected_port.flush();
          irq_collected_port.flush();
          // Reset testbench state
          env.reset();
          load_binary_to_mem();
        end
      join
      // Assert fetch_enable to have the core start executing from boot address
      dut_vif.dut_cb.fetch_enable <= ibex_pkg::FetchEnableOn;
    end
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
    wait_for_csr_write(CSR_MHPMCOUNTER3);
    num_cycles_lsu[31:0] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER4);
    num_cycles_if[31:0] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER5);
    num_loads[31:0] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER6);
    num_stores[31:0] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER7);
    num_jumps[31:0] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER8);
    num_branches[31:0] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER9);
    num_branches_taken[31:0] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER10);
    num_instr_ret_c[31:0] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER3H);
    num_cycles_lsu[63:32] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER4H);
    num_cycles_if[63:32] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER5H);
    num_loads[63:32] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER6H);
    num_stores[63:32] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER7H);
    num_jumps[63:32] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER8H);
    num_branches[63:32] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER9H);
    num_branches_taken[63:32] = signature_data;
    wait_for_csr_write(CSR_MHPMCOUNTER10H);
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
  priv_lvl_e                                    init_operating_mode;
  priv_lvl_e                                    operating_mode;
  bit [$clog2(irq_agent_pkg::DATA_WIDTH)-1:0]   irq_id;
  irq_seq_item                                  irq_txn;
  bit [irq_agent_pkg::DATA_WIDTH-1:0]           irq;
  bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mstatus;
  bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mcause;
  bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mip;
  bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mie;
  bit                                           in_nested_trap;

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
            if (enable_irq_seq) begin
              forever begin
                send_irq_stimulus();
              end
            end
          end
          begin
            if (cfg.enable_debug_seq) begin
              stress_debug();
            end
          end
        join_none
      end
    join_none
  endtask

  function priv_lvl_e select_mode();
    if (in_nested_trap) return operating_mode;
    else return init_operating_mode;
  endfunction

  virtual task wait_for_core_setup();
    wait_for_csr_write(CSR_MSTATUS, 10000);
    core_init_mstatus = signature_data;
    // capture the initial privilege mode ibex will boot into
    init_operating_mode = priv_lvl_e'(core_init_mstatus[12:11]);
    wait_for_csr_write(CSR_MIE, 5000);
    core_init_mie = signature_data;
    check_next_core_status(INITIALIZED, "Core initialization handshake failure", 5000);
  endtask

  function bit determine_irq_from_txn();
    bit irq_valid;

    irq = {irq_txn.irq_nm, irq_txn.irq_fast, 4'b0, irq_txn.irq_external, 3'b0,
           irq_txn.irq_timer, 3'b0, irq_txn.irq_software, 3'b0};
    `uvm_info(`gfn, $sformatf("irq: 0x%0x", irq), UVM_LOW)

    irq_valid = get_valid_irq_id(irq);
    `uvm_info(`gfn, $sformatf("irq_id: 0x%0x", irq_id), UVM_LOW)

    return irq_valid;
  endfunction

  virtual task send_irq_stimulus_start(input bit no_nmi,
                                       input bit no_fast,
                                       output bit ret_val);
    // send the interrupt
    if (cfg.enable_irq_single_seq)        vseq.start_irq_raise_single_seq(no_nmi, no_fast);
    else if (cfg.enable_irq_multiple_seq) vseq.start_irq_raise_seq(no_nmi, no_fast);

    send_irq_stimulus_inner(ret_val);
  endtask

  virtual task send_nmi_stimulus_start(output bit ret_val);
    vseq.start_nmi_raise_seq();
    send_irq_stimulus_inner(ret_val);
  endtask

  virtual task send_irq_stimulus_inner(output bit ret_val);
    bit irq_valid;
    irq_collected_port.get(irq_txn);
    // Get the bit position of the highest priority interrupt - ibex will only handle this one if
    // there are multiple irqs asserted at once.
    irq_valid = determine_irq_from_txn();
    // If the interrupt is maskable, and the corresponding bit in MIE is not set, skip the next
    // checks, as it means the interrupt in question is not enabled by Ibex, and drop the interrupt
    // lines to avoid locking up the simulation.
    if (!irq_valid) begin
      vseq.start_irq_drop_seq();
      irq_collected_port.get(irq_txn);
      determine_irq_from_txn();
      `DV_CHECK_EQ_FATAL(irq, 0, "Interrupt lines have not been dropped")
      ret_val = irq_valid;
      return;
    end

    check_irq_handle();

    ret_val = irq_valid;
  endtask

  virtual task check_irq_handle();
    check_next_core_status(HANDLING_IRQ, "Core did not jump to vectored interrupt handler", 750);
    check_priv_mode(PRIV_LVL_M);
    operating_mode = dut_vif.dut_cb.priv_mode;
    // check mstatus
    wait_for_csr_write(CSR_MSTATUS, 500);
    mstatus = signature_data;
    `DV_CHECK_EQ_FATAL(mstatus[12:11], select_mode(), "Incorrect mstatus.mpp")
    `DV_CHECK_EQ_FATAL(mstatus[7], 1'b1, "mstatus.mpie was not set to 1'b1 after entering handler")
    `DV_CHECK_EQ_FATAL(mstatus[3], 1'b0, "mstatus.mie was not set to 1'b0 after entering handler")
    // check mcause against the interrupt id
    check_mcause(1'b1, irq_id);
    // Wait for MIE and MIP to be written regardless of what interrupt ibex is dealing with, to
    // prevent the case where MIP/MIE stays at 0 due to a nonmaskable interrupt, which will falsely
    // trigger the following call of check_next_core_status()
    wait_for_csr_write(CSR_MIE, 500);
    mie = signature_data;
    wait_for_csr_write(CSR_MIP, 500);
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
  endtask

  virtual task send_irq_stimulus_end();
    // As Ibex interrupts are level sensitive, core must write to memory mapped address to
    // indicate that irq stimulus be dropped
    check_next_core_status(FINISHED_IRQ, "Core did not signal end of interrupt properly", 300);
    // Will receive irq_seq_item indicating that lines have been dropped
    vseq.start_irq_drop_seq();
    // Want to skip this .get() call on the second MRET of nested interrupt scenarios
    if (!(cfg.enable_nested_irq && !in_nested_trap)) begin
      irq_collected_port.get(irq_txn);
      irq = {irq_txn.irq_nm, irq_txn.irq_fast, 4'b0, irq_txn.irq_external, 3'b0,
             irq_txn.irq_timer, 3'b0, irq_txn.irq_software, 3'b0};
      `DV_CHECK_EQ_FATAL(irq, 0, "Interrupt lines have not been dropped")
    end
    wait_ret("mret", 1000);
  endtask

  virtual task send_irq_stimulus(bit no_nmi = 1'b0, bit no_fast = 1'b0);
    bit ret_val;
    send_irq_stimulus_start(no_nmi, no_fast, ret_val);
    if (ret_val) send_irq_stimulus_end();
  endtask

  virtual task send_nmi_stimulus();
    bit ret_val;
    send_nmi_stimulus_start(ret_val);
    if (ret_val) send_irq_stimulus_end();
  endtask

  function int get_valid_irq_id(bit [irq_agent_pkg::DATA_WIDTH-1:0] irq);
    int i;
    bit have_irq = 1'b0;
    // Ibex implementation of MIE does not mask NM interrupts, so need to check this separately
    if (irq[irq_agent_pkg::DATA_WIDTH - 1]) begin
      irq_id = irq_agent_pkg::DATA_WIDTH - 1;
      return 1;
    end
    for (i = irq_agent_pkg::DATA_WIDTH - 2; i >= 16; i = i - 1) begin
      // Fast interrupts (IDs 30-16) are prioritised with the lowest ID first, but any fast
      // interrupt has priority over other interrupts.
      if (irq[i] == 1'b1 && core_init_mie[i] == 1'b1) begin
        irq_id = i;
        have_irq = 1'b1;
      end
    end

    if (!have_irq) begin
      // If there was no enabled fast interrupt, check the other interrupts
      if (irq[11] && core_init_mie[11]) begin
        // External interrupt
        irq_id = 11;
        have_irq = 1'b1;
      end else if (irq[3] && core_init_mie[3]) begin
        // Software interrupt
        irq_id = 3;
        have_irq = 1'b1;
      end else if (irq[7] && core_init_mie[7]) begin
        // Timer interrupt
        irq_id = 7;
        have_irq = 1'b1;
      end

      // Other interrupt IDs aren't implemented in Ibex
    end

    return have_irq;
  endfunction

  virtual task check_mcause(bit irq_or_exc, bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-2:0] cause);
    bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mcause;
    wait_for_csr_write(CSR_MCAUSE, 1000);
    mcause = signature_data;
    `uvm_info(`gfn, $sformatf("mcause: 0x%0x", mcause), UVM_LOW)
    `DV_CHECK_EQ_FATAL(mcause[ibex_mem_intf_agent_pkg::DATA_WIDTH-1], irq_or_exc,
                        $sformatf("mcause.interrupt is not set to 0x%0x", irq_or_exc))
    `DV_CHECK_EQ_FATAL(mcause[ibex_mem_intf_agent_pkg::DATA_WIDTH-2:0], cause,
                       "mcause.exception_code is encoding the wrong exception type")
  endtask

  // Basic debug stimulus check for Ibex for debug stimulus stress tests: check that Ibex enters
  // debug mode properly after stimulus is sent and then check that a dret is encountered signifying
  // the end of debug mode.
  virtual task stress_debug();
    fork
      begin
        vseq.start_debug_stress_seq();
      end
      begin
        forever begin
          wait_for_core_status(IN_DEBUG_MODE);
          check_priv_mode(PRIV_LVL_M);
          wait_ret("dret", 100000);
        end
      end
    join_none
  endtask

  // Task that waits for xRET to be asserted, with no timeout or objection
  virtual task wait_ret_raw(string ret);
      priv_lvl_e tgt_mode;
      case (ret)
        "dret": begin
          wait (dut_vif.dut_cb.dret === 1'b1);
        end
        "mret": begin
          wait (dut_vif.dut_cb.mret === 1'b1);
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("Invalid xRET instruction %0s", ret))
        end
      endcase
      tgt_mode = select_mode();
      wait (dut_vif.dut_cb.priv_mode === tgt_mode);
  endtask

  // Task that waits for xRET to be asserted within a certain number of cycles
  virtual task wait_ret(string ret, int timeout);
    cur_run_phase.raise_objection(this);
    fork
      begin
        wait_ret_raw(ret);
      end
      begin : ret_timeout
        clk_vif.wait_clks(timeout);
        `uvm_fatal(`gfn, $sformatf("No %0s detected, or incorrect privilege mode switch in \
                                    timeout period of %0d cycles", ret, timeout))
      end
    join_any
    // Will only get here if dret successfully detected within timeout period
    disable fork;
    cur_run_phase.drop_objection(this);
  endtask

  virtual function void check_priv_mode(priv_lvl_e mode);
    `DV_CHECK_EQ_FATAL(dut_vif.dut_cb.priv_mode, mode,
                       "Incorrect privilege mode")
  endfunction

endclass

// Base class for directed debug and irq test scenarios
class core_ibex_directed_test extends core_ibex_debug_intr_basic_test;

  `uvm_component_utils(core_ibex_directed_test)
  `uvm_component_new

  instr_t     seen_instr[$];
  bit [15:0]  seen_compressed_instr[$];

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
              if (enable_irq_seq) begin
                forever begin
                  send_irq_stimulus();
                end
              end
            end
            begin
              if (cfg.enable_debug_seq) begin
                stress_debug();
              end
            end
          join_none
        end else begin
          // Wait for core initialization before starting the stimulus check loop - first write
          // to signature address is guaranteed to be core initialization info
          wait_for_core_setup();
          // Wait for a little bit to guarantee that the core has started executing <main>
          // before starting to generate stimulus for the core.
          clk_vif.wait_clks(50);
          // Should be extended by derived classes.
          // DO NOT use this test class directly.
          fork
            check_stimulus();
          join_none
          wait (dut_vif.dut_cb.ecall === 1'b1);
          disable fork;
          if (cur_run_phase.get_objection_count(this) > 1) begin
            cur_run_phase.drop_objection(this);
          end
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

  // Send a single debug request and perform all relevant checks
  virtual task send_debug_stimulus(priv_lvl_e mode, string debug_status_err_msg);
    vseq.start_debug_single_seq();
    check_next_core_status(IN_DEBUG_MODE, debug_status_err_msg, 1000);
    check_priv_mode(PRIV_LVL_M);
    wait_for_csr_write(CSR_DCSR, 500);
    check_dcsr_prv(mode);
    check_dcsr_cause(DBG_CAUSE_HALTREQ);
    wait_ret("dret", 5000);
  endtask

  // Illegal instruction checker
  virtual task check_illegal_insn(string exception_msg);
    check_next_core_status(HANDLING_EXCEPTION, "Core did not jump to vectored exception handler", 1000);
    check_priv_mode(PRIV_LVL_M);
    check_next_core_status(ILLEGAL_INSTR_EXCEPTION, exception_msg, 1000);
    check_mcause(1'b0, ExcCauseIllegalInsn);
    wait_ret("mret", 1500);
  endtask

  // compares dcsr.ebreak against the privilege mode encoded in dcsr.prv
  virtual function void check_dcsr_ebreak();
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

  virtual function void check_dcsr_cause(dbg_cause_e cause);
    `DV_CHECK_EQ_FATAL(cause, signature_data[8:6], "dcsr.cause has been incorrectly updated")
  endfunction

  virtual function void check_dcsr_prv(priv_lvl_e mode);
    `DV_CHECK_EQ_FATAL(mode, signature_data[1:0],
                       "Incorrect dcsr.prv value!")
  endfunction

  // Check if we have seen the same type of instruction before by comparing the instruction
  // currently in the ID stage against the global seen_instr[$] queue.
  // If we've seen the same type of instruction before, return 0, otherwise add it to the
  // seen_instr[$] queue and return 1.
  virtual function bit decode_instr(bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] instr);
    ibex_pkg::opcode_e                            opcode;
    bit [2:0]                                     funct3;
    bit [6:0]                                     funct7;
    bit [12:0]                                    system_imm;
    instr_t                                       instr_fields;

    opcode      = ibex_pkg::opcode_e'(instr[6:0]);
    funct3      = instr[14:12];
    funct7      = instr[31:25];
    system_imm  = instr[31:20];

    // Now we search seen_instr[$] to check if a same instruction has been seen before.
    case (opcode)
      OPCODE_LUI, OPCODE_AUIPC, OPCODE_JAL: begin
        // these instructions only depend on opcode.
        foreach (seen_instr[i]) begin
          if (opcode == seen_instr[i].opcode) begin
            return 0;
          end
        end
      end
      OPCODE_JALR, OPCODE_BRANCH, OPCODE_LOAD,
      OPCODE_STORE, OPCODE_MISC_MEM: begin
        // these instructions only depend on opcode and funct3
        // to be identified.
        foreach (seen_instr[i]) begin
          if (opcode == seen_instr[i].opcode &&
              funct3 == seen_instr[i].funct3) begin
            return 0;
          end
        end
      end
      OPCODE_OP_IMM: begin
        // register-immediate arithmetic instructions are handled separately
        // as slli/srli/srai rely on funct7 in addition to opcode/funct3.
        foreach (seen_instr[i]) begin
          if (opcode == seen_instr[i].opcode &&
              funct3 == seen_instr[i].funct3) begin
            // handle slli/srli/srai instructions.
            if (funct3 inside {3'b001, 3'b101}) begin
              if (funct7 == seen_instr[i].funct7) begin
                return 0;
              end
            end else begin
              return 0;
            end
          end
        end
      end
      OPCODE_OP: begin
        // all register-register arithmetic instructions rely on
        // opcode/funct3/funct7 for identification.
        foreach (seen_instr[i]) begin
          if (opcode == seen_instr[i].opcode &&
              funct3 == seen_instr[i].funct3 &&
              funct7 == seen_instr[i].funct7) begin
            return 0;
          end
        end
      end
      OPCODE_SYSTEM: begin
        // explicitly set is_seen to 0 and return on WFI instructions,
        // as if we don't interrupt them, every test will timeout.
        if (funct3 == 3'b000 && system_imm == 12'h105) begin
          return 1;
        end else if (funct3 == 3'b000 && system_imm != 12'h001) begin
          // raise is_seen if ecall/mret/dret is detected,
          // we exclude them for now (this leads to nested traps).
          return 0;
        end else begin
          foreach (seen_instr[i]) begin
            if (opcode == seen_instr[i].opcode &&
                funct3 == seen_instr[i].funct3 &&
                system_imm == seen_instr[i].system_imm) begin
              return 0;
            end
          end
        end
      end
      default: begin
        `uvm_fatal(`gfn, "Illegal instruction detected")
      end
    endcase

    // We haven't seen this type of instruction before, so add it to seen_instr[$]
    // to flag it as 'seen' the next time we decode an instruction.
    instr_fields = '{opcode, funct3, funct7, system_imm};
    seen_instr.push_back(instr_fields);
    return 1;

  endfunction

  // Similarly to decode_instr(...), this function checks whether we have seen the
  // compressed instruction currently in the ID stage before by comparing it to the
  // global seen_compressed_instr[$] queue.
  // If we have seen it before, it returns 0, otherwise the instruction is added to the
  // and it returns 1.
  virtual function bit decode_compressed_instr(bit [15:0] instr);

    foreach (seen_compressed_instr[i]) begin
      if (instr[1:0] == seen_compressed_instr[i][1:0]) begin
        case (instr[1:0])
          2'b00: begin
            if (instr[15:13] == seen_compressed_instr[i][15:13]) begin
              return 0;
            end
          end
          2'b01: begin
            if (instr[15:13] == seen_compressed_instr[i][15:13]) begin
              case (instr[15:13])
                3'b000, 3'b001, 3'b010,
                3'b011, 3'b101, 3'b110, 3'b111: begin
                  return 0;
                end
                3'b100: begin
                  if (instr[11:10] == seen_compressed_instr[i][11:10]) begin
                    case (instr[11:10])
                      2'b00, 2'b01, 2'b10: begin
                        return 0;
                      end
                      2'b11: begin
                        if (instr[12] == seen_compressed_instr[i][12] &&
                            instr[6:5] == seen_compressed_instr[i][6:5]) begin
                          return 0;
                        end
                      end
                    endcase
                  end
                end
                default: begin
                  `uvm_fatal(`gfn, "Invalid C1 compressed instruction")
                end
              endcase
            end
          end
          2'b10: begin
            if (instr[15:13] == seen_compressed_instr[i][15:13]) begin
              case (instr[15:13])
                3'b000, 3'b010, 3'b110: begin
                  return 0;
                end
                3'b100: begin
                  if (instr[12] == seen_compressed_instr[i][12]) begin
                    return 0;
                  end
                end
                default: begin
                  `uvm_fatal(`gfn, "Illegal C2 compressed instruction")
                end
              endcase
            end
          end
          default: begin
            `uvm_fatal(`gfn, "Instruction is not compressed")
          end
        endcase
      end
    end

    // If we get here we have not seen the current instruction before,
    // so add it to seen_compressed_instr[$].
    seen_compressed_instr.push_back(instr);
    return 1'b1;

  endfunction

endclass

// A directed interrupt test that sends interrupt stimulus into the core
// after seeing every unique (and supported) RISC-V instruction in the core's
// Instruction Decode stage.
class core_ibex_interrupt_instr_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_interrupt_instr_test)
  `uvm_component_new

  virtual task check_stimulus();
    vseq.irq_raise_single_seq_h.max_delay = 0;
    vseq.irq_raise_single_seq_h.max_interval = 0;
    forever begin
      // hold until we see a valid instruction in the ID stage of the pipeline or the core goes to
      // sleep
      wait ((instr_vif.instr_cb.valid_id && !(instr_vif.instr_cb.err_id || dut_vif.illegal_instr))
        || dut_vif.core_sleep);

      // We don't want to send fast interrupts, as due to the random setup of MIE,
      // there's no guarantee that the interrupt will actually be taken.
      if (dut_vif.core_sleep) begin
        // Testbench waits for 50 clocks before calling check_stimulus. If a WFI is executed during
        // these 50 clocks the test would sleep forever, so if the core enters sleep send irq
        // stimulus to wake it up.
        send_irq_stimulus(.no_fast(1'b1));
      end else if (instr_vif.instr_cb.is_compressed_id) begin
        if (decode_compressed_instr(instr_vif.instr_cb.instr_compressed_id)) begin
          send_irq_stimulus(.no_fast(1'b1));
        end
      end else begin
        if (decode_instr(instr_vif.instr_cb.instr_id)) begin
          send_irq_stimulus(.no_fast(1'b1));
        end
      end
      clk_vif.wait_clks(1);
    end
  endtask

endclass

// Interrupt WFI test class
class core_ibex_irq_wfi_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_irq_wfi_test)
  `uvm_component_new

  virtual task check_stimulus();
    forever begin
      wait (dut_vif.dut_cb.core_sleep === 1'b1);
      send_irq_stimulus();
    end
  endtask

endclass

// Interrupt CSR test class
class core_ibex_irq_csr_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_irq_csr_test)
  `uvm_component_new

  virtual task check_stimulus();
    vseq.irq_raise_single_seq_h.max_delay = 0;
    // wait for a write to mstatus - should be in init code
    wait (csr_vif.csr_cb.csr_access === 1'b1 &&
          csr_vif.csr_cb.csr_addr === CSR_MSTATUS &&
          csr_vif.csr_cb.csr_op != CSR_OP_READ);
    // send interrupt immediately after detection
    send_irq_stimulus();
    // wait for a write to mie - should be in init code
    wait (csr_vif.csr_cb.csr_access === 1'b1 &&
          csr_vif.csr_cb.csr_addr === CSR_MIE &&
          csr_vif.csr_cb.csr_op != CSR_OP_READ);
    // send interrupt immediately after detection
    send_irq_stimulus();
  endtask

endclass

// Tests irqs asserted in debug mode
class core_ibex_irq_in_debug_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_irq_in_debug_test)
  `uvm_component_new

  virtual task check_stimulus();
    bit detected_irq = 1'b0;
    bit seen_dret = 1'b0;
    bit irq_valid = 1'b0;

    forever begin
      // Drive core into debug mode
      vseq.start_debug_single_seq();
      check_next_core_status(IN_DEBUG_MODE, "Core did not enter debug mode properly", 1000);
      check_priv_mode(PRIV_LVL_M);
      wait_for_csr_write(CSR_DCSR, 500);
      check_dcsr_prv(init_operating_mode);
      check_dcsr_cause(DBG_CAUSE_HALTREQ);

      seen_dret = 1'b0;
      detected_irq = 1'b0;
      irq_valid = 1'b0;

      // Test will generate an IRQ whilst in debug mode, depending on the random delay on the IRQ it
      // may remain enabled when DRET is executed (so the IRQ should be taken). The fork below
      // splits into three, one process stimulates the IRQ and waits for the DRET. The others check
      // for the IRQ being handled during debug and deal with the IRQ remained asserted after DRET
      // case.
      fork
        begin : wait_irq
          // Get IRQ raise transaction from IRQ monitor
          irq_collected_port.get(irq_txn);
          irq_valid = determine_irq_from_txn();
          detected_irq = 1'b1;

          if (!seen_dret) begin
            // If the DRET hasn't been seen yet await IRQ handler, if it is seen before this process
            // is disabled there is an error.
            wait_for_core_status(HANDLING_IRQ);
            `uvm_fatal(`gfn, "Core is handling interrupt detected in debug mode")
          end
        end
        begin : wait_dret
          wait_ret_raw("dret");
          seen_dret = 1'b1;

          wait (detected_irq);

          // If execution reaches this point the DRET has been seen whilst an IRQ id raised.
          // Disable `wait_irq` at this point as it's no longer an error for the interrupt handler
          // to execute
          disable wait_irq;

          `uvm_info(`gfn, "dret seen before IRQ dropped", UVM_LOW)

          if (irq_valid) begin
            // IRQ isn't disabled so IRQ will get handled
            `uvm_info(`gfn, "IRQ is enabled, interrupt should be taken", UVM_LOW)
            check_irq_handle();
            send_irq_stimulus_end();
          end else begin
            `uvm_info(`gfn, "IRQ is disabled, no interrupt should be taken", UVM_LOW)
            // IRQ is disabled so just drop IRQ
            vseq.start_irq_drop_seq();
            irq_collected_port.get(irq_txn);
          end
        end
        begin : dbg_irq_stimulate
          // Raise interrupts while the core is in debug mode
          vseq.start_irq_raise_seq();
          clk_vif.wait_clks(100);
          if (!seen_dret) begin
            // Reached end of wait and DRET not seen, so core remains in debug mode. Disable
            // `wait_dret` and `wait_irq` as we're dropping the IRQ now
            disable wait_dret;
            disable wait_irq;

            if (detected_irq) begin
              // Drop the IRQ if one was raised
              vseq.start_irq_drop_seq();
            end

            // Wait for DRET
            wait_ret("dret", 5000);
            // Get IRQ drop transaction from IRQ monitor
            irq_collected_port.get(irq_txn);
          end
        end
      join

      clk_vif.wait_clks($urandom_range(250, 500));
    end
  endtask

endclass

// Tests debug mode asserted during irq handler
class core_ibex_debug_in_irq_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_in_irq_test)
  `uvm_component_new

  virtual task check_stimulus();
    // send first part of irq/checking routine
    // then assert basic debug stimulus
    // check that core enters and exits debug mode correctly
    // then finish interrupt handling routine
    bit valid_irq;
    forever begin
      send_irq_stimulus_start(1'b0, 1'b0, valid_irq);
      if (valid_irq) begin
        fork
          begin
            send_debug_stimulus(operating_mode, "Core did not enter debug mode from interrupt handler");
          end
          begin
            wait (dut_vif.dut_cb.dret == 1'b1);
            send_irq_stimulus_end();
          end
        join
      end
      clk_vif.wait_clks($urandom_range(250, 500));
    end
  endtask

endclass

// Nested interrupt test class (with multiple interrupts)
class core_ibex_nested_irq_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_nested_irq_test)
  `uvm_component_new

  virtual task check_stimulus();
    bit valid_irq;
    bit valid_nested_irq;
    int unsigned initial_irq_delay;
    forever begin
      send_irq_stimulus_start(1'b1, 1'b0, valid_irq);
      if (valid_irq) begin
        initial_irq_delay = vseq.irq_raise_nmi_seq_h.max_delay;
        vseq.irq_raise_nmi_seq_h.max_delay = 0;
        // Send nested interrupt after the checks of the first interrupt have finished
        in_nested_trap = 1'b1;
        // wait until we are setting mstatus.mie to 1'b1 to send the next set of interrupts
        wait (csr_vif.csr_cb.csr_access === 1'b1 &&
             csr_vif.csr_cb.csr_addr === CSR_MSTATUS &&
             csr_vif.csr_cb.csr_op != CSR_OP_READ);
        send_nmi_stimulus();
        vseq.irq_raise_nmi_seq_h.max_delay = initial_irq_delay;
        in_nested_trap = 1'b0;
        send_irq_stimulus_end();
      end
    end
  endtask

endclass

// A directed debug test that sends debug stimulus into the core
// after seeing every unique (and supported) RISC-V instruction in the core's
// Instruction Decode stage.
class core_ibex_debug_instr_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_instr_test)
  `uvm_component_new

  virtual task check_stimulus();
    vseq.debug_seq_single_h.max_delay = 0;
    vseq.debug_seq_single_h.max_interval = 0;
    forever begin
      // hold until we see a valid instruction in the ID stage of the pipeline or the core goes to
      // sleep
      wait ((instr_vif.instr_cb.valid_id && !(instr_vif.instr_cb.err_id || dut_vif.illegal_instr)) || dut_vif.core_sleep);

      if (dut_vif.core_sleep) begin
        // Testbench waits for 50 clocks before calling check_stimulus. If a WFI is executed during
        // these 50 clocks the test would sleep forever, so if the core enters sleep send debug
        // stimulus to wake it up.
        send_debug_stimulus(init_operating_mode,
                            $sformatf("Did not jump into debug mode after instruction[0x%0x]",
                                      instr_vif.instr_cb.instr_compressed_id));
      end else if (instr_vif.instr_cb.is_compressed_id) begin
        if (decode_compressed_instr(instr_vif.instr_cb.instr_compressed_id)) begin
          send_debug_stimulus(init_operating_mode,
                              $sformatf("Did not jump into debug mode after instruction[0x%0x]",
                                        instr_vif.instr_cb.instr_compressed_id));
        end
      end else begin
        if (decode_instr(instr_vif.instr_cb.instr_id)) begin
          send_debug_stimulus(init_operating_mode,
                              $sformatf("Did not jump into debug mode after instruction[0x%0x]",
                                        instr_vif.instr_cb.instr_id));
        end
      end
      clk_vif.wait_clks(1);
    end
  endtask

endclass

// Debug WFI test class
class core_ibex_debug_wfi_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_wfi_test)
  `uvm_component_new

  virtual task check_stimulus();
    forever begin
      wait (dut_vif.dut_cb.wfi === 1'b1);
      wait (dut_vif.dut_cb.core_sleep === 1'b1);
      clk_vif.wait_clks($urandom_range(100));
      send_debug_stimulus(init_operating_mode, "Core did not jump into debug mode from WFI state");
    end
  endtask

endclass

// Debug CSR entry test
class core_ibex_debug_csr_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_csr_test)
  `uvm_component_new

  virtual task check_stimulus();
    vseq.debug_seq_single_h.max_delay = 0;
    // wait for a dummy write to mstatus in init code
    wait (csr_vif.csr_cb.csr_access === 1'b1 &&
          csr_vif.csr_cb.csr_addr === CSR_MSTATUS &&
          csr_vif.csr_cb.csr_op != CSR_OP_READ);
    send_debug_stimulus(init_operating_mode, "Core did not trap to debug mode upon debug stimulus");
    // wait for a dummy write to mie in the init code
    wait (csr_vif.csr_cb.csr_access === 1'b1 &&
          csr_vif.csr_cb.csr_addr === CSR_MIE &&
          csr_vif.csr_cb.csr_op != CSR_OP_READ);
    send_debug_stimulus(init_operating_mode, "Core did not trap to debug mode upon debug stimulus");
  endtask

endclass

// DRET test class
class core_ibex_dret_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_dret_test)
  `uvm_component_new

  virtual task check_stimulus();
    forever begin
      wait (dut_vif.dut_cb.dret === 1'b1);
      check_illegal_insn("Core did not treat dret like illegal instruction");
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
      vseq.start_debug_single_seq();
      check_next_core_status(IN_DEBUG_MODE, "Core did not properly jump into debug mode", 1000);
      // capture the first write of dcsr
      check_priv_mode(PRIV_LVL_M);
      wait_for_csr_write(CSR_DCSR, 500);
      check_dcsr_prv(init_operating_mode);
      dcsr = signature_data;
      // We also want to check that dcsr.cause has been set correctly
      check_dcsr_cause(DBG_CAUSE_HALTREQ);
      // capture the first write of dpc
      wait_for_csr_write(CSR_DPC, 500);
      dpc = signature_data;
      wait (dut_vif.dut_cb.ebreak === 1'b1);
      // compare the second writes of dcsr and dpc against the captured values
      wait_for_csr_write(CSR_DCSR, 1000);
      `DV_CHECK_EQ_FATAL(dcsr, signature_data,
                         "ebreak inside the debug rom has changed the value of DCSR")
      wait_for_csr_write(CSR_DPC, 500);
      `DV_CHECK_EQ_FATAL(dpc, signature_data,
                         "ebreak inside the debug rom has changed the value of DPC")
      wait_ret("dret", 1000);
      clk_vif.wait_clks($urandom_range(250, 500));
    end
  endtask

endclass

// Debug ebreak test with dcsr.ebreak(m/s/u) set
class core_ibex_debug_ebreakmu_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_ebreakmu_test)
  `uvm_component_new

  bit seen_ebreak;

  virtual task send_stimulus();
    seen_ebreak = 0;
    fork
      begin : detect_ebreak
        wait (dut_vif.dut_cb.ebreak === 1'b1);
        seen_ebreak = 1;
      end
      begin : run_stimulus
        core_ibex_directed_test::send_stimulus();
      end
    join
  endtask

  virtual task check_stimulus();
    fork begin
      fork
        begin : dbg_setup
          // send a single debug request after core initialization to configure dcsr
          vseq.start_debug_single_seq();
          check_next_core_status(IN_DEBUG_MODE,
                                 "Core did not enter debug mode after debug_req stimulus", 2000);
          check_priv_mode(PRIV_LVL_M);
          // Read dcsr and verify the appropriate ebreak(m/s/u) bit has been set based on the prv field,
          // as well as the cause field
          wait_for_csr_write(CSR_DCSR, 500);
          check_dcsr_prv(init_operating_mode);
          check_dcsr_ebreak();
          check_dcsr_cause(DBG_CAUSE_HALTREQ);
          wait_ret("dret", 5000);
        end
        begin : detect_ebreak
          wait (seen_ebreak == 1);
          `uvm_fatal(`gfn, {"EBreak seen whilst doing initial debug initialization, KNOWN FAILURE ",
            "SEE https://github.com/lowRISC/ibex/issues/1313"})
        end
      join_any
      disable fork;
    end join

    forever begin
      wait (dut_vif.dut_cb.ebreak === 1'b1);
      check_next_core_status(IN_DEBUG_MODE,
                             "Core did not enter debug mode after execution of ebreak", 2000);
      check_priv_mode(PRIV_LVL_M);
      // Read dcsr and verify the appropriate ebreak(m/s/u) bit has been set based on the prv field
      wait_for_csr_write(CSR_DCSR, 500);
      check_dcsr_prv(init_operating_mode);
      check_dcsr_ebreak();
      check_dcsr_cause(DBG_CAUSE_EBREAK);
      wait_ret("dret", 5000);
    end
  endtask

endclass

// Debug single step test
class core_ibex_debug_single_step_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_debug_single_step_test)
  `uvm_component_new

  // Waits until PC has changed from `cur_pc` and continues waiting until PC two steps ahead from
  // `cur_pc` can be determined.
  //
  // cur_pc -> a_pc -> b_pc
  //                    ^
  //                    |
  //
  // This will wait until instruction execution is at `a_pc` and keep waiting until it is clear what
  // `b_pc` will be.
  virtual task wait_for_pc_change(bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] cur_pc);
    // Wait for instruction PC to change then continuing waiting whilst it's stalled, immediately
    // stop waiting if a branch is taken or a jump is set (the PC following `cur_pc` will be
    // available the same cycle this happens). If `cur_pc` is a branch that isn't taken this will
    // be resolved when the branch is unstalled (i.e. `branch_taken_id` won't be set and the branch
    // definitely isn't taken).
    wait (instr_vif.instr_cb.pc_id != cur_pc     &&
          instr_vif.instr_cb.valid_id            &&
          (!instr_vif.instr_cb.stall_id       ||
           instr_vif.instr_cb.branch_taken_id ||
           instr_vif.instr_cb.jump_set_id));
  endtask

  virtual task check_stimulus();
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] counter = 0;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] next_counter = 0;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] ret_pc;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] curr_pc;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] next_pc;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] step_instr;
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] branch_target;
    bit                                           branch_taken;
    bit                                           is_compressed;

    forever begin
      clk_vif.wait_clks(2000);
      vseq.start_debug_single_seq();
      // perform the standard set of debug mode checks
      check_next_core_status(IN_DEBUG_MODE,
                             "Core did not enter debug mode after debug stimulus", 1000);
      check_priv_mode(PRIV_LVL_M);
      wait_for_csr_write(CSR_DPC, 500);
      ret_pc = signature_data;
      wait_for_csr_write(CSR_DSCRATCH0, 500);
      counter = signature_data;
      wait_for_csr_write(CSR_DCSR, 1000);
      check_dcsr_prv(init_operating_mode);
      check_dcsr_cause(DBG_CAUSE_HALTREQ);
      `DV_CHECK_EQ_FATAL(signature_data[2], 1'b1, "dcsr.step is not set")
      // wait for the DRET instruction indicating return out of debug mode.
      wait_ret("dret", 5000);
      ret_pc = instr_vif.instr_cb.pc_id;
      // wait for the instruction after dret to log its PC and other information.
      wait(!dut_vif.dut_cb.dret);
      wait_for_pc_change(ret_pc);
      curr_pc = instr_vif.instr_cb.pc_id;
      step_instr = instr_vif.instr_cb.instr_id;
      is_compressed = instr_vif.instr_cb.is_compressed_id;
      branch_taken  = instr_vif.instr_cb.branch_taken_id;
      // need to zero the bottom bit of branch_target to prevent unaligned addresses.
      branch_target = instr_vif.instr_cb.branch_target_id;
      branch_target[0] = 1'b0;
      // After the first DRET, the next <counter> instructions will cause a transition
      // into debug mode, as the core will single-step over all of them.
      //
      // Now we loop on the counter until we are done single stepping
      while (counter >= 0) begin
        check_next_core_status(IN_DEBUG_MODE,
                               "Core did not enter debug mode after debug stimulus", 1000);
        check_priv_mode(PRIV_LVL_M);
        wait_for_csr_write(CSR_DPC, 500);
        ret_pc = signature_data;
        // checks depend whether the interrupt instruction is a branch/jump.
        // we can also assume the instruction is valid as this test disables illegal instructions.
        case (ibex_pkg::opcode_e'(step_instr[6:0]))
          OPCODE_JAL, OPCODE_JALR: begin
            `DV_CHECK_EQ_FATAL(branch_target, ret_pc,
              $sformatf("DPC value[0x%0x] does not match jump target[0x%0x] at PC[0x%0x]",
                        ret_pc, branch_target, curr_pc))
          end
          OPCODE_BRANCH: begin
            // first check whether branch is actually taken
            if (branch_taken) begin
              `DV_CHECK_EQ_FATAL(branch_target, ret_pc,
                $sformatf("DPC value[0x%0x] does not match branch target[0x%0x] at PC[0x%0x]",
                          ret_pc, branch_target, curr_pc))
            end else begin
              // branch is not taken
              next_pc = (is_compressed) ? curr_pc + 2 : curr_pc + 4;
              `DV_CHECK_EQ_FATAL(next_pc, ret_pc,
                $sformatf("DPC value[0x%0x] does not match expected next PC[0x%0x] at PC[0x%0x]",
                          ret_pc, next_pc, curr_pc))
            end
          end
          // all other instructions
          default: begin
            next_pc = (is_compressed) ? curr_pc + 2 : curr_pc + 4;
            `DV_CHECK_EQ_FATAL(next_pc, ret_pc,
              $sformatf("DPC value[0x%0x] does not match expected next PC[0x%0x] at PC[0x%0x]",
                        ret_pc, next_pc, curr_pc))
          end
        endcase
        wait_for_csr_write(CSR_DSCRATCH0, 500);
        next_counter = signature_data;
        wait_for_csr_write(CSR_DCSR, 500);
        check_dcsr_prv(init_operating_mode);
        check_dcsr_cause(DBG_CAUSE_STEP);
        if (counter === 0) begin
          `DV_CHECK_EQ_FATAL(signature_data[2], 1'b0, "dcsr.step is set")
        end else begin
          `DV_CHECK_EQ_FATAL(signature_data[2], 1'b1, "dcsr.step is not set")
        end
        wait_ret("dret", 5000);
        ret_pc = instr_vif.instr_cb.pc_id;
        if (counter == 0) break;
        // wait until Ibex steps to the next instruction.
        wait(!dut_vif.dut_cb.dret);
        wait_for_pc_change(ret_pc);
        // log information about this instruction
        curr_pc = instr_vif.instr_cb.pc_id;
        step_instr = instr_vif.instr_cb.instr_id;
        is_compressed = instr_vif.instr_cb.is_compressed_id;
        branch_taken  = instr_vif.instr_cb.branch_taken_id;
        // need to zero the bottom bit of branch_target to prevent unaligned addresses.
        branch_target = instr_vif.instr_cb.branch_target_id;
        branch_target[0] = 1'b0;
        counter = next_counter;
      end
    end
  endtask

endclass

// Memory interface error test class
class core_ibex_mem_error_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_mem_error_test)
  `uvm_component_new

  int err_delay;

  // check memory error inputs and verify that core jumps to correct exception handler
  virtual task check_stimulus();
    forever begin
      while (!vseq.data_intf_seq.get_error_synch()) begin
        clk_vif.wait_clks(1);
      end
      vseq.data_intf_seq.inject_error();
      `uvm_info(`gfn, "Injected dmem error", UVM_LOW)
      // Dmem interface error could be either a load or store operation
      check_dmem_fault();
      // Random delay before injecting instruction fetch fault
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_delay, err_delay inside { [50:200] };)
      clk_vif.wait_clks(err_delay);
      inject_imem_error();
      check_imem_fault();
      // Random delay before injecting this series of errors again
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(err_delay, err_delay inside { [250:750] };)
      clk_vif.wait_clks(err_delay);
    end
  endtask

  virtual task inject_imem_error();
    while (!vseq.instr_intf_seq.get_error_synch()) begin
      clk_vif.wait_clks(1);
    end
    `uvm_info(`gfn, "Injecting imem fault", UVM_LOW)
    vseq.instr_intf_seq.inject_error();
  endtask

  virtual task check_dmem_fault();
    bit[ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mcause;
    core_status_t mem_status;
    ibex_pkg::exc_cause_t exc_type;
    // Don't impose a timeout period for dmem check, since dmem errors injected by the sequence are
    // not guaranteed to be reflected in RTL state until the next memory instruction is executed,
    // and the frequency of which is not controllable by the testbench
    check_next_core_status(HANDLING_EXCEPTION, "Core did not jump to exception handler");
    check_priv_mode(PRIV_LVL_M);
    // Next write of CORE_STATUS will be the load/store fault type
    wait_for_mem_txn(cfg.signature_addr, CORE_STATUS);
    mem_status = core_status_t'(signature_data_q.pop_front());
    if (mem_status == LOAD_FAULT_EXCEPTION) begin
      exc_type = ExcCauseLoadAccessFault;
    end else if (mem_status == STORE_FAULT_EXCEPTION) begin
      exc_type = ExcCauseStoreAccessFault;
    end
    check_mcause(1'b0, exc_type.lower_cause);
    wait (dut_vif.dut_cb.mret === 1'b1);
    `uvm_info(`gfn, "exiting mem fault checker", UVM_LOW)
  endtask

  virtual task check_imem_fault();
    bit latched_imem_err = 1'b0;
    core_status_t mem_status;
    ibex_pkg::exc_cause_t exc_type;
    // Need to account for case where imem_error is asserted during an instruction fetch that gets
    // killed - due to jumps and control flow changes
    do begin
      fork
        begin
          fork : imem_fork
            begin
              check_next_core_status(HANDLING_EXCEPTION, "Core did not jump to exception handler");
              check_priv_mode(PRIV_LVL_M);
              latched_imem_err = 1'b1;
              `uvm_info(`gfn, $sformatf("latched_imem_err: 0x%0x", latched_imem_err), UVM_LOW)
            end
            begin
              clk_vif.wait_clks(750);
            end
          join_any
          disable fork;
        end
      join
      if (latched_imem_err === 1'b0) begin
        cur_run_phase.drop_objection(this);
        inject_imem_error();
      end
    end while (latched_imem_err === 1'b0);
    check_next_core_status(INSTR_FAULT_EXCEPTION,
                           "Core did not register correct memory fault type", 500);
    exc_type = ExcCauseInstrAccessFault;
    check_mcause(1'b0, exc_type.lower_cause);
    wait (dut_vif.dut_cb.mret === 1'b1);
    `uvm_info(`gfn, "exiting mem fault checker", UVM_LOW)
  endtask

endclass

// U-mode mstatus.tw test class
class core_ibex_umode_tw_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_umode_tw_test)
  `uvm_component_new

  virtual task check_stimulus();
    bit [ibex_mem_intf_agent_pkg::DATA_WIDTH-1:0] mcause;
    forever begin
      wait (dut_vif.dut_cb.wfi === 1'b1);
      check_illegal_insn("Core did not treat U-mode WFI as illegal");
    end
  endtask

endclass

// Priv-mode CSR access test
class core_ibex_invalid_csr_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_invalid_csr_test)
  `uvm_component_new

  virtual task check_stimulus();
    forever begin
      // Wait for a CSR access
      wait (csr_vif.csr_cb.csr_access == 1'b1);
      check_illegal_insn($sformatf("Core did not treat access to CSR 0x%0x from %0s as illegal",
                                   csr_vif.csr_cb.csr_addr, init_operating_mode));
    end
  endtask

endclass

class core_ibex_fetch_en_chk_test extends core_ibex_directed_test;

  `uvm_component_utils(core_ibex_fetch_en_chk_test)
  `uvm_component_new

  virtual task send_stimulus();
    fetch_enable_seq fetch_enable_seq_h;
    fetch_enable_seq_h = fetch_enable_seq::type_id::create("fetch_enable_seq_h", this);
    `uvm_info(`gfn, "Running core_ibex_fetch_en_chk_test", UVM_LOW)
    fork
      begin
        vseq.start(env.vseqr);
      end
      begin
        fetch_enable_seq_h.start(env.vseqr);
      end
    join_any
  endtask

endclass
