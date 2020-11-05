/*
 * Copyright 2019 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//---------------------------------------------------------------------------------------
// RISC-V debug ROM class
//
// This is the main class to generate a test debug ROM, which includes control knobs to
// toggle various configuration fields of DCSR.
//---------------------------------------------------------------------------------------

class riscv_debug_rom_gen extends riscv_asm_program_gen;

  string debug_main[$];
  string debug_end[$];
  string str[$];
  string dret;
  int hart;

  `uvm_object_utils(riscv_debug_rom_gen)

  function new(string name = "");
    super.new(name);
    dret = "dret";
  endfunction

  //-------------------------------------------------------------------------------------
  // Main function to generate whole debug ROM
  //-------------------------------------------------------------------------------------

  virtual function void gen_program();
    string sub_program_name[$] = {};
    if (!cfg.gen_debug_section) begin
      // If the debug section should not be generated, we just populate it
      // with a dret instruction.
      debug_main = {dret};
      gen_section($sformatf("%0sdebug_rom", hart_prefix(hart)), debug_main);
    end else begin
      if (cfg.enable_ebreak_in_debug_rom) begin
        gen_ebreak_header();
      end
      // Need to save off GPRs to avoid modifying program flow
      push_gpr_to_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, debug_main);
      // Signal that the core entered debug rom only if the rom is actually
      // being filled with random instructions to prevent stress tests from
      // having to execute unnecessary push/pop of GPRs on the stack ever
      // time a debug request is sent
      gen_signature_handshake(debug_main, CORE_STATUS, IN_DEBUG_MODE);
      if (cfg.enable_ebreak_in_debug_rom) begin
        // send dpc and dcsr to testbench, as this handshake will be
        // executed twice due to the ebreak loop, there should be no change
        // in their values as by the Debug Mode Spec Ch. 4.1.8
        gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DCSR));
        gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DPC));
      end
      if (cfg.set_dcsr_ebreak) begin
        // We want to set dcsr.ebreak(m/s/u) to 1'b1, depending on what modes
        // are available.
        // TODO(udinator) - randomize the dcsr.ebreak setup
        gen_dcsr_ebreak();
      end
      if (cfg.enable_debug_single_step) begin
        gen_single_step_logic();
      end
      gen_dpc_update();
      // write DCSR to the testbench for any analysis
      gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DCSR));
      if (cfg.enable_ebreak_in_debug_rom || cfg.set_dcsr_ebreak) begin
        gen_increment_ebreak_counter();
      end
      format_section(debug_main);
      gen_sub_program(hart, sub_program[hart], sub_program_name,
                      cfg.num_debug_sub_program, 1'b1, "debug_sub");
      main_program[hart] = riscv_instr_sequence::type_id::create("debug_program");
      main_program[hart].instr_cnt = cfg.debug_program_instr_cnt;
      main_program[hart].is_debug_program = 1;
      main_program[hart].cfg = cfg;
      `DV_CHECK_RANDOMIZE_FATAL(main_program[hart])
      main_program[hart].gen_instr(.is_main_program(1'b1), .no_branch(cfg.no_branch_jump));
      gen_callstack(main_program[hart], sub_program[hart], sub_program_name,
                    cfg.num_debug_sub_program);
      main_program[hart].post_process_instr();
      main_program[hart].generate_instr_stream(.no_label(1'b1));
      debug_main = {debug_main,
                    main_program[hart].instr_string_list,
                    $sformatf("%sla x%0d, debug_end", indent, cfg.scratch_reg),
                    $sformatf("%sjalr x0, x%0d, 0", indent, cfg.scratch_reg)
                   };
      insert_sub_program(sub_program[hart], debug_main);
      gen_section($sformatf("%0sdebug_rom", hart_prefix(hart)), debug_main);
      if (cfg.enable_ebreak_in_debug_rom) begin
        gen_ebreak_footer();
      end
      pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv,
                                cfg.sp, cfg.tp, debug_end);
      if (cfg.enable_ebreak_in_debug_rom) begin
        gen_restore_ebreak_scratch_reg();
      end
      //format_section(debug_end);
      debug_end = {debug_end, dret};
      gen_section($sformatf("%0sdebug_end", hart_prefix(hart)), debug_end);
    end
    gen_debug_exception_handler();
  endfunction

  // Generate exception handling routine for debug ROM
  // TODO(udinator) - remains empty for now, only a DRET
  virtual function void gen_debug_exception_handler();
    str = {"dret"};
    gen_section($sformatf("%0sdebug_exception", hart_prefix(hart)), str);
  endfunction

  //-------------------------------------------------------------------------------------
  // Helper functions to generate smaller sections of code
  //-------------------------------------------------------------------------------------

  // As execution of ebreak in D mode causes core to re-enter D mode, this directed
  // sequence will be a loop that ensures the ebreak instruction will only be executed
  // once to prevent infinitely looping back to the beginning of the debug rom.
  // Write dscratch to random GPR and branch to debug_end if greater than 0, for ebreak loops.
  // Use dscratch1 to store original GPR value.
  virtual function void gen_ebreak_header();
    str = {$sformatf("csrw 0x%0x, x%0d", DSCRATCH1, cfg.scratch_reg),
           $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH0),
           $sformatf("beq x%0d, x0, 1f", cfg.scratch_reg),
           $sformatf("j %0sdebug_end", hart_prefix(hart)),
           $sformatf("1: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)};
    debug_main = {debug_main, str};
  endfunction

  // Set dscratch0 back to 0x0 to prepare for the next entry into debug
  // mode, and write dscratch0 and dcsr to the testbench for any
  // analysis
  virtual function void gen_ebreak_footer();
    // send dpc and dcsr to testbench, as this handshake will be
    // executed twice due to the ebreak loop, there should be no change
    // in their values as by the Debug Mode Spec Ch. 4.1.8
    gen_signature_handshake(.instr(debug_end), .signature_type(WRITE_CSR), .csr(DCSR));
    gen_signature_handshake(.instr(debug_end), .signature_type(WRITE_CSR), .csr(DPC));
    str = {$sformatf("csrwi 0x%0x, 0x0", DSCRATCH0)};
    debug_end = {debug_end, str};
  endfunction

  // Increment dscratch0 by 1 to update the loop counter for all ebreak tests
  virtual function void gen_increment_ebreak_counter();
    // Add 1 to dscratch0
    increment_csr(DSCRATCH0, 1, debug_main);
    str = {$sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)};
    debug_main = {debug_main, str};
  endfunction

  // We have been using dscratch1 to store the
  // value of our given scratch register for use in ebreak loop, so we
  // need to restore its value before returning from D mode
  virtual function void gen_restore_ebreak_scratch_reg();
    str = {$sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)};
    debug_end = {debug_end, str};
  endfunction

  // To enable debug single stepping, we must set dcsr.step to 1.
  // We will repeat the debug single stepping process a random number of times,
  // using a dscratch CSR as the counter, and decrement this counter by 1 every time we
  // enter debug mode, until this counter reaches 0, at which point we set
  // dcsr.step to 0 until the next debug stimulus is asserted.
  // Store our designated scratch_reg to dscratch1
  virtual function void gen_single_step_logic();
    str = {$sformatf("csrw 0x%0x, x%0d", DSCRATCH1, cfg.scratch_reg),
           // Only un-set dcsr.step if it is 1 and the iterations counter
           // is at 0 (has finished iterating)
           $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DCSR),
           $sformatf("andi x%0d, x%0d, 4", cfg.scratch_reg, cfg.scratch_reg),
           // If dcsr.step is 0, set to 1 and set the counter
           $sformatf("beqz x%0d, 1f", cfg.scratch_reg),
           $sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH0),
           // if the counter is greater than 0, decrement and continue single stepping
           $sformatf("bgtz x%0d, 2f", cfg.scratch_reg),
           $sformatf("csrc 0x%0x, 0x4", DCSR),
           $sformatf("beqz x0, 3f"),
           // Set dcsr.step and the num_iterations counter
           $sformatf("1: csrs 0x%0x, 0x4", DCSR),
           $sformatf("li x%0d, %0d", cfg.scratch_reg, cfg.single_step_iterations),
           $sformatf("csrw 0x%0x, x%0d", DSCRATCH0, cfg.scratch_reg),
           $sformatf("beqz x0, 3f"),
           // Decrement dscratch counter
           $sformatf("2: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH0),
           $sformatf("addi x%0d, x%0d, -1", cfg.scratch_reg, cfg.scratch_reg),
           $sformatf("csrw 0x%0x, x%0d", DSCRATCH0, cfg.scratch_reg),
           // Restore scratch_reg value from dscratch1
           $sformatf("3: csrr x%0d, 0x%0x", cfg.scratch_reg, DSCRATCH1)
    };
    debug_main = {debug_main, str};
    // write dpc to testbench
    gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DPC));
    // write out the counter to the testbench
    gen_signature_handshake(.instr(debug_main), .signature_type(WRITE_CSR), .csr(DSCRATCH0));
  endfunction

  // Check dcsr.cause, and update dpc by 0x4 if the cause is ebreak, as
  // ebreak will set set dpc to its own address, which will cause an
  // infinite loop.
  virtual function void gen_dpc_update();
    str = {$sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, DCSR),
           $sformatf("slli x%0d, x%0d, 0x17", cfg.scratch_reg, cfg.scratch_reg),
           $sformatf("srli x%0d, x%0d, 0x1d", cfg.scratch_reg, cfg.scratch_reg),
           $sformatf("li x%0d, 0x1", cfg.gpr[0]),
           $sformatf("bne x%0d, x%0d, 4f", cfg.scratch_reg, cfg.gpr[0])};
    debug_main = {debug_main, str};
    increment_csr(DPC, 4, debug_main);
    str = {"4: nop"};
    debug_main = {debug_main, str};
  endfunction

  // Set dcsr.ebreak(m/s/u)
  // TODO(udinator) - randomize the setup for these fields
  virtual function void gen_dcsr_ebreak();
    if (MACHINE_MODE inside {riscv_instr_pkg::supported_privileged_mode}) begin
      str = {$sformatf("li x%0d, 0x8000", cfg.scratch_reg),
             $sformatf("csrs 0x%0x, x%0d", DCSR, cfg.scratch_reg)};
      debug_main = {debug_main, str};
    end
    if (SUPERVISOR_MODE inside {riscv_instr_pkg::supported_privileged_mode}) begin
      str = {$sformatf("li x%0d, 0x2000", cfg.scratch_reg),
             $sformatf("csrs 0x%0x, x%0d", DCSR, cfg.scratch_reg)};
      debug_main = {debug_main, str};
    end
    if (USER_MODE inside {riscv_instr_pkg::supported_privileged_mode}) begin
      str = {$sformatf("li x%0d, 0x1000", cfg.scratch_reg),
             $sformatf("csrs 0x%0x, x%0d", DCSR, cfg.scratch_reg)};
      debug_main = {debug_main, str};
    end
  endfunction

  virtual function void increment_csr(privileged_reg_t csr, int val, ref string instr[$]);
    str = {$sformatf("csrr x%0d, 0x%0x", cfg.scratch_reg, csr),
           $sformatf("addi x%0d, x%0d, 0x%0x", cfg.scratch_reg, cfg.scratch_reg, val),
           $sformatf("csrw 0x%0x, x%0d", csr, cfg.scratch_reg)};
    instr = {instr, str};
  endfunction

endclass
