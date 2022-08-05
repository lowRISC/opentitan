/*
 * Copyright 2019 Google LLC
 * Copyright 2022 Coverify Systems Technology
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

module riscv.gen.riscv_debug_rom_gen;

import riscv.gen.riscv_instr_pkg: privileged_reg_t, hart_prefix, push_gpr_to_kernel_stack,
  indent, pop_gpr_from_kernel_stack, privileged_mode_t;
import riscv.gen.target: supported_privileged_mode;
import riscv.gen.riscv_instr_sequence: riscv_instr_sequence;
import riscv.gen.riscv_asm_program_gen: riscv_asm_program_gen;
import riscv.gen.riscv_signature_pkg: core_status_t, signature_type_t, test_result_t;

import std.format: format;
import std.algorithm.searching: canFind;

import esdl.rand: randomize;
import uvm;

class riscv_debug_rom_gen : riscv_asm_program_gen
{
  string[] debug_main;
  string[] debug_end;
  // string[] str;  // This should actually be a local variable inside the methods/functions
  string dret;
  int hart;

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
    dret = "dret";
  }

  //-------------------------------------------------------------------------------------
  // Main function to generate whole debug ROM
  //-------------------------------------------------------------------------------------

  override void gen_program() {
    string[] sub_program_name;
    if (! cfg.gen_debug_section) {
      // If the debug section should not be generated, we just populate it
      // with a dret instruction.
      debug_main ~= dret;
      gen_section(format("%0sdebug_rom", hart_prefix(hart)), debug_main);
    }
    else {
      if (cfg.enable_ebreak_in_debug_rom) {
	gen_ebreak_header();
      }
      // Need to save off GPRs to avoid modifying program flow
      push_gpr_to_kernel_stack(privileged_reg_t.MSTATUS, privileged_reg_t.MSCRATCH,
			       cfg.mstatus_mprv, cfg.sp, cfg.tp, debug_main);
      // Signal that the core entered debug rom only if the rom is actually
      // being filled with random instructions to prevent stress tests from
      // having to execute unnecessary push/pop of GPRs on the stack ever
      // time a debug request is sent
      gen_signature_handshake(debug_main, signature_type_t.CORE_STATUS, core_status_t.IN_DEBUG_MODE);
      if (cfg.enable_ebreak_in_debug_rom) {
	// send dpc and dcsr to testbench, as this handshake will be
	// executed twice due to the ebreak loop, there should be no change
	// in their values as by the Debug Mode Spec Ch. 4.1.8
	gen_signature_handshake(debug_main, signature_type_t.WRITE_CSR, core_status_t.INITIALIZED,
				test_result_t.TEST_FAIL, privileged_reg_t.DCSR);
	gen_signature_handshake(debug_main, signature_type_t.WRITE_CSR, core_status_t.INITIALIZED,
				test_result_t.TEST_FAIL, privileged_reg_t.DPC);
      }
      if (cfg.set_dcsr_ebreak) {
	// We want to set dcsr.ebreak(m/s/u) to 1'b1, depending on what modes
	// are available.
	// TODO(udinator) - randomize the dcsr.ebreak setup
	gen_dcsr_ebreak();
      }
      if (cfg.enable_debug_single_step) {
	gen_single_step_logic();
      }
      gen_dpc_update();
      // write DCSR to the testbench for any analysis
      gen_signature_handshake(debug_main, signature_type_t.WRITE_CSR, core_status_t.INITIALIZED,
			      test_result_t.TEST_FAIL, privileged_reg_t.DCSR);
      if (cfg.enable_ebreak_in_debug_rom || cfg.set_dcsr_ebreak) {
	gen_increment_ebreak_counter();
      }
      format_section(debug_main);
      gen_sub_program(hart, sub_program[hart], sub_program_name,cfg.num_debug_sub_program,
		      true, "debug_sub");
      main_program[hart] = riscv_instr_sequence.type_id.create("debug_program");
      main_program[hart].instr_cnt = cfg.debug_program_instr_cnt;
      main_program[hart].is_debug_program = 1;
      main_program[hart].cfg = cfg;
      main_program[hart].randomize();
      // `DV_CHECK_RANDOMIZE_FATAL(main_program[hart])
      main_program[hart].gen_instr(true, cfg.no_branch_jump);
      gen_callstack(main_program[hart], sub_program[hart], sub_program_name,
		    cfg.num_debug_sub_program);
      main_program[hart].post_process_instr();
      main_program[hart].generate_instr_stream(true);
      debug_main ~= main_program[hart].instr_string_list.toArray ~
	format("%sla x%0d, debug_end", indent, cfg.scratch_reg) ~
	format("%sjalr x0, x%0d, 0", indent, cfg.scratch_reg);
      insert_sub_program(sub_program[hart], debug_main);
      gen_section(format("%0sdebug_rom", hart_prefix(hart)), debug_main);
      if (cfg.enable_ebreak_in_debug_rom) {
	gen_ebreak_footer();
      }
      pop_gpr_from_kernel_stack(privileged_reg_t.MSTATUS, privileged_reg_t.MSCRATCH,
				cfg.mstatus_mprv, cfg.sp, cfg.tp, debug_end);
      if (cfg.enable_ebreak_in_debug_rom) {
	gen_restore_ebreak_scratch_reg();
      }
      //format_section(debug_end);
      debug_end ~= dret;
      gen_section(format("%0sdebug_end", hart_prefix(hart)), debug_end);
    }
    gen_debug_exception_handler();
  }

  // Generate exception handling routine for debug ROM
  // TODO(udinator) - remains empty for now, only a DRET
  void gen_debug_exception_handler() {
    string[] str = ["dret"];
    gen_section(format("%0sdebug_exception", hart_prefix(hart)), str);
  }

  //-------------------------------------------------------------------------------------
  // Helper functions to generate smaller sections of code
  //-------------------------------------------------------------------------------------

  // As execution of ebreak in D mode causes core to re-enter D mode, this directed
  // sequence will be a loop that ensures the ebreak instruction will only be executed
  // once to prevent infinitely looping back to the beginning of the debug rom.
  // Write dscratch to random GPR and branch to debug_end if greater than 0, for ebreak loops.
  // Use dscratch1 to store original GPR value.
  void gen_ebreak_header() {
    string[] str = [format("csrw 0x%0x, x%0d", privileged_reg_t.DSCRATCH1, cfg.scratch_reg),
		    format("csrr x%0d, 0x%0x", cfg.scratch_reg, privileged_reg_t.DSCRATCH0),
		    format("beq x%0d, x0, 1f", cfg.scratch_reg),
		    format("j %0sdebug_end", hart_prefix(hart)),
		    format("1: csrr x%0d, 0x%0x", cfg.scratch_reg, privileged_reg_t.DSCRATCH1)];
    debug_main ~= str;
  }

  // Set dscratch0 back to 0x0 to prepare for the next entry into debug
  // mode, and write dscratch0 and dcsr to the testbench for any
  // analysis
  void gen_ebreak_footer() {
    // send dpc and dcsr to testbench, as this handshake will be
    // executed twice due to the ebreak loop, there should be no change
    // in their values as by the Debug Mode Spec Ch. 4.1.8
    gen_signature_handshake(debug_end, signature_type_t.WRITE_CSR, core_status_t.INITIALIZED,
				test_result_t.TEST_FAIL, privileged_reg_t.DCSR);
    gen_signature_handshake(debug_end, signature_type_t.WRITE_CSR, core_status_t.INITIALIZED,
				test_result_t.TEST_FAIL, privileged_reg_t.DPC);
    string str = format("csrwi 0x%0x, 0x0", privileged_reg_t.DSCRATCH0);
    debug_end ~= str;
  }

  // Increment dscratch0 by 1 to update the loop counter for all ebreak tests
  void gen_increment_ebreak_counter() {
    // Add 1 to dscratch0
    increment_csr(privileged_reg_t.DSCRATCH0, 1, debug_main);
    string str = format("csrr x%0d, 0x%0x", cfg.scratch_reg, privileged_reg_t.DSCRATCH1);
    debug_main ~= str;
  }

  // We have been using dscratch1 to store the
  // value of our given scratch register for use in ebreak loop, so we
  // need to restore its value before returning from D mode
  void gen_restore_ebreak_scratch_reg() {
    string str = format("csrr x%0d, 0x%0x", cfg.scratch_reg, privileged_reg_t.DSCRATCH1);
    debug_end ~= str;
  }

  // To enable debug single stepping, we must set dcsr.step to 1.
  // We will repeat the debug single stepping process a random number of times,
  // using a dscratch CSR as the counter, and decrement this counter by 1 every time we
  // enter debug mode, until this counter reaches 0, at which point we set
  // dcsr.step to 0 until the next debug stimulus is asserted.
  // Store our designated scratch_reg to dscratch1
  void gen_single_step_logic() {
    string[] str = [format("csrw 0x%0x, x%0d", privileged_reg_t.DSCRATCH1, cfg.scratch_reg),
		    // Only un-set dcsr.step if it is 1 and the iterations counter
		    // is at 0 (has finished iterating)
		    format("csrr x%0d, 0x%0x", cfg.scratch_reg, privileged_reg_t.DCSR),
		    format("andi x%0d, x%0d, 4", cfg.scratch_reg, cfg.scratch_reg),
		    // If dcsr.step is 0, set to 1 and set the counter
		    format("beqz x%0d, 1f", cfg.scratch_reg),
		    format("csrr x%0d, 0x%0x", cfg.scratch_reg, privileged_reg_t.DSCRATCH0),
		    // if the counter is greater than 0, decrement and continue single stepping
		    format("bgtz x%0d, 2f", cfg.scratch_reg),
		    format("csrc 0x%0x, 0x4", privileged_reg_t.DCSR),
		    format("beqz x0, 3f"),
		    // Set dcsr.step and the num_iterations counter
		    format("1: csrs 0x%0x, 0x4", privileged_reg_t.DCSR),
		    format("li x%0d, %0d", cfg.scratch_reg, cfg.single_step_iterations),
		    format("csrw 0x%0x, x%0d", privileged_reg_t.DSCRATCH0, cfg.scratch_reg),
		    format("beqz x0, 3f"),
		    // Decrement dscratch counter
		    format("2: csrr x%0d, 0x%0x", cfg.scratch_reg, privileged_reg_t.DSCRATCH0),
		    format("addi x%0d, x%0d, -1", cfg.scratch_reg, cfg.scratch_reg),
		    format("csrw 0x%0x, x%0d", privileged_reg_t.DSCRATCH0, cfg.scratch_reg),
		    // Restore scratch_reg value from dscratch1
		    format("3: csrr x%0d, 0x%0x", cfg.scratch_reg, privileged_reg_t.DSCRATCH1)];
    debug_main ~= str;
    // write dpc to testbench
    gen_signature_handshake(debug_main, signature_type_t.WRITE_CSR, core_status_t.INITIALIZED,
				test_result_t.TEST_FAIL, privileged_reg_t.DPC);
    // write out the counter to the testbench
    gen_signature_handshake(debug_main, signature_type_t.WRITE_CSR, core_status_t.INITIALIZED,
			    test_result_t.TEST_FAIL, privileged_reg_t.DSCRATCH0);
  }

  // Check dcsr.cause, and update dpc by 0x4 if the cause is ebreak, as
  // ebreak will set set dpc to its own address, which will cause an
  // infinite loop.
  void gen_dpc_update() {
    string[] str = [format("csrr x%0d, 0x%0x", cfg.scratch_reg, privileged_reg_t.DCSR),
		    format("slli x%0d, x%0d, 0x17", cfg.scratch_reg, cfg.scratch_reg),
		    format("srli x%0d, x%0d, 0x1d", cfg.scratch_reg, cfg.scratch_reg),
		    format("li x%0d, 0x1", cfg.gpr[0]),
		    format("bne x%0d, x%0d, 4f", cfg.scratch_reg, cfg.gpr[0])];
    debug_main ~= str;
    increment_csr(privileged_reg_t.DPC, 4, debug_main);
    str = ["4: nop"];
    debug_main ~= str;
  }

  // Set dcsr.ebreak(m/s/u)
  // TODO(udinator) - randomize the setup for these fields
  void gen_dcsr_ebreak() {
    if (canFind (supported_privileged_mode, privileged_mode_t.MACHINE_MODE)) {
      string[] str = [format("li x%0d, 0x8000", cfg.scratch_reg),
		      format("csrs 0x%0x, x%0d", privileged_reg_t.DCSR, cfg.scratch_reg)];
      debug_main ~= str;
    }
    if ( canFind (supported_privileged_mode , privileged_mode_t.SUPERVISOR_MODE)) {
      string[] str = [format("li x%0d, 0x2000", cfg.scratch_reg),
		      format("csrs 0x%0x, x%0d", privileged_reg_t.DCSR, cfg.scratch_reg)];
      debug_main ~= str;
    }
    if (canFind (supported_privileged_mode, privileged_mode_t.USER_MODE)) {
      string[] str = [format("li x%0d, 0x1000", cfg.scratch_reg),
		      format("csrs 0x%0x, x%0d", privileged_reg_t.DCSR, cfg.scratch_reg)];
      debug_main ~= str;
    }
  }

  void increment_csr(privileged_reg_t csr, int val, ref string [] instr) {
    string[] str = [format("csrr x%0d, 0x%0x", cfg.scratch_reg, csr),
		    format("addi x%0d, x%0d, 0x%0x", cfg.scratch_reg, cfg.scratch_reg, val),
		    format("csrw 0x%0x, x%0d", csr, cfg.scratch_reg)];
    instr ~= str;
  }
}
