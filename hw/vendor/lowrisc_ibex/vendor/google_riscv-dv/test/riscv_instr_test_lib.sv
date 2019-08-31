/*
 * Copyright 2018 Google LLC
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

//================================================================================================
// RISC-V Test Library
//------------------------------------------------------------------------------------------------
// riscv_arithmetic_basic_test :
//  - Simple arithmetic instruction test, [machine mode]
//
// riscv_machine_mode_rand_test :
//  - Random instruction test, include sub-programs, branch, load/store [machine mode]
//
// riscv_privileged_mode_rand_test :
//  - Similar to riscv_machine_mode_rand_test, run in supervisor mode or user mode if supported
//
// riscv_rand_instr_test :
//  - A full random test, with a mix of directed instruction stream
//
// riscv_rand_jump_test :
//  - Random jump among a large number of sub programs
//
// riscv_mmu_stress_test:
//  - A mixed of intense load/store instructions
//
// riscv_page_table_exception_test:
//  - Running test in privileged mode with page table exceptions
//
// riscv_no_fence_test
//  - Random instruction with fence disabled, allow more intense instruction execution
//
// riscv_sfence_exception_test
//  - Random instruction with sfence exception. sfence.vma could be excuted in non-supervisor mode
//    or mstatus.tvm is set.
//
// riscv_illegal_instr_test:
//  - Random instruction mixed with illegal instructions
//
// riscv_hint_instr_test:
//  - Random instruction mixed with HINT instructions
//
// riscv_ebreak_test:
//  - Randomly inject ebreak instruction, verify core can be halted and resumed properly
//
// riscv_wfi_test:
//  - Randomly inject wfi instruction, verify core can be halted and resumed properly(by interrupt)
//
// riscv_csr_test:
//  - Random instructions with CSR intruction enabled
//
// riscv_illegal_csr_test:
//  - Accessing non-existence CSR or CSR with the wrong privileged mode
//
//================================================================================================

class riscv_arithmetic_basic_test extends riscv_instr_base_test;

  `uvm_component_utils(riscv_arithmetic_basic_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.instr_cnt = 10000;
    cfg.num_of_sub_program = 0;
    cfg.no_fence = 1;
    cfg.no_data_page = 1'b1;
    cfg.no_branch_jump = 1'b1;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(cfg,
                                   init_privileged_mode == MACHINE_MODE;
                                   max_nested_loop == 0;)
    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

endclass

class riscv_machine_mode_rand_test extends riscv_instr_base_test;

  `uvm_component_utils(riscv_machine_mode_rand_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.instr_cnt = 10000;
    cfg.num_of_sub_program = 5;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(cfg,
                                   init_privileged_mode == MACHINE_MODE;
                                   max_nested_loop == 0;)
    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

  virtual function void apply_directed_instr();
    // Add load/store instruction stream
    asm_gen.add_directed_instr_stream("riscv_load_store_rand_instr_stream", 10);
  endfunction

endclass

class riscv_privileged_mode_rand_test extends riscv_instr_base_test;

  `uvm_component_utils(riscv_privileged_mode_rand_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.instr_cnt = 10000;
    cfg.num_of_sub_program = 5;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(cfg,
                                   init_privileged_mode != MACHINE_MODE;
                                   max_nested_loop == 0;)
    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

  virtual function void apply_directed_instr();
    // Add load/store instruction stream
    asm_gen.add_directed_instr_stream("riscv_load_store_rand_instr_stream", 10);
  endfunction

endclass

class riscv_rand_instr_test extends riscv_instr_base_test;

  `uvm_component_utils(riscv_rand_instr_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.instr_cnt = 10000;
    cfg.num_of_sub_program = 5;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(cfg,
                                   max_nested_loop == 2;)
    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

  virtual function void apply_directed_instr();
    // Mix below directed instructino streams with the random instructions
    asm_gen.add_directed_instr_stream("riscv_load_store_rand_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_loop_instr", 4);
    asm_gen.add_directed_instr_stream("riscv_hazard_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_load_store_hazard_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_cache_line_stress_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_multi_page_load_store_instr_stream", 4);
  endfunction

endclass

class riscv_rand_jump_test extends riscv_instr_base_test;

  `uvm_component_utils(riscv_rand_jump_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.instr_cnt = 20000;
    cfg.num_of_sub_program = 20;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(cfg,
                                   max_nested_loop == 1;)
    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

  virtual function void apply_directed_instr();
    asm_gen.add_directed_instr_stream("riscv_load_store_rand_instr_stream", 10);
  endfunction

endclass

class riscv_mmu_stress_test extends riscv_instr_base_test;

  `uvm_component_utils(riscv_mmu_stress_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.instr_cnt = 500;
    cfg.num_of_sub_program = 0;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(cfg,
                                   max_nested_loop == 0;)
    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

  virtual function void apply_directed_instr();
    // Mix below directed instructino streams with the random instructions
    asm_gen.add_directed_instr_stream("riscv_cache_line_stress_instr_stream", 80);
    asm_gen.add_directed_instr_stream("riscv_load_store_hazard_instr_stream", 80);
    asm_gen.add_directed_instr_stream("riscv_multi_page_load_store_instr_stream", 80);
  endfunction

endclass

class riscv_page_table_exception_test extends riscv_rand_instr_test;

  `uvm_component_utils(riscv_page_table_exception_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.enable_page_table_exception = 1'b1;
    super.randomize_cfg();
  endfunction

endclass

class riscv_no_fence_test extends riscv_rand_instr_test;

  `uvm_component_utils(riscv_no_fence_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.no_fence = 1'b1;
    super.randomize_cfg();
  endfunction

endclass

class riscv_sfence_exception_test extends riscv_rand_instr_test;

  `uvm_component_utils(riscv_sfence_exception_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.allow_sfence_exception = 1'b1;
    super.randomize_cfg();
  endfunction

endclass

class riscv_illegal_instr_test extends riscv_rand_instr_test;

  `uvm_component_utils(riscv_illegal_instr_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.enable_illegal_instruction = 1'b1;
    super.randomize_cfg();
  endfunction

endclass

class riscv_hint_instr_test extends riscv_rand_instr_test;

  `uvm_component_utils(riscv_hint_instr_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.enable_hint_instruction = 1'b1;
    super.randomize_cfg();
  endfunction

endclass

class riscv_ebreak_test extends riscv_rand_instr_test;

  `uvm_component_utils(riscv_ebreak_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.no_ebreak = 1'b0;
    super.randomize_cfg();
  endfunction

endclass

class riscv_wfi_test extends riscv_rand_instr_test;

  `uvm_component_utils(riscv_wfi_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.no_wfi = 1'b0;
    super.randomize_cfg();
  endfunction

endclass

class riscv_illegal_csr_test extends riscv_rand_instr_test;

  `uvm_component_utils(riscv_illegal_csr_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.enable_illegal_csr_instruction = 1'b1;
    super.randomize_cfg();
  endfunction

endclass
