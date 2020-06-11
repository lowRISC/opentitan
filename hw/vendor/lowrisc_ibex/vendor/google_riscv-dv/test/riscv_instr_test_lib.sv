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


class riscv_rand_instr_test extends riscv_instr_base_test;

  `uvm_component_utils(riscv_rand_instr_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.instr_cnt = 10000;
    cfg.num_of_sub_program = 5;
    `DV_CHECK_RANDOMIZE_FATAL(cfg)
    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

  virtual function void apply_directed_instr();
    // Mix below directed instruction streams with the random instructions
    asm_gen.add_directed_instr_stream("riscv_load_store_rand_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_loop_instr", 3);
    asm_gen.add_directed_instr_stream("riscv_jal_instr", 4);
    asm_gen.add_directed_instr_stream("riscv_hazard_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_load_store_hazard_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_multi_page_load_store_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_mem_region_stress_test", 4);
  endfunction

endclass

class riscv_ml_test extends riscv_instr_base_test;

  `uvm_component_utils(riscv_ml_test)
  `uvm_component_new

  virtual function void randomize_cfg();
    cfg.addr_translaction_rnd_order_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_FATAL(cfg)
    cfg.addr_translaction_rnd_order_c.constraint_mode(1);
    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

endclass
