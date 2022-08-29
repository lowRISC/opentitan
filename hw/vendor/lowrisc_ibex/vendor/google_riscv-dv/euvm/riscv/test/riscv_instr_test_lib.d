/*
 * Copyright 2018 Google LLC
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
module riscv.test.riscv_instr_test_lib;

import uvm;
import riscv.gen;
import std.format: format;
import esdl;
import riscv.test.riscv_instr_base_test;

class riscv_rand_instr_test:riscv_instr_base_test
{
  mixin uvm_component_utils;

  riscv_instr_gen_config  cfg;
  string                  asm_file_name = "riscv_asm1_test";
  uvm_coreservice_t       coreservice;
  uvm_factory             factory;


  this(string name="", uvm_component parent=null) {
    super(name, parent);
  }


  override void build_phase(uvm_phase phase)
  {  super.build_phase(phase);
    coreservice = uvm_coreservice_t.get();
    factory = coreservice.get_factory();
    uvm_info(get_full_name(), "Create configuration instance", UVM_LOW);
    cfg = riscv_instr_gen_config.type_id.create("cfg");
    uvm_info(get_full_name(), "Create configuration instance...done", UVM_LOW);
    uvm_info(get_full_name(), cfg.sprint(), UVM_LOW);
    uvm_config_db!(riscv_instr_gen_config).set(null, "*", "instr_cfg", cfg);
    if(cfg.asm_test_suffix != "")
      asm_file_name = asm_file_name ~ "." ~ cfg.asm_test_suffix;
    if (support_debug_mode) {
      factory.set_inst_override_by_name("riscv_asm_program_gen",
                                        "riscv_debug_rom_gen",
                                        get_full_name() ~ ".asm_gen.debug_rom");
    }

  }
  override void randomize_cfg()
  {
    cfg.instr_cnt = 1000;
    cfg.num_of_sub_program = 5;
    cfg.randomize();
    uvm_info(get_full_name(), format("riscv_instr_gen_config is randomized:\n%0s",
				     cfg.sprint()), UVM_LOW);
  }

  override void run_phase(uvm_phase phase)
  {
    string test_name;
    randomize_cfg();
    asm_gen = riscv_asm_program_gen.type_id.create("asm_gen", null, get_full_name());
    apply_directed_instr();
  }



  override void apply_directed_instr()
  {
    uvm_info(get_full_name(), "all directed instruction printed here" , UVM_LOW);
    // Mix below directed instruction streams with the random instruction
    asm_gen.add_directed_instr_stream("riscv_load_store_rand_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_loop_instr", 3);
    asm_gen.add_directed_instr_stream("riscv_jal_instr", 4);
    asm_gen.add_directed_instr_stream("riscv_hazard_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_load_store_hazard_instr_st ream", 4);
    asm_gen.add_directed_instr_stream("riscv_multi_page_load_store_instr_stream", 4);
    asm_gen.add_directed_instr_stream("riscv_mem_region_stress_test", 4);
  }
}

class riscv_ml_test: riscv_instr_base_test
{
  mixin uvm_component_utils;

  riscv_instr_gen_config  cfg;
  //string                  asm_file_name = "riscv_asm1_test";
  uvm_coreservice_t       coreservice;
  uvm_factory             factory;

  this(string name="", uvm_component parent=null) {
    super(name, parent);
  }

  override void build_phase(uvm_phase phase)
  {
    super.build_phase(phase);
    coreservice = uvm_coreservice_t.get();
    factory = coreservice.get_factory();
    uvm_info(get_full_name(), "Create configuration instance", UVM_LOW);
    cfg = riscv_instr_gen_config.type_id.create("cfg");
    uvm_info(get_full_name(), "Create configuration instance...done", UVM_LOW);
    uvm_info(get_full_name(), cfg.sprint(), UVM_LOW);
    uvm_config_db!(riscv_instr_gen_config).set(null, "*", "instr_cfg", cfg);
  }

  override void randomize_cfg()
  {
    cfg.addr_translation_rnd_order_c.constraint_mode(0);
    cfg.randomize();
    cfg.addr_translation_rnd_order_c.constraint_mode(1);
    uvm_info(get_full_name(), format("riscv_instr_gen_config is randomized:\n%0s",cfg.sprint()), UVM_LOW);
  }

  override void run_phase(uvm_phase phase)
  {
    randomize_cfg();
  }

}
