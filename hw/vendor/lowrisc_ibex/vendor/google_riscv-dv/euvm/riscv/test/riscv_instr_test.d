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

// Sanity test for riscv_instr_test class

module riscv.test.riscv_instr_test;

import esdl;
import uvm;
import riscv.gen;
import std.format: format;
import std.stdio: File;
import esdl.rand: randomize;
import riscv.test.riscv_instr_base_test;
import std.range : repeat;

class riscv_instr_test: riscv_instr_base_test
{
  mixin uvm_component_utils;

  riscv_instr_gen_config cfg;
  string asm_file_name= "riscv_asm_test";

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
  override void run_phase(uvm_phase phase)
  {
    riscv_instr instr;
    riscv_instr_name_t instr_name;
    string test_name = format("%0s_0.S", asm_file_name);
    auto fd = File(test_name,"w");
    uvm_info(get_full_name(), "Creating instruction list", UVM_LOW);
    cfg.instr_registry.create_instr_list(cfg);
    uvm_info(get_full_name(), "Randomizing instruction list now...", UVM_LOW);

    //10000.repeat();
    for(int i = 0; i<100000; i++)
      {
	instr = cfg.instr_registry.get_rand_instr();
	instr.randomize();
	fd.writeln(instr.convert2asm());
      }
    //repeat (10000);
    instr = cfg.instr_registry.get_rand_instr([riscv_instr_category_t.LOAD, riscv_instr_category_t.STORE]);
    instr.randomize();
    fd.writeln(instr.convert2asm());

    // repeat (10000);
    instr = cfg.instr_registry.get_rand_instr(([riscv_instr_category_t.LOAD, riscv_instr_category_t.STORE , riscv_instr_category_t.BRANCH]),
					      ([riscv_instr_group_t.RV32I, riscv_instr_group_t.RV32M]));
    instr.randomize();
    fd.writeln(instr.convert2asm());

    uvm_info(get_full_name(), format("%0s is generated", test_name), UVM_LOW);

  }

  override void randomize_cfg()
  {
    cfg.randomize();
    uvm_info(get_full_name(), format("riscv_instr_gen_config is randomized:\n%0s",
				     cfg.sprint()), UVM_LOW);
  }

}
