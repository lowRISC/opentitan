/*
 * Copyright 2018 Google LLC
 * Copyright 2021 Coverify Systems Technology
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
module riscv.test.riscv_instr_base_test;

import uvm;
import riscv.gen;

// import riscv.gen.riscv_instr_gen_config;
// import riscv.gen.riscv_asm_program_gen;
// import riscv.gen.riscv_core_setting;
// // import riscv.gen.riscv_instr_registry;
// import riscv.gen.isa.riscv_instr;

import std.format: format;
import esdl;

// Base test
class riscv_instr_base_test: uvm_test
{
  mixin uvm_component_utils;

  riscv_instr_gen_config  cfg;
  // riscv_instr_registry    registry;
  string                  test_opts;
  string                  asm_file_name = "riscv_asm_test";
  riscv_asm_program_gen   asm_gen;
  string                  instr_seq;
  int                     start_idx;
  uvm_coreservice_t       coreservice;
  uvm_factory             factory;

  CommandLine             cmd;


  this(string name="", uvm_component parent=null) {
    super(name, parent);
    cmd = new CommandLine();
    cmd.plusArgs("asm_file_name=%s", asm_file_name);
    cmd.plusArgs("start_idx=%d", start_idx);
  }

  override void build_phase(uvm_phase phase) {
    super.build_phase(phase);
    coreservice = uvm_coreservice_t.get();
    factory = coreservice.get_factory();
    uvm_info(get_full_name(), "Create configuration instance", UVM_LOW);
    cfg = riscv_instr_gen_config.type_id.create("cfg");
    // registry = riscv_instr_registry.type_id.create("registry");
    uvm_info(get_full_name(), "Create configuration instance...done", UVM_LOW);
    uvm_info(get_full_name(), cfg.sprint(), UVM_LOW);
    uvm_config_db!(riscv_instr_gen_config).set(null, "*", "instr_cfg", cfg);
    if(cfg.asm_test_suffix != "")
      asm_file_name = asm_file_name ~ "." ~ cfg.asm_test_suffix;
    // Override the default riscv instruction sequence
    if (cmd.plusArgs("instr_seq=%s", instr_seq)) {
      factory.set_type_override_by_name("riscv_instr_sequence", instr_seq);
    }
    if (support_debug_mode) {
      factory.set_inst_override_by_name("riscv_asm_program_gen",
                                        "riscv_debug_rom_gen",
                                        get_full_name() ~ ".asm_gen.debug_rom");
    }
  }

  override void report_phase(uvm_phase phase) {
    uvm_report_server rs;
    int error_count;

    rs = uvm_report_server.get_server();

    error_count = rs.get_severity_count(UVM_WARNING) +
                  rs.get_severity_count(UVM_ERROR) +
                  rs.get_severity_count(UVM_FATAL);

    if (error_count == 0) {
      uvm_info("", "TEST PASSED", UVM_NONE);
    }
    else {
      uvm_info("", "TEST FAILED", UVM_NONE);
    }
    uvm_trace("", "TEST GENERATION DONE", UVM_NONE);
    super.report_phase(phase);
  }

  void apply_directed_instr() { }


  override void run_phase(uvm_phase phase) {
    int fd;
    for (int i = 0; i < cfg.num_of_tests; i++) {
      string test_name;
      randomize_cfg();
      // registry.create_instr_list(cfg);
      asm_gen = riscv_asm_program_gen.type_id.create("asm_gen", null, get_full_name());
      asm_gen.cfg = cfg;
      asm_gen.get_directed_instr_stream();
      test_name = format("%0s_%0d.S", asm_file_name, i+start_idx);
      apply_directed_instr();
      uvm_info(get_full_name(), "All directed instruction is applied", UVM_LOW);
      asm_gen.gen_program();
      asm_gen.gen_test_file(test_name);
    }
  }

  void randomize_cfg() {
    cfg.randomize();
    uvm_info(get_full_name(), format("riscv_instr_gen_config is randomized:\n%0s",
				     cfg.sprint()), UVM_LOW);
  }

}
