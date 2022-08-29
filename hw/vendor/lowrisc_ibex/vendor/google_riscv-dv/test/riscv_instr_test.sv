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

// Sanity test for riscv_instr_test class
class riscv_instr_test extends riscv_instr_base_test;

  `uvm_component_utils(riscv_instr_test)
  `uvm_component_new

  task run_phase(uvm_phase phase);
    int fd;
    riscv_instr instr;
    riscv_instr_name_t instr_name;
    string test_name = $sformatf("%0s_0.S", asm_file_name);
    fd = $fopen(test_name,"w");
    `uvm_info(`gfn, "Creating instruction list", UVM_LOW)
    riscv_instr::create_instr_list(cfg);
    riscv_csr_instr::create_csr_filter(cfg);
    `uvm_info(`gfn, "Randomizing instruction list now...", UVM_LOW)
    repeat (10000) begin
      instr = riscv_instr::get_rand_instr();
      `DV_CHECK_RANDOMIZE_FATAL(instr);
      $fwrite(fd, {instr.convert2asm(),"\n"});
    end
    repeat (10000) begin
      instr = riscv_instr::get_rand_instr(.include_category({LOAD, STORE}));
      `DV_CHECK_RANDOMIZE_FATAL(instr);
      $fwrite(fd, {instr.convert2asm(),"\n"});
    end
    repeat (10000) begin
      instr = riscv_instr::get_rand_instr(.exclude_category({LOAD, STORE , BRANCH}),
                                          .include_group({RV32I, RV32M}));
      `DV_CHECK_RANDOMIZE_FATAL(instr);
      $fwrite(fd, {instr.convert2asm(),"\n"});
    end
    $fclose(fd);
    `uvm_info(get_full_name(), $sformatf("%0s is generated", test_name), UVM_LOW)
  endtask

  virtual function void randomize_cfg();
    `DV_CHECK_RANDOMIZE_FATAL(cfg);
    `uvm_info(`gfn, $sformatf("riscv_instr_gen_config is randomized:\n%0s",
                    cfg.sprint()), UVM_LOW)
  endfunction

endclass
