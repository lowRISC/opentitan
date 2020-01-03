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

// TODO: Support other loop counter update instruction other than ADDI
// TODO: Support forward branch inside the loop

class riscv_loop_instr extends riscv_rand_instr_stream;

  rand riscv_reg_t         loop_cnt_reg[];
  rand riscv_reg_t         loop_limit_reg[];
  rand int                 loop_init_val[];
  rand int                 loop_step_val[];
  rand int                 loop_limit_val[];
  rand bit [2:0]           num_of_nested_loop;
  rand int                 num_of_instr_in_loop;
  rand riscv_instr_name_t  branch_type[];
  riscv_instr              loop_init_instr[];
  riscv_instr              loop_update_instr[];
  riscv_instr              loop_branch_instr[];
  riscv_instr              loop_branch_target_instr[];
  // Aggregated loop instruction stream
  riscv_instr         loop_instr[];

  constraint legal_loop_regs_c {
    solve num_of_nested_loop before loop_cnt_reg;
    solve num_of_nested_loop before loop_limit_reg;
    foreach (loop_cnt_reg[i]) {
      loop_cnt_reg[i] != ZERO;
      foreach (cfg.reserved_regs[j]) {
        loop_cnt_reg[i] != cfg.reserved_regs[j];
      }
    }
    foreach (loop_limit_reg[i]) {
      foreach (cfg.reserved_regs[j]) {
        loop_limit_reg[i] != cfg.reserved_regs[j];
      }
    }
    unique {loop_cnt_reg, loop_limit_reg};
    loop_cnt_reg.size() == num_of_nested_loop;
    loop_limit_reg.size() == num_of_nested_loop;
  }

  constraint loop_c {
    solve num_of_nested_loop before loop_init_val;
    solve num_of_nested_loop before loop_step_val;
    solve num_of_nested_loop before loop_limit_val;
    solve loop_limit_val before loop_limit_reg;
    solve branch_type before loop_init_val;
    solve branch_type before loop_step_val;
    solve branch_type before loop_limit_val;
    num_of_instr_in_loop inside {[1:25]};
    num_of_nested_loop inside {[1:2]};
    loop_init_val.size() == num_of_nested_loop;
    loop_step_val.size() == num_of_nested_loop;
    loop_limit_val.size() == num_of_nested_loop;
    branch_type.size() == num_of_nested_loop;
    foreach (branch_type[i]) {
      if (!cfg.disable_compressed_instr) {
        branch_type[i] inside {C_BNEZ, C_BEQZ, BEQ, BNE, BLTU, BLT, BGEU, BGE};
      } else {
        branch_type[i] inside {BEQ, BNE, BLTU, BLT, BGEU, BGE};
      }
    }
    foreach(loop_init_val[i]) {
      if (branch_type[i] inside {C_BNEZ, C_BEQZ}) {
        loop_limit_val[i] == 0;
        loop_limit_reg[i] == ZERO;
        loop_cnt_reg[i] inside {riscv_instr_pkg::compressed_gpr};
      } else {
        loop_limit_val[i] inside {[-20:20]};
        loop_limit_reg[i] != ZERO;
      }
      if (branch_type[i] inside {C_BNEZ, C_BEQZ, BEQ, BNE}) {
        ((loop_limit_val[i] - loop_init_val[i]) % loop_step_val[i] == 0) &&
        (loop_limit_val[i] != loop_init_val[i]);
      } else if (branch_type[i] == BGE) {
        loop_step_val[i] < 0;
      } else if (branch_type[i] == BGEU) {
        loop_step_val[i] < 0;
        loop_init_val[i] > 0;
        // Avoid count to negative
        loop_step_val[i] + loop_limit_val[i] > 0;
      } else if (branch_type[i] == BLT) {
        loop_step_val[i] > 0;
      } else if (branch_type[i] == BLTU) {
        loop_step_val[i] > 0;
        loop_limit_val[i] > 0;
      }
      loop_init_val[i]  inside {[-10:10]};
      loop_step_val[i]  inside {[-10:10]};
      if(loop_init_val[i] < loop_limit_val[i]) {
        loop_step_val[i] > 0;
      } else {
        loop_step_val[i] < 0;
      }
    }
  }

  `uvm_object_utils(riscv_loop_instr)
  `uvm_object_new

  function void post_randomize();
    reserved_rd = {loop_cnt_reg, loop_limit_reg};
    // Generate instructions that mixed with the loop instructions
    initialize_instr_list(num_of_instr_in_loop);
    gen_instr(1'b1);
    // Randomize the key loop instructions
    loop_init_instr   = new[num_of_nested_loop*2];
    loop_update_instr = new[num_of_nested_loop];
    loop_branch_instr = new[num_of_nested_loop];
    loop_branch_target_instr = new[num_of_nested_loop];
    for(int i = 0; i < num_of_nested_loop; i++) begin
      // Instruction to init the loop counter
      loop_init_instr[2*i] = riscv_instr::get_rand_instr(.include_instr({ADDI}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(loop_init_instr[2*i],
                                     rd == loop_cnt_reg[i];
                                     rs1 == ZERO;
                                     imm == loop_init_val[i];,
                                     "Cannot randomize loop init insturction")
      loop_init_instr[2*i].comment = $sformatf("init loop %0d counter", i);

      // Instruction to init loop limit
      loop_init_instr[2*i+1] = riscv_instr::get_rand_instr(.include_instr({ADDI}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(loop_init_instr[2*i+1],
                                     rd == loop_limit_reg[i];
                                     rs1 == ZERO;
                                     imm == loop_limit_val[i];,
                                     "Cannot randomize init loop instruction")
      loop_init_instr[2*i+1].comment = $sformatf("init loop %0d limit", i);

      // Branch target instruction, can be anything
      loop_branch_target_instr[i] = riscv_instr::get_rand_instr(
          .include_category({ARITHMETIC, LOGICAL, COMPARE}),
          .exclude_instr({C_ADDI16SP}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(loop_branch_target_instr[i],
                                     if (format == CB_FORMAT) {
                                       !(rs1 inside {reserved_rd, cfg.reserved_regs});
                                     }
                                     if (has_rd) {
                                       !(rd inside {reserved_rd, cfg.reserved_regs});
                                     }, "Cannot randomize branch target instruction")
      loop_branch_target_instr[i].label = $sformatf("%0s_%0d_t", label, i);

      // Instruction to update loop counter
      loop_update_instr[i] = riscv_instr::get_rand_instr(.include_instr({ADDI}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(loop_update_instr[i],
                                     rd == loop_cnt_reg[i];
                                     rs1 == loop_cnt_reg[i];
                                     imm == loop_step_val[i];,
                                     "Cannot randomize loop update instruction")
      loop_update_instr[i].comment = $sformatf("update loop %0d counter", i);

      // Backward branch instruction
      loop_branch_instr[i] = riscv_instr::get_rand_instr(.include_instr({branch_type[i]}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(loop_branch_instr[i],
                                     rs1 == loop_cnt_reg[i];
                                     if (!(branch_type[i] inside {C_BEQZ, C_BNEZ})) {
                                       rs2 == loop_limit_reg[i];
                                     },
                                     "Cannot randomize backward branch instruction")
      loop_branch_instr[i].comment = $sformatf("branch for loop %0d", i);
      loop_branch_instr[i].imm_str = loop_branch_target_instr[i].label;
      loop_branch_instr[i].branch_assigned = 1'b1;
    end
    // Randomly distribute the loop instruction in the existing instruction stream
    build_loop_instr_stream();
    mix_instr_stream(loop_instr, 1'b1);
    foreach(instr_list[i]) begin
      if(instr_list[i].label != "")
        instr_list[i].has_label = 1'b1;
      else
        instr_list[i].has_label = 1'b0;
      instr_list[i].atomic = 1'b1;
    end
  endfunction

  // Build the whole loop structure from innermost loop to the outermost loop
  function void build_loop_instr_stream();
    loop_instr.delete;
    for(int i = 0; i < num_of_nested_loop; i++) begin
      loop_instr = {loop_init_instr[2*i],
                    loop_init_instr[2*i+1],
                    loop_branch_target_instr[i],
                    loop_update_instr[i],
                    loop_instr,
                    loop_branch_instr[i]};
    end
    `uvm_info(get_full_name(), $sformatf("Totally %0d instructions have been added",
                               loop_instr.size()), UVM_HIGH)
  endfunction
endclass
