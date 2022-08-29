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

// TODO: Support other loop counter update instruction other than ADDI
// TODO: Support forward branch inside the loop

module riscv.gen.riscv_loop_instr;

import riscv.gen.riscv_instr_pkg: riscv_reg_t, riscv_instr_name_t,
  riscv_instr_category_t, compressed_gpr;
import riscv.gen.riscv_instr_stream: riscv_rand_instr_stream;
import riscv.gen.isa.riscv_instr: riscv_instr;

import std.format: format;

import esdl.rand: rand, constraint, randomize_with;
import esdl.data.bvec: ubvec;

import uvm;


class riscv_loop_instr: riscv_rand_instr_stream
{
  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }


  @rand riscv_reg_t[]         loop_cnt_reg;
  @rand riscv_reg_t[]         loop_limit_reg;
  @rand int[]                 loop_init_val;
  @rand int[]                 loop_step_val;
  @rand int[]                 loop_limit_val;
  @rand ubvec!3               num_of_nested_loop;
  @rand int                   num_of_instr_in_loop;
  @rand riscv_instr_name_t[]  branch_type;
  riscv_instr[]               loop_init_instr;
  riscv_instr[]               loop_update_instr;
  riscv_instr[]               loop_branch_instr;
  riscv_instr[]               loop_branch_target_instr;
  // Aggregated loop instruction stream
  riscv_instr[]               loop_instr;

  constraint! q{
    solve num_of_nested_loop before loop_cnt_reg;
    solve num_of_nested_loop before loop_limit_reg;
    foreach (lcnt; loop_cnt_reg) {
      lcnt != riscv_reg_t.ZERO;
      foreach (resr; cfg.reserved_regs) {
        lcnt != resr;
      }
    }
    foreach (llimit; loop_limit_reg) {
      foreach (resr; cfg.reserved_regs) {
        llimit != resr;
      }
    }
    unique [loop_cnt_reg, loop_limit_reg];
    loop_cnt_reg.length == num_of_nested_loop;
    loop_limit_reg.length == num_of_nested_loop;
  }  legal_loop_regs_c;

  constraint!  q{
    solve num_of_nested_loop before loop_init_val;
    solve num_of_nested_loop before loop_step_val;
    solve num_of_nested_loop before loop_limit_val;
    solve loop_limit_val before loop_limit_reg;
    solve branch_type before loop_init_val;
    solve branch_type before loop_step_val;
    solve branch_type before loop_limit_val;
    num_of_instr_in_loop inside [1:25];
    num_of_nested_loop inside [1:2];
    loop_init_val.length == num_of_nested_loop;
    loop_step_val.length == num_of_nested_loop;
    loop_limit_val.length == num_of_nested_loop;
    branch_type.length == num_of_nested_loop;
    foreach (btype; branch_type) {
      if (!cfg.disable_compressed_instr) {
	btype inside [riscv_instr_name_t.C_BNEZ, riscv_instr_name_t.C_BEQZ,
		      riscv_instr_name_t.BEQ, riscv_instr_name_t.BNE,
		      riscv_instr_name_t.BLTU, riscv_instr_name_t.BLT,
		      riscv_instr_name_t.BGEU, riscv_instr_name_t.BGE];
      }
      else {
	btype inside [riscv_instr_name_t.BEQ, riscv_instr_name_t.BNE,
		      riscv_instr_name_t.BLTU, riscv_instr_name_t.BLT,
		      riscv_instr_name_t.BGEU, riscv_instr_name_t.BGE];
      }
    }
    foreach (i, linit; loop_init_val) {
      if (branch_type[i] inside [riscv_instr_name_t.C_BNEZ, riscv_instr_name_t.C_BEQZ]) {
        loop_limit_val[i] == 0;
        // loop_limit_reg[i] == riscv_reg_t.ZERO; // handled in post_randomize
	loop_cnt_reg[i] inside [compressed_gpr]; // TBD -- FIXME -- EUVM
      }
      else {
        loop_limit_val[i] inside [-20..20];
        loop_limit_reg[i] != riscv_reg_t.ZERO;
      }
      if (branch_type[i] inside [riscv_instr_name_t.C_BNEZ, riscv_instr_name_t.C_BEQZ,
				 riscv_instr_name_t.BEQ, riscv_instr_name_t.BNE]) {
        ((loop_limit_val[i] - linit) % loop_step_val[i] == 0) &&
	  (loop_limit_val[i] != linit);
      }
      else if (branch_type[i] == riscv_instr_name_t.BGE) {
        loop_step_val[i] < 0;
      }
      else if (branch_type[i] == riscv_instr_name_t.BGEU) {
        loop_step_val[i] < 0;
        linit > 0;
        // Avoid count to negative
        loop_step_val[i] + loop_limit_val[i] > 0;
      }
      else if (branch_type[i] == riscv_instr_name_t.BLT) {
        loop_step_val[i] > 0;
      }
      else if (branch_type[i] == riscv_instr_name_t.BLTU) {
        loop_step_val[i] > 0;
        loop_limit_val[i] > 0;
      }
      linit inside [-10..10];
      loop_step_val[i] inside [-10..10];
      if (linit < loop_limit_val[i]) {
        loop_step_val[i] > 0;
      }
      else {
        loop_step_val[i] < 0;
      }
    }
  } loop_c;

  void post_randomize() {
    reserved_rd = loop_cnt_reg ~ loop_limit_reg;
    // Generate instructions that mixed with the loop instructions
    initialize_instr_list(num_of_instr_in_loop);
    gen_instr(true);
    // Randomize the key loop instructions
    loop_init_instr.length   = num_of_nested_loop*2;
    loop_update_instr.length = num_of_nested_loop;
    loop_branch_instr.length = num_of_nested_loop;
    loop_branch_target_instr.length = num_of_nested_loop;
    for (int i = 0; i < num_of_nested_loop; i++) {
      if (branch_type[i] == riscv_instr_name_t.C_BNEZ ||
	  branch_type[i] == riscv_instr_name_t.C_BEQZ) {
	loop_limit_reg[i] = riscv_reg_t.ZERO;
      }
      // Instruction to init the loop counter
      loop_init_instr[2*i] =
	cfg.instr_registry.get_rand_instr([riscv_instr_name_t.ADDI]);
      //  `DV_CHECK_RANDOMIZE_WITH_FATAL(loop_init_instr[2*i],
      loop_init_instr[2*i].randomize_with!q{
	rd == $0;
	rs1 == riscv_reg_t.ZERO;
	imm == $1;
      } (loop_cnt_reg[i], loop_init_val[i]);

      loop_init_instr[2*i].comment = format("init loop %0d counter", i);

      // Instruction to init loop limit
      loop_init_instr[2*i+1] =
	cfg.instr_registry.get_rand_instr([riscv_instr_name_t.ADDI]);
      //  `DV_CHECK_RANDOMIZE_WITH_FATAL(l,
      loop_init_instr[2*i+1].randomize_with! q{
	rd == $0;
	rs1 == riscv_reg_t.ZERO;
	imm == $1;
      } (loop_limit_reg[i], loop_limit_val[i]);

      loop_init_instr[2*i+1].comment = format("init loop %0d limit", i);

      // Branch target instruction, can be anything
      loop_branch_target_instr[i] =
	cfg.instr_registry.get_rand_instr(null, [riscv_instr_name_t.C_ADDI16SP],
					  [riscv_instr_category_t.ARITHMETIC,
					   riscv_instr_category_t.LOGICAL,
					   riscv_instr_category_t.COMPARE]);
      //DV_CHECK_RANDOMIZE_WITH_FATAL(,
      loop_branch_target_instr[i].randomize_with! q{
	if (instr_format == riscv_instr_format_t.CB_FORMAT) {
	  rs1 !inside [$0, $1];
	}
	if (has_rd) {
	  rd !inside [$0, $1];
	}
      } (reserved_rd, cfg.reserved_regs);

      loop_branch_target_instr[i].label = format("%0s_%0d_t", label, i);

      // Instruction to update loop counter
      loop_update_instr[i] =
	cfg.instr_registry.get_rand_instr([riscv_instr_name_t.ADDI]);
      //DV_CHECK_RANDOMIZE_WITH_FATAL(],
      loop_update_instr[i].randomize_with! q{
	rd == $0;
	rs1 == $0;
	imm == $1;
      } (loop_cnt_reg[i], loop_step_val[i]);
      loop_update_instr[i].comment = format("update loop %0d counter", i);

      // Backward branch instruction
      loop_branch_instr[i] = cfg.instr_registry.get_rand_instr([branch_type[i]]);
      // `DV_CHECK_RANDOMIZE_WITH_FATAL(,
      loop_branch_instr[i].randomize_with! q{
	rs1 == $0;
	if ($1 !inside [riscv_instr_name_t.C_BEQZ,
			riscv_instr_name_t.C_BNEZ]) {
	  rs2 == $2;
	}
      } (loop_cnt_reg[i], branch_type[i], loop_limit_reg[i]);

      loop_branch_instr[i].comment = format("branch for loop %0d", i);
      loop_branch_instr[i].imm_str = loop_branch_target_instr[i].label;
      loop_branch_instr[i].branch_assigned = true;
    }
    // Randomly distribute the loop instruction in the existing instruction stream
    build_loop_instr_stream();
    mix_instr_stream(loop_instr, true);
    foreach (instr; instr_list) {
      if (instr.label != "")
        instr.has_label = true;
      else
        instr.has_label = false;
      instr.atomic = true;
    }
  }

  // Build the whole loop structure from innermost loop to the outermost loop
  void build_loop_instr_stream() {
    loop_instr.length = 0;
    for (int i = 0; i < num_of_nested_loop; i++) {
      loop_instr = [loop_init_instr[2*i],
                    loop_init_instr[2*i+1],
                    loop_branch_target_instr[i],
                    loop_update_instr[i]] ~
	loop_instr ~
	loop_branch_instr[i];
    }
    uvm_info(get_full_name(), format("Totally %0d instructions have been added",
				     loop_instr.length), UVM_HIGH);
  }
}
