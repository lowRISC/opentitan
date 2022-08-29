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

//-----------------------------------------------------------------------------------------
// RISC-V abstract program class
//
// This class is used to model a node in a callstack tree, no actual instruction is included
// in this class.
//-----------------------------------------------------------------------------------------

module riscv.gen.riscv_callstack_gen;

import riscv.gen.riscv_instr_pkg: program_id_t;

import esdl.rand: constraint, rand, randomize;
import esdl.data.bvec: ubvec, toubvec;
import esdl.base.rand: urandom, shuffle;

import uvm;

import std.format: format;


class riscv_program: uvm_object
{
  mixin uvm_object_utils;

  // ID of the current program
  @rand program_id_t  program_id;
  // The level of current program in the call stack tree
  @rand uint   call_stack_level;
  // The list of all sub-programs of the current program
  @rand program_id_t[] sub_program_id;

  constraint! q{
    unique [sub_program_id];
    foreach (id; sub_program_id) {
      // Cannot call itself, recursive function call is not supported
      id != program_id;
    }
  } legal_c;

  this(string name = "") {
    super(name);
  }

  override string convert2string() {
    string str = format("PID[%0d] Lv[%0d] :", program_id, call_stack_level);
    foreach (id; sub_program_id) {
      str = format("%0s %0d", str, id);
    }
    return str;
  }

}

//-----------------------------------------------------------------------------------------
// RISC-V assembly program call stack generator
//
// The call stack is generated as a tree structure to avoid dead call loop.
// Level 0:                     P0
//                           /  |  \
// Level 1:                 P1  P2  P3
//                          |     \/  \
// Level 2:                 P4    P5   P6
//                                 |
// Level 3:                        P7
//
// Rules: A program can only call the program in the next level.
//        A program can be called many times by other upper level programs.
//        A program can call the same lower level programs multiple times.
//-----------------------------------------------------------------------------------------

class riscv_callstack_gen : uvm_object
{
  mixin uvm_object_utils;

  // Number of programs in the call stack
  int program_cnt = 10;
  // Handles of all programs
  riscv_program[]  program_h;
  // Maximum call stack level
  int max_stack_level = 50;
  @rand ubvec!11[] stack_level;

  constraint! q{
    // The stack level is assigned in ascending order to avoid call loop
    stack_level.length == program_cnt;
    stack_level[0] == 0;
    foreach (i, slevel; stack_level) {
      if (i > 0) {
        slevel inside [1..program_cnt];
        slevel >= stack_level[i-1];
        slevel <= stack_level[i-1]+1;
        slevel <= max_stack_level;
      }
    }
  } program_stack_level_c;

  //`endif

  this(string name = "") {
    super(name);
  }

  // Init all program instances before randomization
  void init(int program_cnt) {
    this.program_cnt = program_cnt;
    program_h.length = program_cnt;
    foreach(i, ref prog; program_h) {
      prog = riscv_program.type_id.create(format("program_%0d", i));
    }
  }

  // In the randomiation stage, only the stack level of each program is specified. The call stack
  // generation process is to build the call relationship between different programs. This is
  // implemented with post randomize rather than constraints for performance considerations.
  // Solving a complex call stack with SV constraint could take considerable time for the solver.
  void post_randomize() {
    int last_level;
    last_level = stack_level[program_cnt-1];
    foreach(i, prog; program_h) {
      prog.program_id = toubvec!16(i);
      prog.call_stack_level = stack_level[i];
    }
    // Top-down generate the entire call stack.
    // A program can only call the programs in the next level.
    for(int i = 0; i < last_level; i ++) {
      int total_sub_program_cnt;
      int[] program_list;
      int[] next_program_list;
      int[] sub_program_id_pool;
      int[] sub_program_cnt;
      int idx;
      for (int j=0; j<program_cnt; j++) {
        if (stack_level[j] == i) {
          program_list ~= j;
        }
        if (stack_level[j] == i+1) {
	  next_program_list ~=j;
        }
      }
      // Randmly duplicate some sub programs in the pool to create a case that
      // one sub program is called by multiple caller. Also it's possible to call
      // the same sub program in one program multiple times.
      int len = cast(int) next_program_list.length;
      total_sub_program_cnt = urandom(len, (len + 2));

      sub_program_id_pool.length = total_sub_program_cnt;
      foreach (j, ref spid; sub_program_id_pool) {
	if (j < next_program_list.length)
	  spid = next_program_list[j];
	else {
	  int nextid = urandom(0, cast(int) next_program_list.length);
	  spid = next_program_list[nextid];
	}
      }


      sub_program_id_pool.shuffle();
      sub_program_cnt.length = program_list.length;
      uvm_info(get_full_name(), format("%0d programs @Lv%0d-> %0d programs at next level",
				       program_list.length, i, sub_program_id_pool.length), UVM_LOW);
      // Distribute the programs of the next level among the programs of current level
      // Make sure all program has a caller so that no program is obsolete.
      foreach (spid; sub_program_id_pool) {
        int caller_id = urandom(0, cast(int) sub_program_cnt.length);
        sub_program_cnt[caller_id]++;
      }
      foreach (j, id; program_list) {
        program_h[id].sub_program_id.length = sub_program_cnt[j];
        uvm_info(get_full_name(), format("%0d sub programs are assigned to program[%0d]",
					 sub_program_cnt[j], id), UVM_LOW);
        foreach (ref spid; program_h[id].sub_program_id) {
	  spid = toubvec!16(sub_program_id_pool[idx]);
          idx++;
        }
      }
    }
  }

  void print_call_stack(program_id_t i, string str) {
    if (program_h[i].sub_program_id.length == 0)
      uvm_info(get_full_name(), str, UVM_LOW);
    else {
      foreach (spid; program_h[i].sub_program_id) {
        print_call_stack(spid, format("%0s -> %0d", str, spid));
      }
    }
  }

}
