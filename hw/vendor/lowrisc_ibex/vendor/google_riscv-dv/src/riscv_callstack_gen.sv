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

//-----------------------------------------------------------------------------------------
// RISC-V abstract program class
//
// This class is used to model a node in a callstack tree, no actual instruction is included
// in this class.
//-----------------------------------------------------------------------------------------

class riscv_program extends uvm_object;

  // ID of the current program
  rand program_id_t  program_id;
  // The level of current program in the call stack tree
  rand int unsigned  call_stack_level;
  // The list of all sub-programs of the current program
  rand program_id_t  sub_program_id[];

  constraint legal_c {
    unique{sub_program_id};
    foreach(sub_program_id[i]) {
      // Cannot call itself, recursive function call is not supported
      sub_program_id[i] != program_id;
    }
  }

  `uvm_object_utils(riscv_program)

  function new (string name = "");
    super.new(name);
  endfunction

  function string convert2string();
    string str = $sformatf("PID[%0d] Lv[%0d] :", program_id, call_stack_level);
    foreach(sub_program_id[i])
      str = $sformatf("%0s %0d", str, sub_program_id[i]);
    return str;
  endfunction

endclass

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

class riscv_callstack_gen extends uvm_object;

  // Number of programs in the call stack
  int program_cnt = 10;
  // Handles of all programs
  riscv_program program_h[];
  // Maximum call stack level
  int max_stack_level = 50;
`ifdef DSIM
  // Call stack level of each program
  bit[10:0] stack_level[];
`else
  // Call stack level of each program
  rand bit[10:0] stack_level[];

  constraint program_stack_level_c {
    // The stack level is assigned in ascending order to avoid call loop
    stack_level.size() == program_cnt;
    stack_level[0] == 0;
    foreach(stack_level[i]) {
      if(i > 0) {
        stack_level[i] inside {[1:program_cnt-1]};
        stack_level[i] >= stack_level[i-1];
        stack_level[i] <= stack_level[i-1]+1;
        stack_level[i] <= max_stack_level;
      }
    }
  }

`endif

  `uvm_object_utils(riscv_callstack_gen)

  function new (string name = "");
    super.new(name);
  endfunction

  // Init all program instances before randomization
  function void init(int program_cnt);
    this.program_cnt = program_cnt;
    program_h = new[program_cnt];
    foreach(program_h[i])
      program_h[i] = riscv_program::type_id::create($sformatf("program_%0d", i));
  endfunction

  // In the randomiation stage, only the stack level of each program is specified. The call stack
  // generation process is to build the call relationship between different programs. This is
  // implemented with post randomize rather than constraints for performance considerations.
  // Solving a complex call stack with SV constraint could take considerable time for the solver.
  function void post_randomize();
    int last_level;
    `ifdef DSIM
      stack_level = new[program_cnt];
      foreach (stack_level[i]) begin
        if (i > 0) begin
          stack_level[i] = stack_level[i-1] + $urandom_range(0,1);
        end
      end
    `endif
    last_level = stack_level[program_cnt-1];
    foreach(program_h[i]) begin
      program_h[i].program_id = i;
      program_h[i].call_stack_level = stack_level[i];
    end
    // Top-down generate the entire call stack.
    // A program can only call the programs in the next level.
    for(int i = 0; i < last_level; i ++) begin
      int total_sub_program_cnt;
      int program_list[$];
      int next_program_list[$];
      int sub_program_id_pool[];
      int sub_program_cnt[];
      int idx;
      for (int j=0; j<program_cnt; j++) begin
        if (stack_level[j] == i) begin
          program_list.push_back(j);
        end
        if (stack_level[j] == i+1) begin
          next_program_list.push_back(j);
        end
      end
      // Randmly duplicate some sub programs in the pool to create a case that
      // one sub program is called by multiple caller. Also it's possible to call
      // the same sub program in one program multiple times.
      total_sub_program_cnt = $urandom_range(next_program_list.size(),
                                             next_program_list.size() + 1);
      sub_program_id_pool = new[total_sub_program_cnt];
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(sub_program_id_pool,
        foreach(sub_program_id_pool[j]) {
          if(j < next_program_list.size()) {
            sub_program_id_pool[j] == next_program_list[j];
          } else {
            sub_program_id_pool[j] inside {next_program_list};
          }
        })
      sub_program_id_pool.shuffle();
      sub_program_cnt = new[program_list.size()];
      `uvm_info(get_full_name(), $sformatf("%0d programs @Lv%0d-> %0d programs at next level",
                program_list.size(), i, sub_program_id_pool.size()), UVM_LOW)
      // Distribute the programs of the next level among the programs of current level
      // Make sure all program has a caller so that no program is obsolete.
      foreach (sub_program_id_pool[j]) begin
        int caller_id = $urandom_range(0, sub_program_cnt.size()-1);
        sub_program_cnt[caller_id]++;
      end
      foreach(program_list[j]) begin
        int id = program_list[j];
        program_h[id].sub_program_id = new[sub_program_cnt[j]];
        `uvm_info(get_full_name(), $sformatf("%0d sub programs are assigned to program[%0d]",
                  sub_program_cnt[j], id), UVM_LOW)
        foreach(program_h[id].sub_program_id[k]) begin
          program_h[id].sub_program_id[k] = sub_program_id_pool[idx];
          idx++;
        end
      end
    end
  endfunction

  function void print_call_stack(program_id_t i, string str);
    if(program_h[i].sub_program_id.size() == 0)
      `uvm_info(get_full_name(), str, UVM_LOW)
    else begin
      foreach(program_h[i].sub_program_id[j]) begin
        print_call_stack(program_h[i].sub_program_id[j],
                         $sformatf("%0s -> %0d", str, program_h[i].sub_program_id[j]));
      end
    end
  endfunction

endclass
