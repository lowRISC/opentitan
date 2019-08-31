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

// Base class for RISC-V instruction stream
// A instruction stream here is a  queue of RISC-V basic instructions.
// This class also provides some functions to manipulate the instruction stream, like insert a new
// instruction, mix two instruction streams etc.
class riscv_instr_stream extends uvm_object;

  rand riscv_instr_base instr_list[$];
  int unsigned          instr_cnt;
  string                label = "";

  `uvm_object_utils(riscv_instr_stream)
  `uvm_object_new

  // Initialize the instruction stream, create each instruction instance
  function void initialize_instr_list(int unsigned instr_cnt);
    instr_list = {};
    this.instr_cnt = instr_cnt;
    create_instr_instance();
  endfunction

  virtual function void create_instr_instance();
    riscv_instr_base instr;
    for(int i = 0; i < instr_cnt; i++) begin
      instr = riscv_instr_base::type_id::create($sformatf("instr_%0d", i));
      instr_list.push_back(instr);
    end
  endfunction

  // Insert an instruction to the existing instruction stream at the given index
  // When index is -1, the instruction is injected at a random location
  function void insert_instr(riscv_instr_base instr, int idx = -1);
    int current_instr_cnt = instr_list.size();
    if(idx == -1) begin
      idx = $urandom_range(0, current_instr_cnt-1);
      while(instr_list[idx].atomic) begin
       idx = $urandom_range(0, current_instr_cnt-1);
      end
    end else if((idx > current_instr_cnt) || (idx < 0)) begin
      `uvm_error(`gfn, $sformatf("Cannot insert instr:%0s at idx %0d",
                       instr.convert2asm(), idx))
    end
    instr_list.insert(idx, instr);
  endfunction

  // Insert an instruction to the existing instruction stream at the given index
  // When index is -1, the instruction is injected at a random location
  // When replace is 1, the original instruction at the inserted position will be replaced
  function void insert_instr_stream(riscv_instr_base new_instr[], int idx = -1, bit replace = 1'b0);
    int current_instr_cnt = instr_list.size();
    int new_instr_cnt = new_instr.size();
    if(idx == -1) begin
      idx = $urandom_range(0, current_instr_cnt-1);
      while(instr_list[idx].atomic) begin
       idx = $urandom_range(0, current_instr_cnt-1);
      end
    end else if((idx > current_instr_cnt) || (idx < 0)) begin
      `uvm_error(`gfn, $sformatf("Cannot insert instr stream at idx %0d", idx))
    end
    // When replace is 1, the original instruction at this index will be removed. The label of the
    // original instruction will be copied to the head of inserted instruction stream.
    if(replace) begin
      new_instr[0].label = instr_list[idx].label;
      new_instr[0].has_label = instr_list[idx].has_label;
      instr_list = {instr_list[0:idx-1], new_instr, instr_list[idx+1:current_instr_cnt-1]};
    end else begin
      instr_list = {instr_list[0:idx-1], new_instr, instr_list[idx:current_instr_cnt-1]};
    end
  endfunction

  // Mix the input instruction stream with the original instruction, the instruction order is
  // preserved. When 'contained' is set, the original instruction stream will be inside the
  // new instruction stream with the first and last instruction from the input instruction stream.
  function void mix_instr_stream(riscv_instr_base new_instr[], bit contained = 1'b0);
    int current_instr_cnt = instr_list.size();
    int insert_instr_position[];
    int new_instr_cnt = new_instr.size();
    insert_instr_position = new[new_instr_cnt];
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(insert_instr_position,
      foreach(insert_instr_position[i]) {
        insert_instr_position[i] inside {[0:current_instr_cnt-1]};
        if(i > 0) {
          insert_instr_position[i] >= insert_instr_position[i-1];
        }
      })
    if(contained) begin
      insert_instr_position[0] = 0;
      if(new_instr_cnt > 1)
        insert_instr_position[new_instr_cnt-1] = current_instr_cnt-1;
    end
    foreach(new_instr[i]) begin
      insert_instr(new_instr[i], insert_instr_position[i] + i);
    end
  endfunction

  function string convert2string();
    string str;
    foreach(instr_list[i])
      str = {str, instr_list[i].convert2asm(), "\n"};
    return str;
  endfunction

endclass

// Generate a random instruction stream based on the configuration
// There are two ways to use this class to generate instruction stream
// 1. For short instruction stream, you can call randomize() directly.
// 2. For long instruction stream (>1K), randomize() all instructions together might take a long
// time for the constraint solver. In this case, you can call gen_instr to generate instructions
// one by one. The time only grows linearly with the instruction count
class riscv_rand_instr_stream extends riscv_instr_stream;

  riscv_instr_gen_config  cfg;
  bit                     access_u_mode_mem = 1'b1;
  int                     max_load_store_offset;
  int                     max_data_page_id;

  // Some additional reserved registers that should not be used as rd register
  // by this instruction stream
  riscv_reg_t reserved_rd[];

  constraint avoid_reserved_rd_c {
    if(reserved_rd.size() > 0) {
      foreach(instr_list[i]) {
        !(instr_list[i].rd inside {reserved_rd});
      }
    }
  }

  `uvm_object_utils(riscv_rand_instr_stream)
  `uvm_object_new

  virtual function void create_instr_instance();
    riscv_rand_instr instr;
    if(cfg == null) begin
      `uvm_fatal(get_full_name(), "cfg object is null")
    end
    for(int i = 0; i < instr_cnt; i++) begin
      instr = riscv_rand_instr::type_id::create($sformatf("instr_%0d", i));
      instr.cfg = cfg;
      instr.reserved_rd = reserved_rd;
      instr_list.push_back(instr);
    end
  endfunction

  function void pre_randomize();
    if(access_u_mode_mem) begin
      max_load_store_offset = riscv_instr_pkg::data_page_size;
      max_data_page_id = riscv_instr_pkg::num_of_data_pages;
    end else begin
      max_load_store_offset = riscv_instr_pkg::kernel_data_page_size;
      max_data_page_id = riscv_instr_pkg::num_of_kernel_data_pages;
    end
  endfunction

  virtual function void gen_instr(bit no_branch = 1'b0,
                                  bit no_load_store = 1'b1,
                                  bit enable_hint_instr = 1'b0);
    foreach(instr_list[i]) begin
      `DV_CHECK_RANDOMIZE_WITH_FATAL(instr_list[i],
        // The last instruction cannot be branch instruction as there's no forward branch target.
        if((i == instr_list.size() - 1) || no_branch) {
          category != BRANCH;
        }
        if(no_load_store) {
          !(category inside {LOAD, STORE});
        })
    end
  endfunction

endclass
