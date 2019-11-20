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

  riscv_instr_base      instr_list[$];
  int unsigned          instr_cnt;
  string                label = "";
  // User can specify a small group of available registers to generate various hazard condition
  rand riscv_reg_t      avail_regs[];
  // Some additional reserved registers that should not be used as rd register
  // by this instruction stream
  riscv_reg_t           reserved_rd[];

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
    if(current_instr_cnt == 0) begin
      instr_list = new_instr;
      return;
    end
    if(idx == -1) begin
      idx = $urandom_range(0, current_instr_cnt-1);
      repeat(10) begin
       if (instr_list[idx].atomic) break;
       idx = $urandom_range(0, current_instr_cnt-1);
      end
      if (instr_list[idx].atomic) begin
        foreach (instr_list[i]) begin
          if (!instr_list[i].atomic) begin
            idx = i;
            break;
          end
        end
        if (instr_list[idx].atomic) begin
          `uvm_fatal(`gfn, $sformatf("Cannot inject the instruction"))
        end
      end
    end else if((idx > current_instr_cnt) || (idx < 0)) begin
      `uvm_error(`gfn, $sformatf("Cannot insert instr stream at idx %0d", idx))
    end
    // When replace is 1, the original instruction at this index will be removed. The label of the
    // original instruction will be copied to the head of inserted instruction stream.
    if(replace) begin
      new_instr[0].label = instr_list[idx].label;
      new_instr[0].has_label = instr_list[idx].has_label;
      if (idx == 0) begin
        instr_list = {new_instr, instr_list[idx+1:current_instr_cnt-1]};
      end else begin
        instr_list = {instr_list[0:idx-1], new_instr, instr_list[idx+1:current_instr_cnt-1]};
      end
    end else begin
      if (idx == 0) begin
        instr_list = {new_instr, instr_list[idx:current_instr_cnt-1]};
      end else begin
        instr_list = {instr_list[0:idx-1], new_instr, instr_list[idx:current_instr_cnt-1]};
      end
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
      })
    if (insert_instr_position.size() > 0) begin
      insert_instr_position.sort();
    end
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
  bit                     kernel_mode;
  riscv_instr_name_t      allowed_instr[$];
  int unsigned            category_dist[riscv_instr_category_t];

  `uvm_object_utils(riscv_rand_instr_stream)
  `uvm_object_new

  virtual function void create_instr_instance();
    riscv_instr_base instr;
    for(int i = 0; i < instr_cnt; i++) begin
      instr = riscv_instr_base::type_id::create($sformatf("instr_%0d", i));
      instr_list.push_back(instr);
    end
  endfunction

  virtual function void setup_allowed_instr(bit no_branch = 1'b0, bit no_load_store = 1'b1);
    allowed_instr = cfg.basic_instr;
    if (no_branch == 0) begin
      allowed_instr = {allowed_instr, cfg.instr_category[BRANCH]};
    end
    if (no_load_store == 0) begin
      allowed_instr = {allowed_instr, cfg.instr_category[LOAD], cfg.instr_category[STORE]};
    end
    setup_instruction_dist(no_branch, no_load_store);
  endfunction

  function setup_instruction_dist(bit no_branch = 1'b0, bit no_load_store = 1'b1);
    if (cfg.dist_control_mode) begin
      category_dist = cfg.category_dist;
      if (no_branch) begin
        category_dist[BRANCH] = 0;
      end
      if (no_load_store) begin
        category_dist[LOAD] = 0;
        category_dist[STORE] = 0;
      end
      `uvm_info(`gfn, $sformatf("setup_instruction_dist: %0d", category_dist.size()), UVM_LOW)
    end
  endfunction

  virtual function void gen_instr(bit no_branch = 1'b0, bit no_load_store = 1'b1,
                                  bit is_debug_program = 1'b0);
    setup_allowed_instr(no_branch, no_load_store);
    foreach(instr_list[i]) begin
      randomize_instr(instr_list[i], is_debug_program);
    end
    // Do not allow branch instruction as the last instruction because there's no
    // forward branch target
    while (instr_list[$].category == BRANCH) begin
      void'(instr_list.pop_back());
      if (instr_list.size() == 0) break;
    end
  endfunction

  function void randomize_instr(riscv_instr_base instr,
                                bit is_in_debug = 1'b0,
                                bit skip_rs1 = 1'b0,
                                bit skip_rs2 = 1'b0,
                                bit skip_rd  = 1'b0,
                                bit skip_imm = 1'b0,
                                bit skip_csr = 1'b0,
                                bit disable_dist = 1'b0);
    riscv_instr_name_t instr_name;
    if ((cfg.dist_control_mode == 1) && !disable_dist) begin
      riscv_instr_category_t category;
      int unsigned idx;
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(category,
        category dist {LOAD       := category_dist[LOAD],
                       STORE      := category_dist[STORE],
                       SHIFT      := category_dist[SHIFT],
                       ARITHMETIC := category_dist[ARITHMETIC],
                       LOGICAL    := category_dist[LOGICAL],
                       COMPARE    := category_dist[COMPARE],
                       BRANCH     := category_dist[BRANCH],
                       SYNCH      := category_dist[SYNCH],
                       CSR        := category_dist[CSR]};)
      idx = $urandom_range(0, cfg.instr_category[category].size() - 1);
      instr_name = cfg.instr_category[category][idx];
    // if set_dcsr_ebreak is set, we do not want to generate any ebreak
    // instructions inside the debug_rom
    end else if ((cfg.no_ebreak && !is_in_debug) ||
                 (!cfg.enable_ebreak_in_debug_rom && is_in_debug)) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(instr_name,
                                        instr_name inside {allowed_instr};
                                        !(instr_name inside {EBREAK, C_EBREAK});)
    end else begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(instr_name,
                                         instr_name inside {allowed_instr};)
    end
    instr.copy_base_instr(cfg.instr_template[instr_name]);
    `uvm_info(`gfn, $sformatf("%s: rs1:%0d, rs2:%0d, rd:%0d, imm:%0d",
                              instr.instr_name.name(),
                              instr.has_rs1,
                              instr.has_rs2,
                              instr.has_rd,
                              instr.has_imm), UVM_FULL)
    if (instr.has_imm && !skip_imm) begin
      instr.gen_rand_imm();
    end
    if (instr.has_rs1 && !skip_rs1) begin
      if (instr.is_compressed) begin
        // Compressed instruction could use the same register for rs1 and rd
        instr.rs1 = instr.gen_rand_gpr(
                         .included_reg(avail_regs),
                         .excluded_reg({reserved_rd, cfg.reserved_regs}));
      end else begin
        instr.rs1 = instr.gen_rand_gpr(.included_reg(avail_regs));
      end
    end
    if (instr.has_rs2 && !skip_rs2) begin
      instr.rs2 = instr.gen_rand_gpr(.included_reg(avail_regs));
    end
    if (instr.has_rd && !skip_rd) begin
      if (instr_name == C_LUI) begin
        instr.rd = instr.gen_rand_gpr(
                        .included_reg(avail_regs),
                        .excluded_reg({reserved_rd, cfg.reserved_regs, SP}));
      end else begin
        instr.rd = instr.gen_rand_gpr(
                        .included_reg(avail_regs),
                        .excluded_reg({reserved_rd, cfg.reserved_regs}));
      end
    end
    if ((instr.category == CSR) && !skip_csr) begin
      instr.gen_rand_csr(.privileged_mode(cfg.init_privileged_mode),
                         .enable_floating_point(cfg.enable_floating_point),
                         .illegal_csr_instr(cfg.enable_illegal_csr_instruction));
    end
    if (instr.has_fs1) begin
      instr.fs1 = instr.gen_rand_fpr();
    end
    if (instr.has_fs2) begin
      instr.fs2 = instr.gen_rand_fpr();
    end
    if (instr.has_fs3) begin
      instr.fs3 = instr.gen_rand_fpr();
    end
    if (instr.has_fd) begin
      instr.fd = instr.gen_rand_fpr();
    end
  endfunction

endclass
