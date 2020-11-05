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

  riscv_instr           instr_list[$];
  int unsigned          instr_cnt;
  string                label = "";
  // User can specify a small group of available registers to generate various hazard condition
  rand riscv_reg_t      avail_regs[];
  // Some additional reserved registers that should not be used as rd register
  // by this instruction stream
  riscv_reg_t           reserved_rd[];
  int                   hart;

  `uvm_object_utils(riscv_instr_stream)
  `uvm_object_new

  // Initialize the instruction stream, create each instruction instance
  function void initialize_instr_list(int unsigned instr_cnt);
    instr_list = {};
    this.instr_cnt = instr_cnt;
    create_instr_instance();
  endfunction

  virtual function void create_instr_instance();
    riscv_instr instr;
    for(int i = 0; i < instr_cnt; i++) begin
      instr = riscv_instr::type_id::create($sformatf("instr_%0d", i));
      instr_list.push_back(instr);
    end
  endfunction

  // Insert an instruction to the existing instruction stream at the given index
  // When index is -1, the instruction is injected at a random location
  function void insert_instr(riscv_instr instr, int idx = -1);
    int current_instr_cnt = instr_list.size();
    if (current_instr_cnt == 0) begin
      idx = 0;
    end else if (idx == -1) begin
      idx = $urandom_range(0, current_instr_cnt-1);
      while(instr_list[idx].atomic) begin
       idx += 1;
       if (idx == current_instr_cnt - 1) begin
         instr_list = {instr_list, instr};
         return;
       end
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
  function void insert_instr_stream(riscv_instr new_instr[], int idx = -1, bit replace = 1'b0);
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
  function void mix_instr_stream(riscv_instr new_instr[], bit contained = 1'b0);
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
    riscv_instr instr;
    for (int i = 0; i < instr_cnt; i++) begin
      instr_list.push_back(null);
    end
  endfunction

  virtual function void setup_allowed_instr(bit no_branch = 1'b0, bit no_load_store = 1'b1);
    allowed_instr = riscv_instr::basic_instr;
    if (no_branch == 0) begin
      allowed_instr = {allowed_instr, riscv_instr::instr_category[BRANCH]};
    end
    if (no_load_store == 0) begin
      allowed_instr = {allowed_instr, riscv_instr::instr_category[LOAD],
                                      riscv_instr::instr_category[STORE]};
    end
    setup_instruction_dist(no_branch, no_load_store);
  endfunction

  virtual function void randomize_avail_regs();
    if(avail_regs.size() > 0) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(avail_regs,
                                         unique{avail_regs};
                                         avail_regs[0] inside {[S0 : A5]};
                                         foreach(avail_regs[i]) {
                                           !(avail_regs[i] inside {cfg.reserved_regs, reserved_rd});
                                         },
                                         "Cannot randomize avail_regs")
    end
  endfunction

  function void setup_instruction_dist(bit no_branch = 1'b0, bit no_load_store = 1'b1);
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

  function void randomize_instr(output riscv_instr instr,
                                input  bit is_in_debug = 1'b0,
                                input  bit disable_dist = 1'b0,
                                input  riscv_instr_group_t include_group[$] = {});
    riscv_instr_name_t exclude_instr[];
    if ((SP inside {reserved_rd, cfg.reserved_regs}) ||
        ((avail_regs.size() > 0) && !(SP inside {avail_regs}))) begin
      exclude_instr = {C_ADDI4SPN, C_ADDI16SP, C_LWSP, C_LDSP};
    end
    // Post-process the allowed_instr and exclude_instr lists to handle
    // adding ebreak instructions to the debug rom.
    if (is_in_debug) begin
      if (cfg.no_ebreak && cfg.enable_ebreak_in_debug_rom) begin
        allowed_instr = {allowed_instr, EBREAK, C_EBREAK};
      end else if (!cfg.no_ebreak && !cfg.enable_ebreak_in_debug_rom) begin
        exclude_instr = {exclude_instr, EBREAK, C_EBREAK};
      end
    end
    instr = riscv_instr::get_rand_instr(.include_instr(allowed_instr),
                                        .exclude_instr(exclude_instr),
                                        .include_group(include_group));
    instr.m_cfg = cfg;
    randomize_gpr(instr);
  endfunction

  function void randomize_gpr(riscv_instr instr);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if (avail_regs.size() > 0) {
        if (has_rs1) {
          rs1 inside {avail_regs};
        }
        if (has_rs2) {
          rs2 inside {avail_regs};
        }
        if (has_rd) {
          rd  inside {avail_regs};
        }
      }
      foreach (reserved_rd[i]) {
        if (has_rd) {
          rd != reserved_rd[i];
        }
        if (format == CB_FORMAT) {
          rs1 != reserved_rd[i];
        }
      }
      foreach (cfg.reserved_regs[i]) {
        if (has_rd) {
          rd != cfg.reserved_regs[i];
        }
        if (format == CB_FORMAT) {
          rs1 != cfg.reserved_regs[i];
        }
      }
      // TODO: Add constraint for CSR, floating point register
    )
  endfunction

  function riscv_instr get_init_gpr_instr(riscv_reg_t gpr, bit [XLEN-1:0] val);
    riscv_pseudo_instr li_instr;
    li_instr = riscv_pseudo_instr::type_id::create("li_instr");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(li_instr,
       pseudo_instr_name == LI;
       rd == gpr;
    )
    li_instr.imm_str = $sformatf("0x%0x", val);
    return li_instr;
  endfunction

  function void add_init_vector_gpr_instr(riscv_vreg_t gpr, bit [XLEN-1:0] val);
    riscv_vector_instr instr;
    $cast(instr, riscv_instr::get_instr(VMV));
    instr.m_cfg = cfg;
    instr.avoid_reserved_vregs_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      va_variant == VX;
      vd == gpr;
      rs1 == cfg.gpr[0];
    )
    instr_list.push_front(instr);
    instr_list.push_front(get_init_gpr_instr(cfg.gpr[0], val));
  endfunction

endclass
