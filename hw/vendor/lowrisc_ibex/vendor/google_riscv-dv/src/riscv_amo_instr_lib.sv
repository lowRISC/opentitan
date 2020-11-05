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

// Base class for AMO instruction stream
class riscv_amo_base_instr_stream extends riscv_mem_access_stream;

  rand int unsigned  num_amo;
  rand int unsigned  num_mixed_instr;
  rand int           offset[];
  rand riscv_reg_t   rs1_reg[];
  rand int           num_of_rs1_reg;
  int unsigned       data_page_id;
  int unsigned       max_offset;

  // User can specify a small group of available registers to generate various hazard condition
  rand riscv_reg_t   avail_regs[];

  constraint num_of_rs1_reg_c {
    num_of_rs1_reg == 1;
  }

  constraint rs1_c {
    solve num_of_rs1_reg before rs1_reg;
    rs1_reg.size() == num_of_rs1_reg;
    offset.size() == num_of_rs1_reg;
    foreach (rs1_reg[i]) {
      !(rs1_reg[i] inside {cfg.reserved_regs, reserved_rd, ZERO});
    }
    unique {rs1_reg};
  }

  constraint addr_range_c {
    foreach (offset[i]) {
      offset[i] inside {[0 : max_offset - 1]};
    }
  }

  constraint aligned_amo_c {
    foreach (offset[i]) {
      if (XLEN == 32) {
        offset[i] % 4 == 0;
      } else {
        offset[i] % 8 == 0;
      }
    }
  }

  `uvm_object_utils(riscv_amo_base_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    data_page = cfg.amo_region;
    max_data_page_id = data_page.size();
    data_page_id = $urandom_range(0, max_data_page_id - 1);
    max_offset = data_page[data_page_id].size_in_bytes;
  endfunction

  // Use "la" instruction to initialize the offset regiseter
  virtual function void init_offset_reg();
    foreach (rs1_reg[i]) begin
      riscv_pseudo_instr la_instr;
      la_instr = riscv_pseudo_instr::type_id::create("la_instr");
      la_instr.pseudo_instr_name = LA;
      la_instr.rd = rs1_reg[i];
      la_instr.imm_str = $sformatf("%0s+%0d", cfg.amo_region[data_page_id].name, offset[i]);
      instr_list.push_front(la_instr);
    end
  endfunction

  function void post_randomize();
    gen_amo_instr();
    reserved_rd = {reserved_rd, rs1_reg};
    add_mixed_instr(num_mixed_instr);
    init_offset_reg();
    super.post_randomize();
  endfunction

  // AMO instruction generation
  virtual function void gen_amo_instr();
  endfunction

endclass : riscv_amo_base_instr_stream

// A pair of LR/SC instruction
class riscv_lr_sc_instr_stream extends riscv_amo_base_instr_stream;

  riscv_instr lr_instr;
  riscv_instr sc_instr;

  constraint legal_c {
    num_amo == 1;
    num_mixed_instr inside {[0:15]};
  }

  `uvm_object_utils(riscv_lr_sc_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void gen_amo_instr();
    riscv_instr_name_t allowed_lr_instr[];
    riscv_instr_name_t allowed_sc_instr[];
    if (RV32A inside {supported_isa}) begin
      allowed_lr_instr = {LR_W};
      allowed_sc_instr = {SC_W};
    end
    if (RV64A inside {supported_isa}) begin
      allowed_lr_instr = {allowed_lr_instr, LR_D};
      allowed_sc_instr = {allowed_sc_instr, SC_D};
    end
    lr_instr = riscv_instr::get_rand_instr(.include_instr({allowed_lr_instr}));
    sc_instr = riscv_instr::get_rand_instr(.include_instr({allowed_sc_instr}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(lr_instr,
      rs1 == rs1_reg[0];
      if (reserved_rd.size() > 0) {
        !(rd inside {reserved_rd});
      }
      if (cfg.reserved_regs.size() > 0) {
        !(rd inside {cfg.reserved_regs});
      }
      rd != rs1_reg[0];
    )
    `DV_CHECK_RANDOMIZE_WITH_FATAL(sc_instr,
      rs1 == rs1_reg[0];
      if (reserved_rd.size() > 0) {
        !(rd inside {reserved_rd});
      }
      if (cfg.reserved_regs.size() > 0) {
        !(rd inside {cfg.reserved_regs});
      }
      rd != rs1_reg[0];
    )
    instr_list.push_back(lr_instr);
    instr_list.push_back(sc_instr);
  endfunction

  // section 8.3 Eventual Success of Store-Conditional Instructions
  // An LR/SC sequence begins with an LR instruction and ends with an SC instruction.
  // The dynamic code executed between the LR and SC instructions can only contain
  // instructions from the base “I” instruction set, excluding loads, stores, backward
  // jumps, taken backward branches, JALR, FENCE, and SYSTEM instructions. If the “C”
  // extension is supported, then compressed forms of the aforementioned “I” instructions
  // are also permitted.
  virtual function void add_mixed_instr(int instr_cnt);
    riscv_instr instr;
    int i;
    setup_allowed_instr(.no_branch(1), .no_load_store(1));
    while (i < instr_cnt) begin
      instr = riscv_instr::type_id::create("instr");
      randomize_instr(instr, .include_group({RV32I, RV32C}));
      if (!(instr.category inside {SYNCH, SYSTEM})) begin
        insert_instr(instr);
        i++;
      end
    end
  endfunction

endclass : riscv_lr_sc_instr_stream

class riscv_amo_instr_stream extends riscv_amo_base_instr_stream;

  riscv_instr amo_instr[];

  constraint reasonable_c {
    solve num_amo before num_mixed_instr;
    num_amo inside {[1 : 10]};
    num_mixed_instr inside {[0 : num_amo]};
  }

  constraint num_of_rs1_reg_c {
    solve num_amo before num_of_rs1_reg;
    num_of_rs1_reg inside {[1 : num_amo]};
    num_of_rs1_reg < 5;
  }

  `uvm_object_utils(riscv_amo_instr_stream)
  `uvm_object_new

  virtual function void gen_amo_instr();
    amo_instr = new[num_amo];
    foreach (amo_instr[i]) begin
      amo_instr[i] = riscv_instr::get_rand_instr(.include_category({AMO}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(amo_instr[i],
        if (reserved_rd.size() > 0) {
          !(rd inside {reserved_rd});
        }
        if (cfg.reserved_regs.size() > 0) {
          !(rd inside {cfg.reserved_regs});
        }
        rs1 inside {rs1_reg};
        !(rd inside {rs1_reg});
      )
      instr_list.push_front(amo_instr[i]);
    end
  endfunction

endclass : riscv_amo_instr_stream


class riscv_vector_amo_instr_stream extends riscv_vector_load_store_instr_stream;

  constraint amo_address_mode_c {
    // AMO operation uses indexed address mode
    address_mode == INDEXED;
  }

  `uvm_object_utils(riscv_vector_amo_instr_stream)
  `uvm_object_new

  virtual function void add_element_vec_load_stores();
    allowed_instr = {VAMOSWAPE_V, VAMOADDE_V, VAMOXORE_V,
                     VAMOANDE_V, VAMOORE_V, VAMOMINE_V,
                     VAMOMAXE_V, VAMOMINUE_V, VAMOMAXUE_V, allowed_instr};
  endfunction

endclass : riscv_vector_amo_instr_stream
