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
  rand int           base;
  rand riscv_reg_t   rs1_reg;
  rand int unsigned  data_page_id;
  rand int           max_load_store_offset;

  // User can specify a small group of available registers to generate various hazard condition
  rand riscv_reg_t   avail_regs[];

  `uvm_object_utils(riscv_amo_base_instr_stream)

  constraint rs1_c {
    !(rs1_reg inside {cfg.reserved_regs, reserved_rd, ZERO});
  }

  constraint addr_range_c {
    data_page_id < max_data_page_id;
    base inside {[0 : max_load_store_offset-1]};
  }

  constraint aligned_amo_c {
    if (XLEN == 32) {
      base % 4 == 0;
    } else {
      base % 8 == 0;
    }
  }

  function new(string name = "");
    super.new(name);
  endfunction

  function void post_randomize();
    gen_amo_instr();
    // rs1 cannot be modified by other instructions
    if(!(rs1_reg inside {reserved_rd})) begin
      reserved_rd = {reserved_rd, rs1_reg};
    end
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id);
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
    lr_instr = riscv_instr::get_rand_instr(.include_instr({LR_W, LR_D}));
    sc_instr = riscv_instr::get_rand_instr(.include_instr({SC_W, SC_D}));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(lr_instr,
      rs1 == rs1_reg;
      if (reserved_rd.size() > 0) {
        !(rd inside {reserved_rd});
      }
      if (cfg.reserved_regs.size() > 0) {
        !(rd inside {cfg.reserved_regs});
      }
      rd != rs1_reg;
    )
    `DV_CHECK_RANDOMIZE_WITH_FATAL(sc_instr,
      rs1 == rs1_reg;
      if (reserved_rd.size() > 0) {
        !(rd inside {reserved_rd});
      }
      if (cfg.reserved_regs.size() > 0) {
        !(rd inside {cfg.reserved_regs});
      }
      rd != rs1_reg;
    )
    instr_list.push_back(lr_instr);
    instr_list.push_back(sc_instr);
  endfunction

endclass : riscv_lr_sc_instr_stream

class riscv_amo_instr_stream extends riscv_amo_base_instr_stream;

  riscv_instr amo_instr[];

  constraint reasonable_c {
    solve num_amo before num_mixed_instr;
    num_amo inside {[1:10]};
    num_mixed_instr inside {[0:2*num_amo]};
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
        rs1 == rs1_reg;
        rd != rs1_reg;
      )
      instr_list.push_front(amo_instr[i]);
    end
  endfunction

endclass : riscv_amo_instr_stream
