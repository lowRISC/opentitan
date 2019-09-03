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
class riscv_amo_base_instr_stream extends riscv_directed_instr_stream;

  rand int unsigned  num_amo;
  rand int unsigned  num_mixed_instr;
  rand int           base;
  rand riscv_reg_t   rs1_reg;
  riscv_reg_t        reserved_rd[$];
  rand int unsigned  data_page_id;

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
    instr_list.rand_mode(0);
  endfunction

  function void post_randomize();
    gen_amo_instr();
    // rs1 cannot be modified by other instructions
    if(!(rs1_reg inside {reserved_rd})) begin
      reserved_rd.push_back(rs1_reg);
    end
    add_mixed_instr();
    add_rs1_init_la_instr();
    super.post_randomize();
  endfunction

  // Use "la" instruction to initialize the base regiseter
  virtual function void add_rs1_init_la_instr();
    riscv_pseudo_instr la_instr;
    la_instr = riscv_pseudo_instr::type_id::create("la_instr");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(la_instr,
                                   pseudo_instr_name == LA;
                                   rd == rs1_reg;,
                                   "Cannot randomize la_instr")
    if(access_u_mode_mem) begin
      la_instr.imm_str = $sformatf("data_page_%0d+%0d", data_page_id, base);
    end else begin
      la_instr.imm_str = $sformatf("kernel_data_page_%0d+%0d", data_page_id, base);
    end
    instr_list.push_front(la_instr);
  endfunction

  // AMO instruction generation
  virtual function void gen_amo_instr();
  endfunction

  // Insert some other instructions to mix with load/store instruction
  virtual function void add_mixed_instr();
    riscv_rand_instr rand_instr;
    for(int i = 0; i < num_mixed_instr; i ++) begin
      rand_instr = riscv_rand_instr::type_id::create("rand_instr");
      rand_instr.cfg = cfg;
      rand_instr.reserved_rd = reserved_rd;
      `DV_CHECK_RANDOMIZE_WITH_FATAL(rand_instr,
        if(avail_regs.size() > 0) {
          rs1 inside {avail_regs};
          rd inside {avail_regs};
        }
        !(category inside {LOAD, STORE, BRANCH, JUMP});,
        "Cannot randomize instruction")
      insert_instr(rand_instr);
    end
  endfunction

endclass

// A pair of LR/SC instruction
class riscv_lr_sc_instr_stream extends riscv_amo_base_instr_stream;

  riscv_rand_instr lr_instr;
  riscv_rand_instr sc_instr;

  constraint legal_c {
    num_amo == 1;
    num_mixed_instr inside {[0:15]};
  }

  `uvm_object_utils(riscv_lr_sc_instr_stream)

  function new(string name = "");
    super.new(name);
    lr_instr = riscv_rand_instr::type_id::create("lr_instr");
    sc_instr = riscv_rand_instr::type_id::create("sc_instr");
  endfunction

  virtual function void gen_amo_instr();
    lr_instr.cfg = cfg;
    sc_instr.cfg = cfg;
    lr_instr.disable_a_extension_c.constraint_mode(0);
    sc_instr.disable_a_extension_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(lr_instr,
                                   rs1 == rs1_reg;
                                   rd != rs1_reg;
                                   instr_name inside {LR_W, LR_D};)
    `DV_CHECK_RANDOMIZE_WITH_FATAL(sc_instr,
                                   rs1 == rs1_reg;
                                   rd != rs1_reg;
                                   instr_name inside {SC_W, SC_D};)
    instr_list.push_front(lr_instr);
    instr_list.push_front(sc_instr);
  endfunction

endclass

class riscv_amo_instr_stream extends riscv_amo_base_instr_stream;

  riscv_rand_instr amo_instr[];

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
      amo_instr[i] = riscv_rand_instr::type_id::create($sformatf("amo_instr_%0d", i));
      amo_instr[i].cfg = cfg;
      amo_instr[i].disable_a_extension_c.constraint_mode(0);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(amo_instr[i],
                                     rs1 == rs1_reg;
                                     rd != rs1_reg;
                                     category == AMO;)
      instr_list.push_front(amo_instr[i]);
    end
  endfunction

endclass
