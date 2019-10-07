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

// Base class for all load/store instruction stream

class riscv_load_store_base_instr_stream extends riscv_mem_access_stream;

  typedef enum bit [1:0] {
    NARROW,
    HIGH,
    MEDIUM,
    SPARSE
  } locality_e;

  rand int unsigned  num_load_store;
  rand int unsigned  num_mixed_instr;
  rand int           base;
  int                offset[];
  int                addr[];
  rand int unsigned  data_page_id;
  rand riscv_reg_t   rs1_reg;
  rand locality_e    locality;
  rand int           max_load_store_offset;

  `uvm_object_utils(riscv_load_store_base_instr_stream)

  constraint rs1_c {
    !(rs1_reg inside {cfg.reserved_regs, reserved_rd, ZERO});
  }

  constraint addr_c {
    solve data_page_id before max_load_store_offset;
    solve max_load_store_offset before base;
    data_page_id < max_data_page_id;
    foreach (data_page[i]) {
      if (i == data_page_id) {
        max_load_store_offset == data_page[i].size_in_bytes;
      }
    }
    base inside {[0 : max_load_store_offset-1]};
  }

  function new(string name = "");
    super.new(name);
  endfunction

  virtual function void randomize_offset();
    int offset_, addr_;
    offset = new[num_load_store];
    addr = new[num_load_store];
    for (int i=0; i<num_load_store; i++) begin
      if (!std::randomize(offset_, addr_) with {
        // Locality
        if (locality == NARROW) {
          soft offset_ inside {[-16:16]};
        } else if (locality == HIGH) {
          soft offset_ inside {[-64:64]};
        } else if (locality == MEDIUM) {
          soft offset_ inside {[-256:256]};
        } else if (locality == SPARSE) {
          soft offset_ inside {[-2048:2047]};
        }
        addr_ == base + offset_;
        addr_ inside {[0 : max_load_store_offset - 1]};
      }) begin
        `uvm_fatal(`gfn, "Cannot randomize load/store offset")
      end
      offset[i] = offset_;
      addr[i] = addr_;
    end
  endfunction

  function void post_randomize();
    randomize_offset();
    // rs1 cannot be modified by other instructions
    if(!(rs1_reg inside {reserved_rd})) begin
      reserved_rd = {reserved_rd, rs1_reg};
    end
    gen_load_store_instr();
    add_mixed_instr(num_mixed_instr);
    add_rs1_init_la_instr(rs1_reg, data_page_id, base);
    super.post_randomize();
  endfunction

  // Generate each load/store instruction
  virtual function void gen_load_store_instr();
    bit enable_compressed_load_store;
    riscv_instr_base instr;
    if(avail_regs.size() > 0) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(avail_regs,
                                         unique{avail_regs};
                                         avail_regs[0] inside {[S0 : A5]};
                                         foreach(avail_regs[i]) {
                                           !(avail_regs[i] inside {cfg.reserved_regs, reserved_rd});
                                         },
                                         "Cannot randomize avail_regs")
    end
    if (rs1_reg inside {[S0 : A5]}) begin
      enable_compressed_load_store = 1;
    end
    foreach(addr[i]) begin
      instr = riscv_instr_base::type_id::create("instr");
      // Assign the allowed load/store instructions based on address alignment
      // This is done separately rather than a constraint to improve the randomization performance
      allowed_instr = {LB, LBU, SB};
      if (addr[i][0] == 1'b0) begin
        allowed_instr = {LH, LHU, SH, allowed_instr};
      end
      if (!cfg.enable_unaligned_load_store) begin
        if (addr[i] % 4 == 0) begin
          allowed_instr = {LW, SW, allowed_instr};
          if((offset[i] inside {[0:127]}) && (offset[i] % 4 == 0) &&
             (RV32C inside {riscv_instr_pkg::supported_isa}) &&
             enable_compressed_load_store) begin
            allowed_instr = {C_LW, C_SW, allowed_instr};
          end
        end
        if ((XLEN >= 64) && (addr[i] % 8 == 0)) begin
          allowed_instr = {LWU, LD, SD, allowed_instr};
          if((offset[i] inside {[0:255]}) && (offset[i] % 8 == 0) &&
             (RV64C inside {riscv_instr_pkg::supported_isa} &&
             enable_compressed_load_store)) begin
            allowed_instr = {C_LD, C_SD, allowed_instr};
          end
        end
      end else begin
        allowed_instr = {LW, SW, allowed_instr};
        if ((offset[i] inside {[0:127]}) && (offset[i] % 4 == 0) &&
            (RV32C inside {riscv_instr_pkg::supported_isa}) &&
            enable_compressed_load_store) begin
          allowed_instr = {C_LW, C_SW, allowed_instr};
        end
        if (XLEN >= 64) begin
          allowed_instr = {LWU, LD, SD, allowed_instr};
          if ((offset[i] inside {[0:255]}) && (offset[i] % 8 == 0) &&
              (RV64C inside {riscv_instr_pkg::supported_isa}) &&
              enable_compressed_load_store) begin
              allowed_instr = {C_LD, C_SD, allowed_instr};
           end
        end
      end
      randomize_instr(instr, .skip_rs1(1'b1), .skip_imm(1'b1));
      instr.rs1 = rs1_reg;
      instr.set_imm(offset[i]);
      instr.process_load_store = 0;
      instr_list.push_back(instr);
    end
  endfunction

endclass

// A single load/store instruction
class riscv_single_load_store_instr_stream extends riscv_load_store_base_instr_stream;

  constraint legal_c {
    num_load_store == 1;
    num_mixed_instr < 5;
  }

  `uvm_object_utils(riscv_load_store_base_instr_stream)
  `uvm_object_new

endclass

// Back to back load/store instructions
class riscv_load_store_stress_instr_stream extends riscv_load_store_base_instr_stream;

  int unsigned max_instr_cnt = 30;
  int unsigned min_instr_cnt = 10;

  constraint legal_c {
    num_load_store inside {[min_instr_cnt:max_instr_cnt]};
    num_mixed_instr == 0;
  }

  `uvm_object_utils(riscv_load_store_stress_instr_stream)
  `uvm_object_new

endclass

// Random load/store sequence
// A random mix of load/store instructions and other instructions
class riscv_load_store_rand_instr_stream extends riscv_load_store_base_instr_stream;

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  `uvm_object_utils(riscv_load_store_rand_instr_stream)
  `uvm_object_new

endclass

// Use a small set of GPR to create various WAW, RAW, WAR hazard scenario
class riscv_hazard_instr_stream extends riscv_load_store_base_instr_stream;

  int unsigned num_of_avail_regs = 6;

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  `uvm_object_utils(riscv_hazard_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    avail_regs = new[num_of_avail_regs];
    super.pre_randomize();
  endfunction

endclass

// Use a small set of address to create various load/store hazard sequence
// This instruction stream focus more on hazard handling of load store unit.
class riscv_load_store_hazard_instr_stream extends riscv_load_store_base_instr_stream;

  rand int avail_addr[];

  constraint legal_c {
    num_load_store inside {[10:30]};
    num_mixed_instr inside {[10:30]};
  }

  constraint avail_addr_c {
    avail_addr.size() inside {[1:3]};
    foreach(avail_addr[i]) {
      avail_addr[i] inside {[0 : max_load_store_offset - 1]};
    }
  }

  `uvm_object_utils(riscv_load_store_hazard_instr_stream)
  `uvm_object_new

  // Randomize each address in the post_randomize to reduce the complexity of solving everything
  // in one shot.
  function void post_randomize();
    int temp_addr;
    foreach(addr[i]) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(temp_addr,
                                         temp_addr inside {avail_addr};,
                                         "Cannot randomize address")
      addr[i] = temp_addr;
    end
  endfunction
endclass

// Back to back access to multiple data pages
// This is useful to test data TLB switch and replacement
class riscv_multi_page_load_store_instr_stream extends riscv_mem_access_stream;

  riscv_load_store_stress_instr_stream load_store_instr_stream[];
  rand int unsigned num_of_instr_stream;
  rand int unsigned data_page_id[];
  rand riscv_reg_t  rs1_reg[];

  constraint default_c {
    foreach(data_page_id[i]) {
      data_page_id[i] < max_data_page_id;
    }
    data_page_id.size() == num_of_instr_stream;
    rs1_reg.size() == num_of_instr_stream;
    unique {rs1_reg};
    foreach(rs1_reg[i]) {
      !(rs1_reg[i] inside {cfg.reserved_regs, ZERO});
    }
  }

  constraint page_c {
    solve num_of_instr_stream before data_page_id;
    num_of_instr_stream inside {[1 : max_data_page_id]};
    unique {data_page_id};
  }

  // Avoid accessing a large number of pages because we may run out of registers for rs1
  // Each page access needs a reserved register as the base address of load/store instruction
  constraint reasonable_c {
    num_of_instr_stream inside {[2:8]};
  }

  `uvm_object_utils(riscv_multi_page_load_store_instr_stream)
  `uvm_object_new

  // Generate each load/store seq, and mix them together
  function void post_randomize();
    load_store_instr_stream = new[num_of_instr_stream];
    foreach(load_store_instr_stream[i]) begin
      load_store_instr_stream[i] = riscv_load_store_stress_instr_stream::type_id::
                                   create($sformatf("load_store_instr_stream_%0d", i));
      load_store_instr_stream[i].min_instr_cnt = 5;
      load_store_instr_stream[i].max_instr_cnt = 10;
      load_store_instr_stream[i].cfg = cfg;
      // Make sure each load/store sequence doesn't override the rs1 of other sequences.
      foreach(rs1_reg[j]) begin
        if(i != j) begin
          load_store_instr_stream[i].reserved_rd =
            {load_store_instr_stream[i].reserved_rd, rs1_reg[j]};
        end
      end
      `DV_CHECK_RANDOMIZE_WITH_FATAL(load_store_instr_stream[i],
                                     rs1_reg == local::rs1_reg[i];
                                     data_page_id == local::data_page_id[i];,
                                     "Cannot randomize load/store instruction")
      // Mix the instruction stream of different page access, this could trigger the scenario of
      // frequent data TLB switch
      if(i == 0) begin
        instr_list = load_store_instr_stream[i].instr_list;
      end else begin
        mix_instr_stream(load_store_instr_stream[i].instr_list);
      end
    end
  endfunction

endclass

// Access the different locations of the same memory regions
class riscv_mem_region_stress_test extends riscv_multi_page_load_store_instr_stream;

  `uvm_object_utils(riscv_mem_region_stress_test)
  `uvm_object_new

  constraint page_c {
    num_of_instr_stream inside {[2:5]};
    foreach (data_page_id[i]) {
      if (i > 0) {
        data_page_id[i] == data_page_id[i-1];
      }
    }
  }

endclass
