/*
 * Copyright 2020 Google LLC
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

class riscv_pmp_cfg extends uvm_object;

  // default to a single PMP region
  rand int pmp_num_regions = 1;

  // default to granularity of 0 (4 bytes grain)
  int pmp_granularity = 0;

  // enable bit for pmp randomization
  bit pmp_randomize = 0;

  // allow pmp randomization to cause address range overlap
  bit pmp_allow_addr_overlap = 0;

  // pmp CSR configurations
  rand pmp_cfg_reg_t pmp_cfg[];

  // This value is the address offset between the minimum and maximum pmpaddr
  // CSR values.
  // As pmpaddr0 will be set to the address of the <main> label, the address stored
  // in pmpaddr0 added to this pmp_max_offset value will give the upper bound of the
  // address range covered by the PMP address range.
  // Can be manually configured from the command line.
  bit [XLEN - 1 : 0] pmp_max_offset = {XLEN{1'b1}};

  // used to parse addr_mode configuration from cmdline
  typedef uvm_enum_wrapper#(pmp_addr_mode_t) addr_mode_wrapper;
  pmp_addr_mode_t addr_mode;

  `uvm_object_utils_begin(riscv_pmp_cfg)
    `uvm_field_int(pmp_num_regions, UVM_DEFAULT)
    `uvm_field_int(pmp_granularity, UVM_DEFAULT)
    `uvm_field_int(pmp_max_offset, UVM_DEFAULT)
  `uvm_object_utils_end

  /////////////////////////////////////////////////
  // Constraints - apply when pmp_randomize is 1 //
  /////////////////////////////////////////////////

  constraint sanity_c {
    pmp_num_regions inside {[1 : 16]};
    pmp_granularity inside {[0 : XLEN + 3]};
  }

  // TODO(udinator) more address constraints?
  // TODO(udinator) move to posts_randomize() if lower performance
  constraint xwr_c {
    foreach (pmp_cfg[i]) {
      !(pmp_cfg[i].w && !pmp_cfg[i].r);
    }
  }

  constraint grain_addr_mode_c {
    foreach (pmp_cfg[i]) {
      (pmp_granularity >= 1) -> (pmp_cfg[i].a != NA4);
    }
  }

  constraint addr_range_c {
    foreach (pmp_cfg[i]) {
      // Offset of pmp_cfg[0] does not matter, since it will be set to <main>,
      // so we do not constrain it here, as it will be overridden during generation
      if (i != 0) {
        pmp_cfg[i].offset inside {[1 : pmp_max_offset + 1]};
      } else {
        pmp_cfg[i].offset == 0;
      }
    }
  }

  constraint addr_overlapping_c {
    foreach (pmp_cfg[i]) {
      if (!pmp_allow_addr_overlap && i > 0) {
        pmp_cfg[i].offset > pmp_cfg[i-1].offset;
      }
    }
  }

  function new(string name = "");
    string s;
    super.new(name);
    inst = uvm_cmdline_processor::get_inst();
    get_bool_arg_value("+pmp_randomize=", pmp_randomize);
    get_bool_arg_value("+pmp_allow_addr_overlap=", pmp_allow_addr_overlap);
    get_int_arg_value("+pmp_granularity=", pmp_granularity);
    get_int_arg_value("+pmp_num_regions=", pmp_num_regions);
    get_hex_arg_value("+pmp_max_offset=", pmp_max_offset);
    `uvm_info(`gfn, $sformatf("pmp max offset: 0x%0x", pmp_max_offset), UVM_LOW)
    pmp_cfg = new[pmp_num_regions];
  endfunction

  function void initialize(bit require_signature_addr);
    if (!pmp_randomize) begin
      set_defaults();
      setup_pmp();
    end
  endfunction

  // This will only get called if pmp_randomize is set, in which case we apply command line
  // arguments after randomization
  function void post_randomize();
`ifdef _VCP //GRK958
    foreach(pmp_cfg[i]) pmp_cfg[i].zero = 2'b00;
`endif  
    setup_pmp();
  endfunction

  function void set_defaults();
    `uvm_info(`gfn, $sformatf("MAX OFFSET: 0x%0x", pmp_max_offset), UVM_LOW)
    foreach(pmp_cfg[i]) begin
      pmp_cfg[i].l      = 1'b0;
      pmp_cfg[i].a      = TOR;
      pmp_cfg[i].x      = 1'b1;
      pmp_cfg[i].w      = 1'b1;
      pmp_cfg[i].r      = 1'b1;
      pmp_cfg[i].offset = assign_default_addr_offset(pmp_num_regions, i);
    end
  endfunction

  function bit [XLEN - 1 : 0] assign_default_addr_offset(int num_regions, int index);
    bit [XLEN - 1 : 0] offset;
    offset = pmp_max_offset / (num_regions - 1);
    offset = offset * index;
    return offset;
  endfunction

  function void setup_pmp();
    string arg_name;
    string pmp_region;
    foreach (pmp_cfg[i]) begin
      arg_name = $sformatf("+pmp_region_%0d=", i);
      if (inst.get_arg_value(arg_name, pmp_region)) begin
        parse_pmp_config(pmp_region, pmp_cfg[i]);
        `uvm_info(`gfn, $sformatf("Configured pmp_cfg[%0d] from command line: %p",
                                  i, pmp_cfg[i]), UVM_LOW)
      end
    end
  endfunction

  function void parse_pmp_config(string pmp_region, ref pmp_cfg_reg_t pmp_cfg_reg);
    string fields[$];
    string field_vals[$];
    string field_type;
    string field_val;
    uvm_split_string(pmp_region, ",", fields);
    foreach (fields[i]) begin
      uvm_split_string(fields[i], ":", field_vals);
      field_type = field_vals.pop_front();
      field_val = field_vals.pop_front();
      case (field_type)
        "L": begin
          pmp_cfg_reg.l = field_val.atobin();
        end
        "A": begin
          `DV_CHECK(addr_mode_wrapper::from_name(field_val, addr_mode))
          pmp_cfg_reg.a = addr_mode;
        end
        "X": begin
          pmp_cfg_reg.x = field_val.atobin();
        end
        "W": begin
          pmp_cfg_reg.w = field_val.atobin();
        end
        "R": begin
          pmp_cfg_reg.r = field_val.atobin();
        end
        "ADDR": begin
          // Don't have to convert address to "PMP format" here,
          // since it must be masked off in hardware
          pmp_cfg_reg.offset = format_addr(field_val.atohex());
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("%s, Invalid PMP configuration field name!", field_val))
        end
      endcase
    end
  endfunction

  function bit [XLEN - 1 : 0] format_addr(bit [XLEN - 1 : 0] addr);
    // For all ISAs, pmpaddr CSRs do not include the bottom two bits of the input address
    bit [XLEN - 1 : 0] shifted_addr;
    shifted_addr = addr >> 2; case (XLEN)
      // RV32 - pmpaddr is bits [33:2] of the whole 34 bit address
      // Return the input address right-shifted by 2 bits
      32: begin
        return shifted_addr;
      end
      // RV64 - pmpaddr is bits [55:2] of the whole 56 bit address, prepended by 10'b0
      // Return {10'b0, shifted_addr[53:0]}
      64: begin
        return {10'b0, shifted_addr[XLEN - 11 : 0]};
      end
      default: `uvm_fatal(`gfn, $sformatf("Unsupported XLEN %0s", XLEN))
    endcase
  endfunction

  // TODO(udinator) - implement function to return hardware masked pmpaddr "representation"
  function bit [XLEN - 1 : 0] convert_addr2pmp(bit [XLEN - 1 : 0] addr);
    `uvm_info(`gfn, "Placeholder function, need to implement", UVM_LOW)
  endfunction

  // This function parses the pmp_cfg[] array to generate the actual instructions to set up
  // the PMP CSR registers.
  // Since either 4 (in rv32) or 8 (in rv64) PMP configuration registers fit into one physical
  // CSR, this function waits until it has reached this maximum to write to the physical CSR to
  // save some extraneous instructions from being performed.
  function void gen_pmp_instr(riscv_reg_t scratch_reg[2], ref string instr[$]);
    int cfg_per_csr = XLEN / 8;
    bit [XLEN - 1 : 0] pmp_word;
    bit [XLEN - 1 : 0] cfg_bitmask;
    bit [7 : 0] cfg_byte;
    riscv_instr_pkg::privileged_reg_t base_pmp_addr = PMPADDR0;
    riscv_instr_pkg::privileged_reg_t base_pmpcfg_addr = PMPCFG0;
    int pmp_id;
    foreach (pmp_cfg[i]) begin
      // TODO(udinator) condense this calculations if possible
      pmp_id = i / cfg_per_csr;
      if (i == 0) begin
        cfg_byte = {1'b0, pmp_cfg[i].zero, TOR, 1'b1, 1'b1, 1'b1};
      end else begin
        cfg_byte = {pmp_cfg[i].l, pmp_cfg[i].zero, pmp_cfg[i].a,
                    pmp_cfg[i].x, pmp_cfg[i].w, pmp_cfg[i].r};
      end
      `uvm_info(`gfn, $sformatf("cfg_byte: 0x%0x", cfg_byte), UVM_DEBUG)
      // First write to the appropriate pmpaddr CSR
      cfg_bitmask = cfg_byte << ((i % cfg_per_csr) * 8);
      `uvm_info(`gfn, $sformatf("cfg_bitmask: 0x%0x", cfg_bitmask), UVM_DEBUG)
      pmp_word = pmp_word | cfg_bitmask;
      `uvm_info(`gfn, $sformatf("pmp_word: 0x%0x", pmp_word), UVM_DEBUG)
      cfg_bitmask = 0;
      if (i == 0) begin
        // load the address of the <main> section into pmpaddr0
        instr.push_back($sformatf("la x%0d, main", scratch_reg[0]));
        instr.push_back($sformatf("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]));
        instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + i, scratch_reg[0]));
        `uvm_info(`gfn, "Loaded the address of <main> section into pmpaddr0", UVM_LOW)
      end else begin
        // Add the offset to the base address to get the other pmpaddr values
        instr.push_back($sformatf("la x%0d, main", scratch_reg[0]));
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[1], pmp_cfg[i].offset));
        instr.push_back($sformatf("add x%0d, x%0d, x%0d",
                                  scratch_reg[0], scratch_reg[0], scratch_reg[1]));
        instr.push_back($sformatf("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]));
        instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + i, scratch_reg[0]));
        `uvm_info(`gfn, $sformatf("Offset of pmp_addr_%d from pmpaddr0: 0x%0x",
                                  i, pmp_cfg[i].offset), UVM_LOW)
      end
      // Now, check if we have to write to the appropriate pmpcfg CSR.
        // Short circuit if we reach the end of the list
      if (i == pmp_cfg.size() - 1) begin
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], pmp_word));
        instr.push_back($sformatf("csrw 0x%0x, x%0d",
                                  base_pmpcfg_addr + pmp_id,
                                  scratch_reg[0]));
        return;
      end else if ((i + 1) % cfg_per_csr == 0) begin
        // if we've filled up pmp_word, write to the corresponding CSR
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], pmp_word));
        instr.push_back($sformatf("csrw 0x%0x, x%0d",
                                  base_pmpcfg_addr + pmp_id,
                                  scratch_reg[0]));
        pmp_word = 0;
      end
    end
  endfunction

endclass
