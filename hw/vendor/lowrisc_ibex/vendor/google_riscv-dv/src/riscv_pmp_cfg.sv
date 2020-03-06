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
  // pmp CSR configurations
  rand pmp_cfg_reg_t pmp_cfg[];
  // PMP maximum address - used to set defaults
  // TODO(udinator) - make this address configurable?
  bit [XLEN - 1 : 0] pmp_max_address = {XLEN{1'b1}};

  // used to parse addr_mode configuration from cmdline
  typedef uvm_enum_wrapper#(pmp_addr_mode_t) addr_mode_wrapper;
  pmp_addr_mode_t addr_mode;

  `uvm_object_utils_begin(riscv_pmp_cfg)
    `uvm_field_int(pmp_num_regions, UVM_DEFAULT)
    `uvm_field_int(pmp_granularity, UVM_DEFAULT)
  `uvm_object_utils_end

  // constraints
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

  function new(string name = "");
    string s;
    super.new(name);
    inst = uvm_cmdline_processor::get_inst();
    get_bool_arg_value("+pmp_randomize=", pmp_randomize);
    get_int_arg_value("+pmp_granularity=", pmp_granularity);
    get_int_arg_value("+pmp_num_regions=", pmp_num_regions);
    pmp_cfg = new[pmp_num_regions];
    // As per privileged spec, the top 10 bits of a rv64 PMP address are all 0.
    if (XLEN == 64) begin
      pmp_max_address[XLEN - 1 : XLEN - 11] = 10'b0;
    end
    if (!pmp_randomize) begin
      set_defaults();
      setup_pmp();
    end
  endfunction

  // This will only get called if pmp_randomize is set, in which case we apply command line
  // arguments after randomization
  function void post_randomize();
    setup_pmp();
  endfunction

  function void set_defaults();
    foreach(pmp_cfg[i]) begin
      pmp_cfg[i].l    = 1'b0;
      pmp_cfg[i].a    = TOR;
      pmp_cfg[i].x    = 1'b1;
      pmp_cfg[i].w    = 1'b1;
      pmp_cfg[i].r    = 1'b1;
      pmp_cfg[i].addr = assign_default_addr(pmp_num_regions, i + 1);
    end
  endfunction

  // Helper function to break down
  function bit [XLEN - 1 : 0] assign_default_addr(int num_regions, int index);
    return pmp_max_address / num_regions * index;
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

  function void parse_pmp_config(string pmp_region, output pmp_cfg_reg_t pmp_cfg_reg);
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
          pmp_cfg_reg.addr = format_addr(field_val.atohex());
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
  function void gen_pmp_instr(ref string instr[$], riscv_reg_t scratch_reg);
    int cfg_per_csr = XLEN / 4;
    bit [XLEN - 1 : 0] pmp_word;
    bit [XLEN - 1 : 0] cfg_bitmask;
    bit [7 : 0] cfg_byte;
    riscv_instr_pkg::privileged_reg_t base_pmp_addr = PMPADDR0;
    riscv_instr_pkg::privileged_reg_t base_pmpcfg_addr = PMPCFG0;
    int pmp_id;
    foreach (pmp_cfg[i]) begin
      // TODO(udinator) condense this calculations if possible
      pmp_id = i / cfg_per_csr;
      cfg_byte = {pmp_cfg[i].l, pmp_cfg[i].zero, pmp_cfg[i].a,
                  pmp_cfg[i].x, pmp_cfg[i].w, pmp_cfg[i].r};
      `uvm_info(`gfn, $sformatf("cfg_byte: 0x%0x", cfg_byte), UVM_DEBUG)
      cfg_bitmask = cfg_byte << ((i % cfg_per_csr) * 8);
      `uvm_info(`gfn, $sformatf("cfg_bitmask: 0x%0x", cfg_bitmask), UVM_DEBUG)
      pmp_word = pmp_word | cfg_bitmask;
      `uvm_info(`gfn, $sformatf("pmp_word: 0x%0x", pmp_word), UVM_DEBUG)
      cfg_bitmask = 0;
      `uvm_info(`gfn, $sformatf("pmp_addr: 0x%0x", pmp_cfg[i].addr), UVM_DEBUG)
      instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg, pmp_cfg[i].addr));
      instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + i, scratch_reg));
      // short circuit if end of list
      if (i == pmp_cfg.size() - 1) begin
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg, pmp_word));
        instr.push_back($sformatf("csrw 0x%0x, x%0d",
                                  base_pmpcfg_addr + pmp_id,
                                  scratch_reg));
        return;
      end else if ((i + 1) % cfg_per_csr == 0) begin
        // if we've filled up pmp_word, write to the corresponding CSR
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg, pmp_word));
        instr.push_back($sformatf("csrw 0x%0x, x%0d",
                                  base_pmpcfg_addr + pmp_id,
                                  scratch_reg));
        pmp_word = 0;
      end
    end
  endfunction

endclass
