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

  // number of configuration bytes per pmpcfg CSR
  int cfg_per_csr;

  // enable bit for pmp randomization
  bit pmp_randomize = 0;

  // allow pmp randomization to cause address range overlap
  bit pmp_allow_illegal_tor = 0;

  // By default, after returning from a PMP exception, we return to the exact same instruction that
  // resulted in a PMP exception to begin with, creating an infinite loop of taking an exception.
  // To avoid this situation, this configuration knob will enable the relevant PMP exception
  // handlers to find the pmpcfg CSR that controls the address region resulting in the exception and
  // change the relevant access bit to 1'b1, allowing forward progress in the code, while also
  // allowing all access restrictions to be enforced.
  bit enable_pmp_exception_handler = 1'b1;

  // Don't generate the usual PMP setup section, instead generate a setup that provides a single
  // region allowing full access to all of memory from both U mode and M mode.
  bit suppress_pmp_setup = 0;

  // Setting this bit to 1'b1 enables generation of the directed stream of instructions to test
  // write accesses to all supported pmpaddr[i] CSRs.
  bit enable_write_pmp_csr;

  // ePMP machine security configuration - RLB, MMWP, MML
  rand mseccfg_reg_t mseccfg = '{1'b1, 1'b0, 1'b0};

  // allow regions that start above 32-bit address space when XLEN == 32
  rand bit allow_high_addrs;

  // percentage of configs that will allow high address regions. Set low by default as for cores
  // where physical addresses do not go beyond 32 bits high regions don't do anything interesting
  // (though you want some to ensure they're handled correctly).
  int high_addr_proportion = 10;

  // pmp CSR configurations
  rand pmp_cfg_reg_t pmp_cfg[];

  // Hints used during PMP generation
  bit pmp_cfg_addr_valid[];
  bit pmp_cfg_already_configured[];

  // This value is the address offset between the minimum and maximum pmpaddr
  // CSR values.
  // As pmpaddr0 will be set to the address of the <main> label, the address stored
  // in pmpaddr0 added to this pmp_max_offset value will give the upper bound of the
  // address range covered by the PMP address range.
  // Can be manually configured from the command line.
  bit [XLEN - 1 : 0] pmp_max_offset = {XLEN{1'b1}};

  // Value to hold the end signature address to that signals the end to the test environment.
  // Currently the design assumes that the end signature is address is equal to the signature
  // address minus 4 Bytes.
  bit [XLEN - 1 : 0] end_signature_addr;

  // used to parse addr_mode configuration from cmdline
  typedef uvm_enum_wrapper#(pmp_addr_mode_t) addr_mode_wrapper;
  pmp_addr_mode_t addr_mode;

  // Store the base addresses of pmpaddr0 and pmpcfg0
  riscv_instr_pkg::privileged_reg_t base_pmp_addr = PMPADDR0;
  riscv_instr_pkg::privileged_reg_t base_pmpcfg_addr = PMPCFG0;

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

  constraint xwr_c {
    foreach (pmp_cfg[i]) {
      solve mseccfg.mml before pmp_cfg[i].w, pmp_cfg[i].r;
      !(!mseccfg.mml && pmp_cfg[i].w && !pmp_cfg[i].r);
    }
  }

  constraint allow_high_addrs_c {
    allow_high_addrs dist { 0 := 100 - high_addr_proportion,
                            1 := high_addr_proportion };
    if (XLEN == 64) {
      allow_high_addrs == 1'b1;
    }
  }

  constraint address_modes_c {
    foreach (pmp_cfg[i]) {
      pmp_cfg[i].addr_mode >= 0;
      if (allow_high_addrs) {
        pmp_cfg[i].addr_mode <= XLEN;
      } else {
        pmp_cfg[i].addr_mode <= XLEN - 3;
      }
    }
  }

  constraint grain_addr_mode_c {
    foreach (pmp_cfg[i]) {
      (pmp_granularity >= 1) -> (pmp_cfg[i].a != NA4);
    }
  }

  constraint addr_range_c {
    foreach (pmp_cfg[i]) {
      // Offset of pmp_cfg[0] is always set to 0 from main.
      if (i != 0) {
        pmp_cfg[i].offset inside {[1 : pmp_max_offset]};
      } else {
        pmp_cfg[i].offset == 0;
      }
    }
  }

  constraint modes_before_addr_c {
    foreach (pmp_cfg[i]) {
      solve allow_high_addrs before pmp_cfg[i].addr, pmp_cfg[i].addr_mode;
      solve pmp_cfg[i].a before pmp_cfg[i].addr;
      solve pmp_cfg[i].addr_mode before pmp_cfg[i].addr;
    }
  }

  constraint addr_legal_tor_c {
    foreach (pmp_cfg[i]) {
      // In case illegal TOR regions are disallowed always add the constraint, otherwise make the
      // remove the constraint for 1 in every XLEN entries.
      if (i > 0 && pmp_cfg[i].a == TOR && (!pmp_allow_illegal_tor || pmp_cfg[i].addr_mode > 0)) {
        pmp_cfg[i].addr > pmp_cfg[i-1].addr;
      }

      if (!allow_high_addrs) {
        pmp_cfg[i].addr[31:29] == '0;
      }
    }
  }

  constraint addr_napot_mode_c {
    foreach (pmp_cfg[i]) {
      // In case NAPOT is selected make sure that we randomly select a region mode and force the
      // address to match that mode.
      if (pmp_cfg[i].a == NAPOT) {
        // Make sure the bottom addr_mode - 1 bits are set to 1.
        (pmp_cfg[i].addr & ((1 << pmp_cfg[i].addr_mode) - 1)) == ((1 << pmp_cfg[i].addr_mode) - 1);
        if (pmp_cfg[i].addr_mode < XLEN) {
          // Unless the largest region is selected make sure the bit just before the ones is set to 0.
          (pmp_cfg[i].addr & (1 << pmp_cfg[i].addr_mode)) == 0;
        }

        if (!allow_high_addrs) {
          pmp_cfg[i].addr[31:29] == '0;
        }
      }
    }
  }

  constraint addr_na4_mode_c {
    foreach (pmp_cfg[i]) {
      if (pmp_cfg[i].a == NA4) {
        if (!allow_high_addrs) {
          pmp_cfg[i].addr[31:29] == '0;
        }
      }
    }
  }

  function new(string name = "");
    string s;
    super.new(name);
    cfg_per_csr = XLEN / 8;
    inst = uvm_cmdline_processor::get_inst();
    if (inst.get_arg_value("+pmp_num_regions=", s)) begin
      pmp_num_regions = s.atoi();
      pmp_num_regions.rand_mode(0);
    end
    get_int_arg_value("+pmp_granularity=", pmp_granularity);
    get_bool_arg_value("+pmp_randomize=", pmp_randomize);
    get_bool_arg_value("+pmp_allow_illegal_tor=", pmp_allow_illegal_tor);
    get_bool_arg_value("+suppress_pmp_setup=", suppress_pmp_setup);
    get_bool_arg_value("+enable_write_pmp_csr=", enable_write_pmp_csr);
    get_hex_arg_value("+pmp_max_offset=", pmp_max_offset);
    `uvm_info(`gfn, $sformatf("pmp max offset: 0x%08x", pmp_max_offset), UVM_LOW)
    pmp_cfg = new[pmp_num_regions];
    pmp_cfg_addr_valid = new[pmp_num_regions];
    pmp_cfg_already_configured = new[pmp_num_regions];
  endfunction

  function void initialize(bit [XLEN - 1 : 0] signature_addr);
    end_signature_addr = signature_addr - 'h4;
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
    `uvm_info(`gfn, $sformatf("MAX OFFSET: 0x%08x", pmp_max_offset), UVM_LOW)
    mseccfg.mml  = 1'b0;
    mseccfg.mmwp = 1'b0;
    mseccfg.rlb  = 1'b1;
    foreach(pmp_cfg[i]) begin
      pmp_cfg[i].l                  = 1'b0;
      pmp_cfg[i].a                  = TOR;
      pmp_cfg[i].x                  = 1'b1;
      pmp_cfg[i].w                  = 1'b1;
      pmp_cfg[i].r                  = 1'b1;
      pmp_cfg[i].offset             = assign_default_addr_offset(pmp_num_regions, i);
      pmp_cfg_addr_valid[i]         = 1'b0;
      pmp_cfg_already_configured[i] = 1'b0;
    end
  endfunction

  function bit [XLEN - 1 : 0] assign_default_addr_offset(int num_regions, int index);
    bit [XLEN - 1 : 0] offset;
    offset = pmp_max_offset / (num_regions - 1);
    offset = offset * index;
    return offset;
  endfunction

  typedef struct { pmp_cfg_reg_t pmp_cfg_reg; bit addr_valid; } parse_pmp_config_t;

  function void setup_pmp();
    string arg_name;
    string arg_value;
    parse_pmp_config_t tmp_value;
    if (inst.get_arg_value("+mseccfg=", arg_value)) begin
      mseccfg = parse_mseccfg(arg_value, mseccfg);
    end
    foreach (pmp_cfg[i]) begin
      arg_name = $sformatf("+pmp_region_%0d=", i);
      if (inst.get_arg_value(arg_name, arg_value)) begin
        tmp_value = parse_pmp_config(arg_value, pmp_cfg[i]);
        pmp_cfg[i] = tmp_value.pmp_cfg_reg;
        pmp_cfg_addr_valid[i] = tmp_value.addr_valid;
        `uvm_info(`gfn, $sformatf("Configured pmp_cfg[%0d] from command line: %p",
                                  i, pmp_cfg[i]), UVM_LOW)
      end
    end
  endfunction

  function mseccfg_reg_t parse_mseccfg(string mseccfg, mseccfg_reg_t ref_mseccfg);
    string fields[$];
    string field_vals[$];
    string field_type;
    string field_val;
    mseccfg_reg_t mseccfg_reg = ref_mseccfg;
    uvm_split_string(mseccfg, ",", fields);
    foreach (fields[i]) begin
      uvm_split_string(fields[i], ":", field_vals);
      field_type = field_vals.pop_front();
      field_val = field_vals.pop_front();
      case (field_type)
        "MML": begin
          mseccfg_reg.mml = field_val.atobin();
        end
        "MMWP": begin
          mseccfg_reg.mmwp = field_val.atobin();
        end
        "RLB": begin
          mseccfg_reg.rlb = field_val.atobin();
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("%s, Invalid MSECCFG field name!", field_val))
        end
      endcase
    end
    return mseccfg_reg;
  endfunction

  function parse_pmp_config_t parse_pmp_config(string pmp_region, pmp_cfg_reg_t ref_pmp_cfg);
    string fields[$];
    string field_vals[$];
    string field_type;
    string field_val;
    parse_pmp_config_t return_value;
    return_value.pmp_cfg_reg = ref_pmp_cfg;
    return_value.addr_valid = 1'b0;
    uvm_split_string(pmp_region, ",", fields);
    foreach (fields[i]) begin
      uvm_split_string(fields[i], ":", field_vals);
      field_type = field_vals.pop_front();
      field_val = field_vals.pop_front();
      case (field_type)
        "L": begin
          return_value.pmp_cfg_reg.l = field_val.atobin();
        end
        "A": begin
          `DV_CHECK(addr_mode_wrapper::from_name(field_val, addr_mode))
          return_value.pmp_cfg_reg.a = addr_mode;
        end
        "X": begin
          return_value.pmp_cfg_reg.x = field_val.atobin();
        end
        "W": begin
          return_value.pmp_cfg_reg.w = field_val.atobin();
        end
        "R": begin
          return_value.pmp_cfg_reg.r = field_val.atobin();
        end
        "ADDR": begin
          // Don't have to convert address to "PMP format" here,
          // since it must be masked off in hardware
          return_value.addr_valid = 1'b1;
          return_value.pmp_cfg_reg.addr = format_addr(field_val.atohex());
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("%s, Invalid PMP configuration field name!", field_val))
        end
      endcase
    end
    return return_value;
  endfunction

  function bit [XLEN - 1 : 0] format_addr(bit [XLEN - 1 : 0] addr);
    // For all ISAs, pmpaddr CSRs do not include the bottom two bits of the input address
    bit [XLEN - 1 : 0] shifted_addr;
    shifted_addr = addr >> 2;
    case (XLEN)
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

  // Generates code to setup a single PMP region allowing full access to all memory
  function void gen_pmp_enable_all(riscv_reg_t scratch_reg, ref string instr[$]);
    // Setup region 0 to NAPOT covering the whole 32-bit address space, with RWX permissions and no
    // lock.
    instr.push_back($sformatf("li x%0d, 0x1fffffff", scratch_reg));
    instr.push_back($sformatf("csrw 0x%0x, x%0d", PMPADDR0, scratch_reg));
    instr.push_back($sformatf("csrw 0x%0x, 0x1f", PMPCFG0));
  endfunction

  // This function parses the pmp_cfg[] array to generate the actual instructions to set up
  // the PMP CSR registers.
  // Since either 4 (in rv32) or 8 (in rv64) PMP configuration registers fit into one physical
  // CSR, this function waits until it has reached this maximum to write to the physical CSR to
  // save some extraneous instructions from being performed.
  //
  // The general flow of this function:
  // - If randomization, generate code region, otherwise select region 0.
  // - Set address of code region before setting MSECCFG.
  // - If  MML, initially set MSECCFG to MML=0, MMWP=0, RLB=1.
  // - If  MML, set the config of code region to LXWR=1100 and TOR.
  // - If MMWP, set the config of code region to LXWR=0100 and TOR.
  // - If MML or MMWP, set requested MSECCFG with RLB hardcoded to 1.
  // - Don't override code region config if corresponding `+pmp_region_` is passed.
  // - If MML, set default code region config to shared execute.
  // - If MML or MMWP, set stack and signature regions to shared read/write.
  // - Set requested MSECCFG (including RLB).
  // - Set all other addresses and configs.
  function void gen_pmp_instr(riscv_reg_t scratch_reg[2], ref string instr[$]);
    bit [XLEN - 1 : 0] pmp_word;
    bit [XLEN - 1 : 0] cfg_bitmask;
    bit [7 : 0] cfg_byte;
    int pmp_id;
    string arg_value;
    int code_entry, stack_entry, sig_entry;
    pmp_cfg_reg_t tmp_pmp_cfg;

    if (riscv_instr_pkg::support_epmp) begin
      // In case of MML or MMWP we need to set code region to executable before setting MSECCFG.
      if (mseccfg.mml || mseccfg.mmwp) begin
        // Writing MSECCFG with RLB set to 1 to stop the config with L enabled from locking
        // everything before configuration is done.
        `uvm_info(`gfn, $sformatf("MSECCFG: MML 0, MMWP 0, RLB 1"), UVM_LOW)
        cfg_byte = {1'b1, 1'b0, 1'b0};
        instr.push_back($sformatf("csrwi 0x%0x, %0d", MSECCFG, cfg_byte));

        if (pmp_randomize) begin
          // Randomly select a PMP region to contain the code for permitting execution and two
          // extra regions to contain the stack and the signature address.
          code_entry = $urandom_range(pmp_num_regions - 3);
          // In case of full randomization we actually want the code region to cover main as well.
          pmp_cfg[code_entry].offset = pmp_max_offset;
          stack_entry = code_entry + 1;
          sig_entry = code_entry + 2;
        end else begin
          code_entry = 0;
          stack_entry = pmp_num_regions - 2;
          sig_entry = pmp_num_regions - 1;
          // This is the default offset.
          pmp_cfg[code_entry].offset = assign_default_addr_offset(pmp_num_regions, code_entry);
          pmp_cfg[pmp_num_regions - 3].offset = pmp_max_offset;
        end

        if (code_entry > 0) begin
          // Load _start into PMP address of previous entry to complete TOR region.
          instr.push_back($sformatf("la x%0d, _start", scratch_reg[0]));
          instr.push_back($sformatf("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]));
          instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + code_entry - 1,
                                    scratch_reg[0]));
          `uvm_info(`gfn, $sformatf("Address of pmp_addr_%d is _start", code_entry - 1), UVM_LOW)
          pmp_cfg_already_configured[code_entry - 1] = 1'b1;
        end
        // Load the address of the kernel_instr_end into PMP code entry.
        instr.push_back($sformatf("la x%0d, kernel_instr_end", scratch_reg[0]));
        instr.push_back($sformatf("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]));
        instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + code_entry, scratch_reg[0]));
        `uvm_info(`gfn, $sformatf("Address of pmp_addr_%d is kernel_instr_end", code_entry),
                  UVM_LOW)
        pmp_cfg_already_configured[code_entry] = 1'b1;

        if (mseccfg.mml) begin
          // This value is different from below (M-mode execute only) because we need code region
          // to be executable in both M-mode and U-mode, since RISCV-DV switches priviledge before
          // <main> but after <pmp_setup>. We choose to allow M-mode reads to allows checking
          // whether instructions are compressed in the trap handler in order to recover from load
          // and store access faults.
          tmp_pmp_cfg.l = 1'b1;
          tmp_pmp_cfg.a = TOR;
          tmp_pmp_cfg.x = 1'b1;
          tmp_pmp_cfg.w = 1'b1;
          tmp_pmp_cfg.r = 1'b0;
          // This configuration needs to be executable in M-mode both before and after writing to
          // MSECCFG. It will deny execution for U-Mode, but this is necessary because RWX=111 in
          // MML means read only, and RW=01 is not allowed before MML is enabled.
          cfg_byte = {tmp_pmp_cfg.l, tmp_pmp_cfg.zero, tmp_pmp_cfg.a, tmp_pmp_cfg.x,
                      1'b0, tmp_pmp_cfg.r};
        end else begin
          // We must set pmp code region to executable before enabling MMWP.
          tmp_pmp_cfg.l = 1'b0;
          tmp_pmp_cfg.a = TOR;
          tmp_pmp_cfg.x = 1'b1;
          tmp_pmp_cfg.w = 1'b0;
          tmp_pmp_cfg.r = 1'b0;
          cfg_byte      = {tmp_pmp_cfg.l, tmp_pmp_cfg.zero, tmp_pmp_cfg.a,
                           tmp_pmp_cfg.x, tmp_pmp_cfg.w,    tmp_pmp_cfg.r};
        end
        // In case the randomly selected code entry is not also configured in the arguments,
        // overwrite it in pmp_cfg.
        // The pmp_config has value LXWR = 1010, which means it is executable in both M and U mode.
        if (!inst.get_arg_value($sformatf("+pmp_region_%0d=", code_entry), arg_value)) begin
          pmp_cfg[code_entry].l      = tmp_pmp_cfg.l;
          pmp_cfg[code_entry].a      = tmp_pmp_cfg.a;
          pmp_cfg[code_entry].x      = tmp_pmp_cfg.x;
          pmp_cfg[code_entry].w      = tmp_pmp_cfg.w;
          pmp_cfg[code_entry].r      = tmp_pmp_cfg.r;
        end

        if (code_entry > 0) begin
          // Disable all configs before the code entry because PMP regions can be initialized with
          // any value and we need to make sure that the code entry is the first valid entry during
          // PMP setup.
          cfg_bitmask = 0;
          instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], cfg_bitmask));
          for (int i = 0; i < (code_entry / cfg_per_csr); i++) begin
            instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmpcfg_addr + i, scratch_reg[0]));
          end
        end
        // Enable the selected config on region code_entry.
        cfg_bitmask = cfg_byte << ((code_entry % cfg_per_csr) * 8);
        `uvm_info(`gfn, $sformatf("temporary code config: 0x%08x", cfg_bitmask), UVM_DEBUG)
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], cfg_bitmask));
        instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmpcfg_addr + (code_entry/cfg_per_csr),
                                  scratch_reg[0]));

        // Load the address of the kernel_stack_end into PMP stack entry.
        instr.push_back($sformatf("la x%0d, kernel_stack_end", scratch_reg[0]));
        // Add 4 to also include the final address of the kernel stack.
        instr.push_back($sformatf("addi x%0d, x%0d, 4", scratch_reg[0], scratch_reg[0]));
        instr.push_back($sformatf("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]));
        instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + stack_entry,
                                  scratch_reg[0]));
        `uvm_info(`gfn, $sformatf("Address of pmp_addr_%d is kernel_stack_end", stack_entry),
                  UVM_LOW)
        pmp_cfg_already_configured[stack_entry] = 1'b1;
        // In case the randomly selected stack_entry is not also specified in the arguments,
        // overwrite it in pmp_cfg. We use this for the stack entry.
        if (!inst.get_arg_value($sformatf("+pmp_region_%0d=", stack_entry), arg_value)) begin
          if (mseccfg.mml) begin
            // Marking the pmp stack region as shared write/read region before starting main.
            pmp_cfg[stack_entry].l = 1'b0;
            pmp_cfg[stack_entry].a = TOR;
            pmp_cfg[stack_entry].x = 1'b1;
            pmp_cfg[stack_entry].w = 1'b1;
            pmp_cfg[stack_entry].r = 1'b0;
          end else begin
            // We must set PMP stack region to write/read before starting main. X=0 to be consistent
            // with MML mode.
            pmp_cfg[stack_entry].l = 1'b0;
            pmp_cfg[stack_entry].a = TOR;
            pmp_cfg[stack_entry].x = 1'b0;
            pmp_cfg[stack_entry].w = 1'b1;
            pmp_cfg[stack_entry].r = 1'b1;
          end
        end
        // Load the signature address into PMP signature entry. This assumes the
        // end_signature_addr = signature_addr - 4. And that both are 4 Bytes.
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], end_signature_addr));
        instr.push_back($sformatf("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]));
        instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + sig_entry,
                                  scratch_reg[0]));
        `uvm_info(`gfn, $sformatf("Address of pmp_addr_%0d is signature_addr", sig_entry),
                  UVM_LOW)
        pmp_cfg_already_configured[sig_entry] = 1'b1;
        // In case the randomly selected sig_entry is not also specified in the arguments,
        // overwrite it in pmp_cfg. This is used for the signature address.
        if (!inst.get_arg_value($sformatf("+pmp_region_%0d=", sig_entry), arg_value)) begin
          if (mseccfg.mml) begin
            // Marking the PMP signature region as shared write/read region before starting main.
            pmp_cfg[sig_entry].l = 1'b0;
            pmp_cfg[sig_entry].a = NAPOT;
            pmp_cfg[sig_entry].x = 1'b1;
            pmp_cfg[sig_entry].w = 1'b1;
            pmp_cfg[sig_entry].r = 1'b0;
          end else begin
            // We must set PMP signature region to write/read before starting main. X=0 to be
            // consistent with MML mode.
            pmp_cfg[sig_entry].l = 1'b0;
            pmp_cfg[sig_entry].a = NAPOT;
            pmp_cfg[sig_entry].x = 1'b0;
            pmp_cfg[sig_entry].w = 1'b1;
            pmp_cfg[sig_entry].r = 1'b1;
          end
        end
      end

      // Writing MSECCFG with RLB still set to 1 otherwise we cannot complete configuration.
      `uvm_info(`gfn, $sformatf("MSECCFG: MML %0x, MMWP %0x, RLB 1", mseccfg.mml, mseccfg.mmwp),
                UVM_LOW)
      cfg_byte = {1'b1, mseccfg.mmwp, mseccfg.mml};
      instr.push_back($sformatf("csrwi 0x%0x, %0d", MSECCFG, cfg_byte));
    end

    foreach (pmp_cfg[i]) begin
      pmp_id = i / cfg_per_csr;
      cfg_byte = {pmp_cfg[i].l, pmp_cfg[i].zero, pmp_cfg[i].a,
                  pmp_cfg[i].x, pmp_cfg[i].w,    pmp_cfg[i].r};
      `uvm_info(`gfn, $sformatf("cfg_byte: 0x%02x", cfg_byte), UVM_LOW)
      // First write to the appropriate pmpaddr CSR.
      cfg_bitmask = cfg_byte << ((i % cfg_per_csr) * 8);
      `uvm_info(`gfn, $sformatf("cfg_bitmask: 0x%08x", cfg_bitmask), UVM_DEBUG)
      pmp_word = pmp_word | cfg_bitmask;
      `uvm_info(`gfn, $sformatf("pmp_word: 0x%08x", pmp_word), UVM_DEBUG)
      cfg_bitmask = 0;
      // If an actual address has been set from the command line, use this address,
      // otherwise use the default <main> + offset.
      //
      // TODO(udinator) - The practice of passing in a max offset from the command line
      //  is somewhat unintuitive, and is just an initial step. Eventually a max address
      //  should be passed in from the command line and this routine do all of the
      //  calculations to split the address range formed by [<main> : pmp_max_addr].
      //  This will likely require a complex assembly routine - the code below is a very simple
      //  first step towards this goal, allowing users to specify a PMP memory address
      //  from the command line instead of having to calculate an offset themselves.
      //
      // Only set the address if it has not already been configured in the above routine.
      if (pmp_cfg_already_configured[i] == 1'b0 || pmp_cfg_addr_valid[i]) begin
        if (pmp_cfg_addr_valid[i] || pmp_randomize) begin
          // In case an address was supplied by the test or full randomize is enabled.
          instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], pmp_cfg[i].addr));
          instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + i, scratch_reg[0]));
          `uvm_info(`gfn, $sformatf("Value 0x%08x loaded into pmpaddr[%d] CSR, corresponding to address 0x%0x", pmp_cfg[i].addr, i, pmp_cfg[i].addr << 2),
                    UVM_LOW);
        end else begin
          // Add the offset to the base address to get the other pmpaddr values.
          instr.push_back($sformatf("la x%0d, main", scratch_reg[0]));
          instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[1], pmp_cfg[i].offset));
          instr.push_back($sformatf("add x%0d, x%0d, x%0d",
                                    scratch_reg[0], scratch_reg[0], scratch_reg[1]));
          instr.push_back($sformatf("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]));
          instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmp_addr + i, scratch_reg[0]));
          `uvm_info(`gfn, $sformatf("Offset of pmp_addr_%d from main: 0x%08x", i,
                                    pmp_cfg[i].offset), UVM_LOW)
        end
      end
      // Now, check if we have to write to the appropriate pmpcfg CSR.
      // Short circuit if we reach the end of the list.
      if (i == pmp_cfg.size() - 1) begin
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], pmp_word));
        instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmpcfg_addr + pmp_id, scratch_reg[0]));
        break;
      end else if ((i + 1) % cfg_per_csr == 0) begin
        // If we've filled up pmp_word, write to the corresponding CSR.
        instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], pmp_word));
        instr.push_back($sformatf("csrw 0x%0x, x%0d", base_pmpcfg_addr + pmp_id, scratch_reg[0]));
        pmp_word = 0;
      end
    end

    // Unsetting RLB if that was requested.
    if (riscv_instr_pkg::support_epmp && !mseccfg.rlb) begin
      `uvm_info(`gfn, $sformatf("MSECCFG: MML %0x, MMWP %0x, RLB %0x", mseccfg.mml, mseccfg.mmwp,
                mseccfg.rlb), UVM_LOW)
      cfg_byte = {mseccfg.rlb, mseccfg.mmwp, mseccfg.mml};
      instr.push_back($sformatf("csrwi 0x%0x, %0d", MSECCFG, cfg_byte));
    end
  endfunction

  // This function creates a special PMP exception routine that is generated within the
  // instr_fault, load_fault, and store_fault exception routines to prevent infinite loops.
  // This routine will first find the correct pmpcfg CSR that corresponds to the address that
  // caused the exception in the first place, and then will enable the appropriate access bit
  // (X for instruction faults, W for store faults, and R for load faults).
  //
  // Note: If a pmpcfg CSR is locked, it is unable to be written to until a full reset, so in this
  //       case we will immediately jump to the <test_done> label if the faulting address matches to
  //       this region, otherwise we'll keep looping through the remaining CSRs.
  //
  // TODO(udinator) : investigate switching branch targets to named labels instead of numbers
  //                  to better clarify where the multitude of jumps are actually going to.
  function void gen_pmp_exception_routine(riscv_reg_t scratch_reg[7],
                                          exception_cause_t fault_type,
                                          ref string instr[$]);
    // scratch_reg[0] : temporary storage
    // scratch_reg[1] : &pmpaddr[i]
    // scratch_reg[2] : &pmpcfg[i]
    // scratch_reg[3] : 8-bit configuration fields
    // scratch_reg[4] : 2-bit pmpcfg[i].A address matching mode
    // scratch_reg[5] : holds the previous pmpaddr[i] value (necessary for TOR matching)
    // scratch_reg[6] : loop counter
    instr = {instr,
             ////////////////////////////////////////////////////////
             // Initialize loop counter and save to scratch_reg[6] //
             ////////////////////////////////////////////////////////
             $sformatf("li x%0d, 0", scratch_reg[0]),
             $sformatf("mv x%0d, x%0d", scratch_reg[6], scratch_reg[0]),
             $sformatf("li x%0d, 0", scratch_reg[5]),
             ////////////////////////////////////////////////////
             // calculate next pmpaddr and pmpcfg CSRs to read //
             ////////////////////////////////////////////////////
             $sformatf("0: mv x%0d, x%0d", scratch_reg[0], scratch_reg[6]),
             $sformatf("mv x%0d, x%0d", scratch_reg[4], scratch_reg[0])
            };
    // Generate a sequence of loads and branches that will compare the loop index to every
    // value within [0 : pmp_num_regions] to manually check which PMP CSRs to read from
    for (int i = 1; i < pmp_num_regions + 1; i++) begin
      int pmpaddr_addr = base_pmp_addr + i;
      int pmpcfg_addr = base_pmpcfg_addr + (i / cfg_per_csr);
      instr.push_back($sformatf("li x%0d, %0d", scratch_reg[4], i-1));
      instr.push_back($sformatf("beq x%0d, x%0d, %0df", scratch_reg[0], scratch_reg[4], i));
    end

    // Generate the branch targets for the above sequence of loads and branches to actually
    // read from the pmpaddr and pmpcfg CSRs
    for (int i = 1; i < pmp_num_regions + 1; i++) begin
      int pmpaddr_addr = base_pmp_addr + i;
      int pmpcfg_addr = base_pmpcfg_addr + (i / cfg_per_csr);
      instr.push_back($sformatf("%0d: csrr x%0d, 0x%0x", i, scratch_reg[1], base_pmp_addr + i - 1));
      instr.push_back($sformatf("csrr x%0d, 0x%0x", scratch_reg[2], base_pmpcfg_addr + ((i-1)/4)));
      instr.push_back("j 17f");
    end

    // Logic to store pmpaddr[i] and pmpcfg[i] and branch to a code section
    // based on pmpcfg[i].A (address matching mode)
    instr = {instr,
             ////////////////////////////////////////////
             // get correct 8-bit configuration fields //
             ////////////////////////////////////////////
             $sformatf("17: li x%0d, %0d", scratch_reg[3], cfg_per_csr),
             // calculate offset to left-shift pmpcfg[i] (scratch_reg[2]),
             // use scratch_reg[4] as temporary storage
             //
             // First calculate (loop_counter % cfg_per_csr)
             $sformatf("slli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[6],
                                               XLEN - $clog2(cfg_per_csr)),
             $sformatf("srli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[0],
                                               XLEN - $clog2(cfg_per_csr)),
             // Calculate (cfg_per_csr - modded_loop_counter - 1) to determine how many 8bit slots to
             // the left this needs to be shifted
             $sformatf("sub x%0d, x%0d, x%0d", scratch_reg[4], scratch_reg[3], scratch_reg[0]),
             $sformatf("addi x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[4], -1),
             // Multiply this "slot offset" by 8 to get the actual number of bits it should
             // be leftshifted.
             $sformatf("slli x%0d, x%0d, 3", scratch_reg[4], scratch_reg[4]),
             // Perform the leftshifting operation
             $sformatf("sll x%0d, x%0d, x%0d", scratch_reg[3], scratch_reg[2], scratch_reg[4]),
             // Add 8*modded_loop_counter to 8*(cfg_per_csr - modded_loop_counter - 1)
             // stored in scratch_reg[4] to get "slot offset" for the pending rightshift operation.
             $sformatf("slli x%0d, x%0d, 3", scratch_reg[0], scratch_reg[0]),
             $sformatf("add x%0d, x%0d, x%0d", scratch_reg[4], scratch_reg[4], scratch_reg[0]),
             // Perform the rightshift operation
             $sformatf("srl x%0d, x%0d, x%0d", scratch_reg[3], scratch_reg[3], scratch_reg[4]),
             ///////////////////////////
             // get pmpcfg[i].A field //
             ///////////////////////////
             // pmpcfg[i].A will be bits [4:3] of the 8-bit configuration entry
             $sformatf("slli x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[3], XLEN - 5),
             $sformatf("srli x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[4], XLEN - 2),
             //////////////////////////////////////////////////////////////////
             // based on address match mode, branch to appropriate "handler" //
             //////////////////////////////////////////////////////////////////
             // pmpcfg[i].A == OFF
             $sformatf("beqz x%0d, 20f", scratch_reg[4]),
             // pmpcfg[i].A == TOR
             // scratch_reg[5] will contain pmpaddr[i-1]
             $sformatf("li x%0d, 1", scratch_reg[0]),
             $sformatf("beq x%0d, x%0d, 21f", scratch_reg[4], scratch_reg[0]),
             // pmpcfg[i].A == NA4
             $sformatf("li x%0d, 2", scratch_reg[0]),
             $sformatf("beq x%0d, x%0d, 24f", scratch_reg[4], scratch_reg[0]),
             // pmpcfg[i].A == NAPOT
             $sformatf("li x%0d, 3", scratch_reg[0]),
             $sformatf("beq x%0d, x%0d, 25f", scratch_reg[4], scratch_reg[0]),
             // Error check, if no address modes match, something has gone wrong
             $sformatf("la x%0d, test_done", scratch_reg[0]),
             $sformatf("jalr x0, x%0d, 0", scratch_reg[0]),
             /////////////////////////////////////////////////////////////////
             // increment loop counter and branch back to beginning of loop //
             /////////////////////////////////////////////////////////////////
             $sformatf("18: mv x%0d, x%0d", scratch_reg[0], scratch_reg[6]),
             // load pmpaddr[i] into scratch_reg[5] to store for iteration [i+1]
             $sformatf("mv x%0d, x%0d", scratch_reg[5], scratch_reg[1]),
             // increment loop counter by 1
             $sformatf("addi x%0d, x%0d, 1", scratch_reg[0], scratch_reg[0]),
             // store loop counter to scratch_reg[6]
             $sformatf("mv x%0d, x%0d", scratch_reg[6], scratch_reg[0]),
             // load number of pmp regions - loop limit
             $sformatf("li x%0d, %0d", scratch_reg[1], pmp_num_regions),
             // if counter < pmp_num_regions => branch to beginning of loop,
             // otherwise jump to the end of the loop
             $sformatf("ble x%0d, x%0d, 19f", scratch_reg[1], scratch_reg[0]),
             $sformatf("j 0b"),
             // If we reach here, it means that no PMP entry has matched the request.
             // We must immediately jump to <test_done> since the CPU is taking a PMP exception,
             // but this routine is unable to find a matching PMP region for the faulting access -
             // there is a bug somewhere.
             // In case of MMWP mode this is expected behavior, we should try to continue.
             $sformatf("19: csrr x%0d, 0x%0x", scratch_reg[0], MSECCFG),
             $sformatf("andi x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]),
             $sformatf("bnez x%0d, 27f", scratch_reg[0]),
             $sformatf("la x%0d, test_done", scratch_reg[0]),
             $sformatf("jalr x0, x%0d, 0", scratch_reg[0])
            };

    /////////////////////////////////////////////////
    // Sub-sections for all address matching modes //
    /////////////////////////////////////////////////
    // scratch_reg[0] : temporary storage
    // scratch_reg[1] : pmpaddr[i]
    // scratch_reg[2] : pmpcfg[i]
    // scratch_reg[3] : 8-bit configuration fields
    // scratch_reg[4] : temporary storage
    // scratch_reg[5] : pmpaddr[i-1]

    // Sub-section to deal with address matching mode OFF.
    // If entry is OFF, simply continue looping through other PMP CSR.
    instr = {instr, "20: j 18b"};

    // Sub-section to handle address matching mode TOR.
    instr = {instr,
             $sformatf("21: mv x%0d, x%0d", scratch_reg[0], scratch_reg[6]),
             $sformatf("csrr x%0d, 0x%0x", scratch_reg[4], MTVAL),
             $sformatf("srli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[4]),
             // If loop_counter==0, compare fault_addr to 0
             $sformatf("bnez x%0d, 22f", scratch_reg[0]),
             // If fault_addr < 0 : continue looping
             $sformatf("bltz x%0d, 18b", scratch_reg[4]),
             $sformatf("j 23f"),
             // If fault_addr < pmpaddr[i-1] : continue looping
             $sformatf("22: bgtu x%0d, x%0d, 18b", scratch_reg[5], scratch_reg[4]),
             // If fault_addr >= pmpaddr[i] : continue looping
             $sformatf("23: bleu x%0d, x%0d, 18b", scratch_reg[1], scratch_reg[4]),
             $sformatf("j 26f")
            };

    // Sub-section to handle address matching mode NA4.
    // TODO(udinator) : add rv64 support
    instr = {instr,
             $sformatf("24: csrr x%0d, 0x%0x", scratch_reg[0], MTVAL),
             $sformatf("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]),
             // Zero out pmpaddr[i][31:30]
             $sformatf("slli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[1]),
             $sformatf("srli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[4]),
             // If fault_addr[31:2] != pmpaddr[i][29:0] => there is a mismatch,
             // so continue looping
             $sformatf("bne x%0d, x%0d, 18b", scratch_reg[0], scratch_reg[4]),
             $sformatf("j 26f")
            };

    // Sub-section to handle address matching mode NAPOT.
    instr = {instr,
             $sformatf("25: csrr x%0d, 0x%0x", scratch_reg[0], MTVAL),
             // get fault_addr[31:2]
             $sformatf("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]),
             // mask the bottom pmp_granularity bits of fault_addr
             $sformatf("srli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[0], pmp_granularity),
             $sformatf("slli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[0], pmp_granularity),
             // get pmpaddr[i][29:0]
             $sformatf("slli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[1]),
             $sformatf("srli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[4]),
             // mask the bottom pmp_granularity bits of pmpaddr[i]
             $sformatf("srli x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[4], pmp_granularity),
             $sformatf("slli x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[4], pmp_granularity),
             // If masked_fault_addr != masked_pmpaddr[i] : mismatch, so continue looping
             $sformatf("bne x%0d, x%0d, 18b", scratch_reg[0], scratch_reg[4]),
             $sformatf("j 26f")
           };

    // Sub-section that is common to the address modes deciding what to do what to do when hitting
    // a locked region
    instr = {instr,
             // If we get here there is an address match.
             // First check whether we are in MML mode.
             $sformatf("26: csrr x%0d, 0x%0x", scratch_reg[4], MSECCFG),
             $sformatf("andi x%0d, x%0d, 1", scratch_reg[4], scratch_reg[4]),
             $sformatf("bnez x%0d, 27f", scratch_reg[4]),
             // Then check whether the lock bit is set.
             $sformatf("andi x%0d, x%0d, 128", scratch_reg[4], scratch_reg[3]),
             $sformatf("bnez x%0d, 27f", scratch_reg[4]),
             $sformatf("j 29f")
            };

    // This case statement creates a bitmask that enables the correct access permissions
    // and ORs it with the 8-bit configuration fields.
    case (fault_type)
      INSTRUCTION_ACCESS_FAULT: begin
        instr = {instr,
                 // If MML or locked just quit the test.
                 $sformatf("27: la x%0d, test_done", scratch_reg[0]),
                 $sformatf("jalr x0, x%0d, 0", scratch_reg[0]),
                 // If neither is true then try to modify the PMP permission bits.
                 // The X bit is bit 2, and 1 << 2 = 2.
                 $sformatf("29: ori x%0d, x%0d, 4", scratch_reg[3], scratch_reg[3])
                };
      end
      STORE_AMO_ACCESS_FAULT: begin
        instr = {instr,
                 // If MML or locked try to load the instruction and see if it is compressed so
                 // the MEPC can be advanced appropriately.
                 $sformatf("27: csrr x%0d, 0x%0x", scratch_reg[0], MEPC),
                 // This might cause a load access fault, which we much handle in the load trap
                 // handler.
                 $sformatf("lw x%0d, 0(x%0d)", scratch_reg[0], scratch_reg[0]),
                 // Non-compressed instructions have two least significant bits set to one.
                 $sformatf("li x%0d, 3", scratch_reg[4]),
                 $sformatf("and x%0d, x%0d, x%0d", scratch_reg[0], scratch_reg[0], scratch_reg[4]),
                 // Check whether instruction is compressed.
                 $sformatf("beq x%0d, x%0d, 28f", scratch_reg[0], scratch_reg[4]),
                 $sformatf("csrr x%0d, 0x%0x", scratch_reg[0], MEPC),
                 // Increase MEPC by 2 in case instruction is compressed.
                 $sformatf("addi x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]),
                 $sformatf("csrw 0x%0x, x%0d", MEPC, scratch_reg[0]),
                 $sformatf("j 34f"),
                 $sformatf("28: csrr x%0d, 0x%0x", scratch_reg[0], MEPC),
                 // Increase MEPC by 4 in case instruction is compressed.
                 $sformatf("addi x%0d, x%0d, 4", scratch_reg[0], scratch_reg[0]),
                 $sformatf("csrw 0x%0x, x%0d", MEPC, scratch_reg[0]),
                 $sformatf("j 34f"),
                 // If neither is true then try to modify the PMP permission bits.
                 // The combination of W:1 and R:0 is reserved, so if we are enabling write
                 // permissions, also enable read permissions to adhere to the spec.
                 $sformatf("29: ori x%0d, x%0d, 3", scratch_reg[3], scratch_reg[3])
                };
      end
      LOAD_ACCESS_FAULT: begin
        instr = {instr,
                 // If MML or locked try to load the instruction and see if it is compressed so
                 // the MEPC can be advanced appropriately.
                 $sformatf("27: csrr x%0d, 0x%0x", scratch_reg[0], MEPC),
                 // We must first check whether the access fault was in the trap handler in case
                 // we previously tried to load an instruction in a PMP entry that did not have
                 // read permissions.
                 $sformatf("la x%0d, main", scratch_reg[4]),
                 $sformatf("bge x%0d, x%0d, 40f", scratch_reg[0], scratch_reg[4]),
                 // In case MEPC is before main, then the load access fault probably happened in a
                 // trap handler and we should just quit the test.
                 $sformatf("la x%0d, test_done", scratch_reg[0]),
                 $sformatf("jalr x0, x%0d, 0", scratch_reg[0]),
                 // This might cause a load access fault, which we much handle in the load trap
                 // handler.
                 $sformatf("40: lw x%0d, 0(x%0d)", scratch_reg[0], scratch_reg[0]),
                 // Non-compressed instructions have two least significant bits set to one.
                 $sformatf("li x%0d, 3", scratch_reg[4]),
                 $sformatf("and x%0d, x%0d, x%0d", scratch_reg[0], scratch_reg[0], scratch_reg[4]),
                 // Check whether instruction is compressed.
                 $sformatf("beq x%0d, x%0d, 28f", scratch_reg[0], scratch_reg[4]),
                 $sformatf("csrr x%0d, 0x%0x", scratch_reg[0], MEPC),
                 // Increase MEPC by 2 in case instruction is compressed.
                 $sformatf("addi x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]),
                 $sformatf("csrw 0x%0x, x%0d", MEPC, scratch_reg[0]),
                 $sformatf("j 34f"),
                 $sformatf("28: csrr x%0d, 0x%0x", scratch_reg[0], MEPC),
                 // Increase MEPC by 4 in case instruction is compressed.
                 $sformatf("addi x%0d, x%0d, 4", scratch_reg[0], scratch_reg[0]),
                 $sformatf("csrw 0x%0x, x%0d", MEPC, scratch_reg[0]),
                 $sformatf("j 34f"),
                 // If neither is true then try to modify the PMP permission bits.
                 // The R bit is bit 0, and 1 << 0 = 1.
                 $sformatf("29: ori x%0d, x%0d, 1", scratch_reg[3], scratch_reg[3])
                };
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid PMP fault type")
      end
    endcase
    instr = {instr,
             // Calculate (loop_counter % cfg_per_csr) to find the index of the correct
             // entry in pmpcfg[i].
             //
             // Calculate XLEN - $clog2(cfg_per_csr) to give how many low order bits
             // of loop_counter we need to keep around
             $sformatf("li x%0d, %0d", scratch_reg[4], XLEN - $clog2(cfg_per_csr)),
             // Now leftshift and rightshift loop_counter by this amount to clear all the upper
             // bits
             $sformatf("sll x%0d, x%0d, x%0d", scratch_reg[0], scratch_reg[6], scratch_reg[4]),
             $sformatf("srl x%0d, x%0d, x%0d", scratch_reg[0], scratch_reg[0], scratch_reg[4]),
             // Multiply the index by 8 to get the shift amount.
             $sformatf("slli x%0d, x%0d, 3", scratch_reg[4], scratch_reg[0]),
             // Shift the updated configuration byte to the proper alignment
             $sformatf("sll x%0d, x%0d, x%0d", scratch_reg[3], scratch_reg[3], scratch_reg[4]),
             // OR pmpcfg[i] with the updated configuration byte
             $sformatf("or x%0d, x%0d, x%0d", scratch_reg[2], scratch_reg[2], scratch_reg[3]),
             // Divide the loop counter by cfg_per_csr to determine which pmpcfg CSR to write to.
             $sformatf("mv x%0d, x%0d", scratch_reg[0], scratch_reg[6]),
             $sformatf("srli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[0], $clog2(cfg_per_csr)),
             // Write the updated pmpcfg[i] to the CSR bank and exit the handler.
             //
             // Don't touch scratch_reg[2], as it contains the updated pmpcfg[i] to be written.
             // All other scratch_reg[*] can be used.
             // scratch_reg[0] contains the index of the correct pmpcfg CSR.
             // We simply check the index and then write to the correct pmpcfg CSR based on its value.
             $sformatf("beqz x%0d, 30f", scratch_reg[0]),
             $sformatf("li x%0d, 1", scratch_reg[4]),
             $sformatf("beq x%0d, x%0d, 31f", scratch_reg[0], scratch_reg[4]),
             $sformatf("li x%0d, 2", scratch_reg[4]),
             $sformatf("beq x%0d, x%0d, 32f", scratch_reg[0], scratch_reg[4]),
             $sformatf("li x%0d, 3", scratch_reg[4]),
             $sformatf("beq x%0d, x%0d, 33f", scratch_reg[0], scratch_reg[4]),
             $sformatf("30: csrw 0x%0x, x%0d", PMPCFG0, scratch_reg[2]),
             $sformatf("j 34f"),
             $sformatf("31: csrw 0x%0x, x%0d", PMPCFG1, scratch_reg[2]),
             $sformatf("j 34f"),
             $sformatf("32: csrw 0x%0x, x%0d", PMPCFG2, scratch_reg[2]),
             $sformatf("j 34f"),
             $sformatf("33: csrw 0x%0x, x%0d", PMPCFG3, scratch_reg[2]),
             // End the pmp handler with a labeled nop instruction, this provides a branch target
             // for the internal routine after it has "fixed" the pmp configuration CSR.
             $sformatf("34: nop")
            };

  endfunction

  // This function is used for a directed PMP test to test writes to all the pmpcfg and pmpaddr
  // CSRs to test that writes succeed or fail appropriately.
  virtual function void gen_pmp_write_test(riscv_reg_t scratch_reg[2],
                                           ref string instr[$]);

    bit [11:0] pmp_addr;
    bit [11:0] pmpcfg_addr;
    bit [XLEN-1:0] pmp_val;
    for (int i = 0; i < pmp_num_regions; i++) begin
      pmp_addr = base_pmp_addr + i;
      pmpcfg_addr = base_pmpcfg_addr + (i / cfg_per_csr);
      // We randomize the lower 31 bits of pmp_val and then add this to the
      // address of <main>, guaranteeing that the random value written to
      // pmpaddr[i] doesn't interfere with the safe region.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(pmp_val, pmp_val[31] == 1'b0;)
      instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], pmp_val));
      instr.push_back($sformatf("la x%0d, main", scratch_reg[1]));
      instr.push_back($sformatf("add x%0d, x%0d, x%0d",
                                scratch_reg[0], scratch_reg[0], scratch_reg[1]));
      // Write the randomized address to pmpaddr[i].
      // Original value of pmpaddr[i] will be written to scratch_reg[0].
      instr.push_back($sformatf("csrrw x%0d, 0x%0x, x%0d",
                                scratch_reg[0], pmp_addr, scratch_reg[0]));
      // Restore the original address to pmpaddr[i].
      // New value of pmpaddr[i] will be written to scratch_reg[0].
      instr.push_back($sformatf("csrrw x%0d, 0x%0x, x%0d",
                                scratch_reg[0], pmp_addr, scratch_reg[0]));
      // Randomize value to be written to pmpcfg CSR.
      //
      // TODO: support rv64.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(pmp_val,
                                         foreach (pmp_val[i]) {
                                           // constrain each Lock bit to 0
                                           if ((i+1) % 8 == 0) {
                                             pmp_val[i] == 1'b0;
                                           }
                                           // prevent W=1/R=0 combination
                                           if (i % 8 == 0) { // this is an R bit
                                             !((pmp_val[i] == 0) && (pmp_val[i+1] == 1'b1));
                                           }
                                         }
                                        )
      // If we're writing to the pmpcfg CSR that contains region0 config information,
      // ensure that the "safe" region remains fully accessible.
      if (pmpcfg_addr == base_pmpcfg_addr) begin
        if (mseccfg.mml) begin
          // In case of MML make this a shared code region with LXWR='b1010.
          pmp_val[7:0] = 'h8a;
        end else begin
          pmp_val[7:0] = 'h0f;
        end
      end
      instr.push_back($sformatf("li x%0d, 0x%0x", scratch_reg[0], pmp_val));
      // Write the randomized address to pmpcfg[i].
      // Original value of pmpcfg[i] will be written to scratch_reg[0].
      instr.push_back($sformatf("csrrw x%0d, 0x%0x, x%0d",
                                scratch_reg[0], pmpcfg_addr, scratch_reg[0]));
      // Restore the original address to pmpcfg[i].
      // New value of pmpcfg[i] will be written to scratch_reg[0].
      instr.push_back($sformatf("csrrw x%0d, 0x%0x, x%0d",
                                scratch_reg[0], pmpcfg_addr, scratch_reg[0]));
    end

  endfunction

endclass
