/*
 * Copyright 2020 Google LLC
 * Copyright 2022 Coverify Systems Technology
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

module riscv.gen.riscv_pmp_cfg;

import riscv.gen.riscv_instr_pkg: pmp_cfg_reg_t, pmp_addr_mode_t,
  privileged_reg_t, riscv_reg_t, exception_cause_t, get_int_arg_value,
  get_bool_arg_value, get_hex_arg_value;

import riscv.gen.target: XLEN;
import std.format: format;

import esdl.data.bvec: ubvec, toubvec, tobvec, clog2;
import esdl.rand: rand, constraint;

import uvm;

class riscv_pmp_cfg: uvm_object {

  mixin uvm_object_utils;

  // default to a single PMP region
  @rand @UVM_DEFAULT int pmp_num_regions = 1;

  // default to granularity of 0 (4 bytes grain)
  @UVM_DEFAULT int pmp_granularity = 0;

  // number of configuration bytes per pmpcfg CSR
  int cfg_per_csr;

  // enable bit for pmp randomization
  bool pmp_randomize = false;

  // allow pmp randomization to cause address range overlap
  @rand bool pmp_allow_addr_overlap = false;

  // By default, after returning from a PMP exception, we return to the exact same instruction that
  // resulted in a PMP exception to begin with, creating an infinite loop of taking an exception.
  // To avoid this situation, this configuration knob will enable the relevant PMP exception
  // handlers to find the pmpcfg CSR that controls the address region resulting in the exception and
  // change the relevant access bit to 1'b1, allowing forward progress in the code, while also
  // allowing all access restrictions to be enforced.
  bool enable_pmp_exception_handler = true;

  // Setting this bit to 1'b1 enables generation of the directed stream of instructions to test
  // write accesses to all supported pmpaddr[i] CSRs.
  bool enable_write_pmp_csr;

  // pmp CSR configurations
  @rand pmp_cfg_reg_t[]  pmp_cfg;

  // This value is the address offset between the minimum and maximum pmpaddr
  // CSR values.
  // As pmpaddr0 will be set to the address of the <main> label, the address stored
  // in pmpaddr0 added to this pmp_max_offset value will give the upper bound of the
  // address range covered by the PMP address range.
  // Can be manually configured from the command line.
  @UVM_DEFAULT ubvec!(XLEN) pmp_max_offset = ubvec!(XLEN).max();

  // used to parse addr_mode configuration from cmdline
  alias addr_mode_wrapper = uvm_enum_wrapper!(pmp_addr_mode_t);
  pmp_addr_mode_t addr_mode;

  // Store the base addresses of pmpaddr0 and pmpcfg0
  privileged_reg_t base_pmp_addr = privileged_reg_t.PMPADDR0;
  privileged_reg_t base_pmpcfg_addr = privileged_reg_t.PMPCFG0;

  /////////////////////////////////////////////////
  // constraints - apply when pmp_randomize is 1 //
  /////////////////////////////////////////////////


  constraint! q{
    pmp_num_regions inside [1 : 16];
    pmp_granularity inside [0 : XLEN + 3];
  } sanity_c;


  constraint! q{
    foreach (cfg; pmp_cfg) {
      !(cfg.w && !cfg.r);
    }
  } xwr_c;

  constraint! q{
    foreach (cfg; pmp_cfg) {
      (pmp_granularity == 0) ->	(cfg.a != pmp_addr_mode_t.NAPOT);
      (pmp_granularity >= 1) -> (cfg.a != pmp_addr_mode_t.NA4);
    }
  } grain_addr_mode_c;

  constraint! q{
    foreach (i, cfg; pmp_cfg) {
      // Offset of pmp_cfg[0] does not matter, since it will be set to <main>,
      // so we do not constrain it here, as it will be overridden during generation
      if (i != 0) {
        cfg.offset inside [1 : pmp_max_offset];
      }
      else {
        cfg.offset == 0;
      }
    }
  }  addr_range_c;

  constraint! q{
    foreach (i, cfg; pmp_cfg) {
      if (!pmp_allow_addr_overlap && i > 0) {
        cfg.offset > pmp_cfg[i-1].offset;
      }
    }
  }  addr_overlapping_c;

  // Privileged spec states that in TOR mode, offset[i-1] < offset[i]
  constraint! q{
    foreach (cfg; pmp_cfg) {
      if (cfg.a == pmp_addr_mode_t.TOR) {
        pmp_allow_addr_overlap == false;
      }
    }
  }  tor_addr_overlap_c;

  this(string name = "") {
    string s;
    super(name);
    int pmp_max_offset_int;
    cfg_per_csr = XLEN / 8;
    if (uvm_cmdline_processor.get_inst().get_arg_value("+pmp_num_regions=", s)) {
      import std.conv: to;
      pmp_num_regions = s.to!int;
      rand_mode!q{pmp_num_regions}(false);
    }
    get_int_arg_value("+pmp_granularity=", pmp_granularity);
    get_bool_arg_value("+pmp_randomize=", pmp_randomize);
    get_bool_arg_value("+pmp_allow_addr_overlap=", pmp_allow_addr_overlap);
    get_bool_arg_value("+enable_write_pmp_csr=", enable_write_pmp_csr);
    get_hex_arg_value("+pmp_max_offset=", pmp_max_offset_int);
    pmp_max_offset = toubvec!XLEN(pmp_max_offset_int);
    uvm_info(get_full_name(), format("pmp max offset: 0x%0x", pmp_max_offset), UVM_LOW);
    pmp_cfg.length = pmp_num_regions;
  }

  void initialize(bool require_signature_addr) {
    if (!pmp_randomize) {
      set_defaults();
      setup_pmp();
    }
  }

  // This will only get called if pmp_randomize is set, in which case we apply command line
  // arguments after randomization
  void post_randomize() {
    // `ifdef _VCP //GRK958
    //     foreach(pmp_cfg[i]) pmp_cfg[i].zero = 2'b00;
    // `endif
    setup_pmp();
  }

  void set_defaults() {
    uvm_info(get_full_name(), format("MAX OFFSET: 0x%0x", pmp_max_offset), UVM_LOW);
    foreach (i, cfg; pmp_cfg) {
      cfg.l      = false;
      cfg.a      = pmp_addr_mode_t.TOR;
      cfg.x      = true;
      cfg.w      = true;
      cfg.r      = true;
      cfg.offset = assign_default_addr_offset(pmp_num_regions, cast(int) i);
    }
  }

  ubvec!XLEN  assign_default_addr_offset(int num_regions, int index) {
    ubvec!XLEN  offset;
    if (num_regions == 1) {
      assert (index == 0);
      offset = 0;
    }
    else {
      offset = pmp_max_offset / (num_regions - 1);
      offset = offset * index;
    }
    return offset;
  }

  void setup_pmp() {
    string arg_name;
    string pmp_region;
    foreach (i, ref cfg; pmp_cfg) {
      arg_name = format("+pmp_region_%0d=", i);
      if (uvm_cmdline_processor.get_inst().get_arg_value(arg_name, pmp_region)) {
        cfg = parse_pmp_config(pmp_region, cfg);
        uvm_info(get_full_name(), format("Configured pmp_cfg[%0d] from command line: %p",
					 i , cfg), UVM_LOW);
      }
    }
  }

  pmp_cfg_reg_t parse_pmp_config(string pmp_region, pmp_cfg_reg_t ref_pmp_cfg) {
    string [] fields;
    string [] field_vals;
    string field_type;
    string field_val;
    pmp_cfg_reg_t pmp_cfg_reg = ref_pmp_cfg;
    uvm_string_split(pmp_region, ',', fields);
    foreach (i, ref field; fields) {
      import std.conv: to;
      uvm_string_split(field, ':', field_vals);

      field_type = field_vals[0];
      field_val = field_vals[1];
      field_vals.length = 0;

      switch (field_type) {
      case "L" :
	pmp_cfg_reg.l = field_val.to!bool;
	break;
      case "A":
	bool ch_mode = addr_mode_wrapper.from_name(field_val, addr_mode);
	if(!ch_mode) uvm_error(get_full_name(), format("Check failed : %s", field_val));
	pmp_cfg_reg.a = addr_mode;
	break;
      case "X":
	pmp_cfg_reg.x = field_val.to!bool;
	break;
      case "W":
	pmp_cfg_reg.w = field_val.to!bool;
	break;
      case  "R":
	pmp_cfg_reg.r = field_val.to!bool;
	break;
      case "ADDR":
	// Don't have to convert address to "PMP format" here,
	// since it must be masked off in hardware
	static if (XLEN == 32) {
	  pmp_cfg_reg.addr = format_addr(toubvec!XLEN(field_val.to!uint(16)));
	}
	else static if (XLEN == 64) {
	  pmp_cfg_reg.addr = format_addr(toubvec!XLEN(field_val.to!ulong(16)));
	}
	else {
	  uvm_fatal(get_full_name(), format("Unsupported XLEN %0s", XLEN));
	}
	break;
      default:
	uvm_fatal(get_full_name(), format("%s, Invalid PMP configuration field name!", field_val));
      }
    }

    return pmp_cfg_reg;
  }

  ubvec!XLEN format_addr(ubvec!XLEN addr) {
    // For all ISAs, pmpaddr CSRs do not include the bottom two bits of the input address
    ubvec!XLEN    shifted_addr;
    shifted_addr = addr >> 2;
    switch (XLEN) {
      // RV32 - pmpaddr is bits [33:2] of the whole 34 bit address
      // Return the input address right-shifted by 2 bits
    case  32:
      return shifted_addr;
      // RV64 - pmpaddr is bits [55:2] of the whole 56 bit address, prepended by 10'b0
      // Return {10'b0, shifted_addr[53:0]}
    case  64:
      shifted_addr[53..64] = 0;
      return shifted_addr;
    default:
      uvm_fatal(get_full_name(), format("Unsupported XLEN %0s", XLEN));
      assert (false);
    }
  }

  // TODO(udinator) - implement function to return hardware masked pmpaddr "representation"
  ubvec!XLEN  convert_addr2pmp(ubvec!XLEN addr) {
    uvm_info(get_full_name(), "Placeholder function, need to implement", UVM_LOW);
    return addr;
  }

  ubvec!1  booltobit( bool x) {
    if ( x == true)
      return 0b1.toubvec!1;
    else
      return 0b0.toubvec!1;
  }

  // This function parses the pmp_cfg[] array to generate the actual instructions to set up
  // the PMP CSR registers.
  // Since either 4 (in rv32) or 8 (in rv64) PMP configuration registers fit into one physical
  // CSR, this function waits until it has reached this maximum to write to the physical CSR to
  // save some extraneous instructions from being performed.
  void gen_pmp_instr(riscv_reg_t[2] scratch_reg, ref string[] instr) {
    ubvec!XLEN   pmp_word;
    ubvec!XLEN   cfg_bitmask;
    ubvec!8       cfg_byte;
    int pmp_id;
    foreach (i, ref cfg; pmp_cfg) {

      // TODO(udinator) condense this calculations if possible
      pmp_id = cast(int) (i/cfg_per_csr);
      if (i == 0) {
	cfg_byte = tobvec!0b0 ~ cfg.zero ~ tobvec!2(pmp_addr_mode_t.TOR) ~ tobvec!3(0b111);
      }
      else {
	bool l, w, r, x;
	l = cfg.l;
	//a = cfg.a;
	x = cfg.x;
	w = cfg.w;
	r = cfg.r;
	cfg_byte = booltobit(l) ~ cfg.zero ~ tobvec!2(cfg.a)
	  ~ booltobit(x) ~ booltobit(w) ~ booltobit(r);
      }
      uvm_info(get_full_name(), format("cfg_byte: 0x%0x", cfg_byte), UVM_DEBUG);
      // First write to the appropriate pmpaddr CSR
      cfg_bitmask = cfg_byte << ((i % cfg_per_csr) * 8);
      uvm_info(get_full_name(), format("cfg_bitmask: 0x%0x", cfg_bitmask), UVM_DEBUG);
      pmp_word = pmp_word | cfg_bitmask;
      uvm_info(get_full_name(), format("pmp_word: 0x%0x", pmp_word), UVM_DEBUG);
      cfg_bitmask = 0;

      if (i == 0)  {
        // load the address of the <main> section into pmpaddr0
        instr ~= format("la x%0d, main", scratch_reg[0]);
        instr ~= format("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]);
        instr ~= format("csrw 0x%0x, x%0d", base_pmp_addr + i, scratch_reg[0]);
        uvm_info(get_full_name(), "Loaded the address of <main> section into pmpaddr0", UVM_LOW);
      }
      else {
        // If an actual address has been set from the command line, use this address,
        // otherwise use the default offset+<main> address
        //
        // TODO(udinator) - The practice of passing in a max offset from the command line
        //  is somewhat unintuitive, and is just an initial step. Eventually a max address
        //  should be passed in from the command line and this routine do all of the
        //  calculations to split the address range formed by [<main> : pmp_max_addr].
        //  This will likely require a complex assembly routine - the code below is a very simple
        //  first step towards this goal, allowing users to specify a PMP memory address
        //  from the command line instead of having to calculate an offset themselves.
        if (cfg.addr != 0) {
	  instr ~= format("li x%0d, 0x%0x", scratch_reg[0], cfg.addr);
	  instr ~= format("csrw 0x%0x, x%0d", base_pmp_addr + i, scratch_reg[0]);
	  uvm_info(get_full_name(),
		   format("Address 0x%0x loaded into pmpaddr[%d] CSR", base_pmp_addr + i, i),
		   UVM_LOW);
	}
	else {
          // Add the offset to the base address to get the other pmpaddr values
          instr ~= format("la x%0d, main", scratch_reg[0]);
          instr ~= format("li x%0d, 0x%0x", scratch_reg[1], cfg.offset);
          instr ~= format("add x%0d, x%0d, x%0d",
				scratch_reg[0], scratch_reg[0], scratch_reg[1]);
          instr ~= format("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]);
	  instr ~= format("csrw 0x%0x, x%0d", base_pmp_addr + i, scratch_reg[0]);
	  uvm_info(get_full_name(), format("Offset of pmp_addr_%d from pmpaddr0: 0x%0x",
					   i, cfg.offset), UVM_LOW);
        }
      }

      // Now, check if we have to write to the appropriate pmpcfg CSR.
      // Short circuit if we reach the end of the list
      if (i == pmp_cfg.length - 1) {

        instr ~= format("li x%0d, 0x%0x", scratch_reg[0], pmp_word);
        instr ~= format("csrw 0x%0x, x%0d",
			base_pmpcfg_addr + pmp_id,
			scratch_reg[0]);
        return;
      }
      else if ((i + 1) % cfg_per_csr == 0) {
        // if we've filled up pmp_word, write to the corresponding CSR
        instr ~= format("li x%0d, 0x%0x", scratch_reg[0], pmp_word);
        instr ~= format("csrw 0x%0x, x%0d",
			base_pmpcfg_addr + pmp_id,
			scratch_reg[0]);
        pmp_word = 0;
      }
    }
  }

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
  void gen_pmp_exception_routine(riscv_reg_t[] scratch_reg,
				 exception_cause_t fault_type,
				 ref string[] instr) {
    assert (scratch_reg.length == 6);
    // mscratch       : loop counter
    // scratch_reg[0] : temporary storage
    // scratch_reg[1] : &pmpaddr[i]
    // scratch_reg[2] : &pmpcfg[i]
    // scratch_reg[3] : 8-bit configuration fields
    // scratch_reg[4] : 2-bit pmpcfg[i].A address matching mode
    // scratch_reg[5] : holds the previous pmpaddr[i] value (necessary for TOR matching)
    instr ~=
      //////////////////////////////////////////////////
      // Initialize loop counter and save to mscratch //
      //////////////////////////////////////////////////
      [format("li x%0d, 0", scratch_reg[0]),
       format("csrw 0x%0x, x%0d", privileged_reg_t.MSCRATCH, scratch_reg[0]),
       format("li x%0d, 0", scratch_reg[5]),
      ////////////////////////////////////////////////////
      // calculate next pmpaddr and pmpcfg CSRs to read //
      ////////////////////////////////////////////////////
       format("0: csrr x%0d, 0x%0x", scratch_reg[0], privileged_reg_t.MSCRATCH),
       format("mv x%0d, x%0d", scratch_reg[4], scratch_reg[0])];

    // Generate a sequence of loads and branches that will compare the loop index to every
    // value within [0 : pmp_num_regions] to manually check which PMP CSRs to read from
    for (int i = 1; i < pmp_num_regions + 1; i++) {
      int pmpaddr_addr = base_pmp_addr + i;
      int pmpcfg_addr = base_pmpcfg_addr + (i / cfg_per_csr);
      instr ~= format("li x%0d, %0d", scratch_reg[4], i-1);
      instr ~= format("beq x%0d, x%0d, %0df", scratch_reg[0], scratch_reg[4], i);
    }

    // Generate the branch targets for the above sequence of loads and branches to actually
    // read from the pmpaddr and pmpcfg CSRs
    for (int i = 1; i < pmp_num_regions + 1; i++) {
      int pmpaddr_addr = base_pmp_addr + i;
      int pmpcfg_addr = base_pmpcfg_addr + (i / cfg_per_csr);
      instr ~= format("%0d: csrr x%0d, 0x%0x", i, scratch_reg[1], base_pmp_addr + i - 1);
      instr ~= format("csrr x%0d, 0x%0x", scratch_reg[2], base_pmpcfg_addr + ((i-1)/4));
      instr ~=  ("j 17f");
    }

    // Logic to store pmpaddr[i] and pmpcfg[i] and branch to a code section
    // based on pmpcfg[i].A (address matching mode)
    instr ~=
      ////////////////////////////////////////////
      // get correct 8-bit configuration fields //
      ////////////////////////////////////////////
      [format("17: li x%0d, %0d", scratch_reg[3], cfg_per_csr),
       format("csrr x%0d, 0x%0x", scratch_reg[0], privileged_reg_t.MSCRATCH),
       // calculate offset to left-shift pmpcfg[i] (scratch_reg[2]),
       // use scratch_reg[4] as temporary storage
       //
       // First calculate (loop_counter % cfg_per_csr)
       format("slli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[0],
	      XLEN - clog2(cfg_per_csr)),
       format("srli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[0],
	      XLEN - clog2(cfg_per_csr)),
       // Calculate (cfg_per_csr - modded_loop_counter - 1) to determine how many 8bit slots to
       // the left this needs to be shifted
       format("sub x%0d, x%0d, x%0d", scratch_reg[4], scratch_reg[3], scratch_reg[0]),
       format("addi x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[4], -1),
       // Multiply this "slot offset" by 8 to get the actual number of bits it should
       // be leftshifted.
       format("slli x%0d, x%0d, 3", scratch_reg[4], scratch_reg[4]),
       // Perform the leftshifting operation
       format("sll x%0d, x%0d, x%0d", scratch_reg[3], scratch_reg[2], scratch_reg[4]),
       // Add 8*modded_loop_counter to 8*(cfg_per_csr - modded_loop_counter - 1)
       // stored in scratch_reg[4] to get "slot offset" for the pending rightshift operation.
       format("slli x%0d, x%0d, 3", scratch_reg[0], scratch_reg[0]),
       format("add x%0d, x%0d, x%0d", scratch_reg[4], scratch_reg[4], scratch_reg[0]),
       // Perform the rightshift operation
       format("srl x%0d, x%0d, x%0d", scratch_reg[3], scratch_reg[3], scratch_reg[4]),
       ///////////////////////////
       // get pmpcfg[i].A field //
       ///////////////////////////
       // pmpcfg[i].A will be bits [4:3] of the 8-bit configuration entry
       format("slli x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[3], XLEN - 5),
       format("srli x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[4], XLEN - 2),
       //////////////////////////////////////////////////////////////////
       // based on address match mode, branch to appropriate "handler" //
       //////////////////////////////////////////////////////////////////
       // pmpcfg[i].A == OFF
       format("beqz x%0d, 20f", scratch_reg[4]),
       // pmpcfg[i].A == TOR
       // scratch_reg[5] will contain pmpaddr[i-1]
       format("li x%0d, 1", scratch_reg[0]),
       format("beq x%0d, x%0d, 21f", scratch_reg[4], scratch_reg[0]),
       // pmpcfg[i].A == NA4
       format("li x%0d, 2", scratch_reg[0]),
       format("beq x%0d, x%0d, 25f", scratch_reg[4], scratch_reg[0]),
       // pmpcfg[i].A == NAPOT
       format("li x%0d, 3", scratch_reg[0]),
       format("beq x%0d, x%0d, 27f", scratch_reg[4], scratch_reg[0]),
       // Error check, if no address modes match, something has gone wrong
       format("la x%0d, test_done", scratch_reg[0]),
       format("jalr x0, x%0d, 0", scratch_reg[0]),
       /////////////////////////////////////////////////////////////////
       // increment loop counter and branch back to beginning of loop //
       /////////////////////////////////////////////////////////////////
       format("18: csrr x%0d, 0x%0x", scratch_reg[0], privileged_reg_t.MSCRATCH),
       // load pmpaddr[i] into scratch_reg[5] to store for iteration [i+1]
       format("mv x%0d, x%0d", scratch_reg[5], scratch_reg[1]),
       // increment loop counter by 1
       format("addi x%0d, x%0d, 1", scratch_reg[0], scratch_reg[0]),
       // store loop counter to MSCRATCH
       format("csrw 0x%0x, x%0d", privileged_reg_t.MSCRATCH, scratch_reg[0]),
       // load number of pmp regions - loop limit
       format("li x%0d, %0d", scratch_reg[1], pmp_num_regions),
       // if counter < pmp_num_regions => branch to beginning of loop,
       // otherwise jump to the end of the loop
       format("ble x%0d, x%0d, 19f", scratch_reg[1], scratch_reg[0]),
       format("j 0b"),
       // If we reach here, it means that no PMP entry has matched the request.
       // We must immediately jump to <test_done> since the CPU is taking a PMP exception,
       // but this routine is unable to find a matching PMP region for the faulting access -
       // there is a bug somewhere.
       format("19: la x%0d, test_done", scratch_reg[0]),
       format("jalr x0, x%0d, 0", scratch_reg[0])];

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
    instr ~= "20: j 18b" ;

    // Sub-section to handle address matching mode TOR.
    instr ~=
      [format("21: csrr x%0d, 0x%0x", scratch_reg[0], privileged_reg_t.MSCRATCH),
       format("csrr x%0d, 0x%0x", scratch_reg[4], privileged_reg_t.MTVAL),
       format("srli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[4]),
       // If loop_counter==0, compare fault_addr to 0
       format("bnez x%0d, 22f", scratch_reg[0]),
       // If fault_addr < 0 : continue looping
       format("bltz x%0d, 18b", scratch_reg[4]),
       format("j 23f"),
       // If fault_addr < pmpaddr[i-1] : continue looping
       format("22: bgtu x%0d, x%0d, 18b", scratch_reg[5], scratch_reg[4]),
       // If fault_addr >= pmpaddr[i] : continue looping
       format("23: bleu x%0d, x%0d, 18b", scratch_reg[1], scratch_reg[4]),
       // If we get here, there is a TOR match, if the entry is locked jump to
       // <test_done>, otherwise modify access bits and return
       format("andi x%0d, x%0d, 128", scratch_reg[4], scratch_reg[3]),
       format("beqz x%0d, 24f", scratch_reg[4]),
       format("la x%0d, test_done", scratch_reg[0]),
       format("jalr x0, x%0d, 0", scratch_reg[0]),
       format("24: j 29f")];

    // Sub-section to handle address matching mode NA4.
    // TODO(udinator) : add rv64 support
    instr ~=
      [format("25: csrr x%0d, 0x%0x", scratch_reg[0], privileged_reg_t.MTVAL),
       format("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]),
       // Zero out pmpaddr[i][31:30]
       format("slli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[1]),
       format("srli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[4]),
       // If fault_addr[31:2] != pmpaddr[i][29:0] => there is a mismatch,
       // so continue looping
       format("bne x%0d, x%0d, 18b", scratch_reg[0], scratch_reg[4]),
       // If we get here, there is an NA4 address match, jump to <test_done> if the
       // entry is locked, otherwise modify access bits
       format("andi x%0d, x%0d, 128", scratch_reg[4], scratch_reg[3]),
       format("beqz x%0d, 26f", scratch_reg[4]),
       format("la x%0d, test_done", scratch_reg[0]),
       format("jalr x0, x%0d, 0", scratch_reg[0]),
       format("26: j 29f")];

    // Sub-section to handle address matching mode NAPOT.
    instr ~=
      [format("27: csrr x%0d, 0x%0x", scratch_reg[0], privileged_reg_t.MTVAL),
       // get fault_addr[31:2]
       format("srli x%0d, x%0d, 2", scratch_reg[0], scratch_reg[0]),
       // mask the bottom pmp_granularity bits of fault_addr
       format("srli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[0], pmp_granularity),
       format("slli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[0], pmp_granularity),
       // get pmpaddr[i][29:0]
       format("slli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[1]),
       format("srli x%0d, x%0d, 2", scratch_reg[4], scratch_reg[4]),
       // mask the bottom pmp_granularity bits of pmpaddr[i]
       format("srli x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[4], pmp_granularity),
       format("slli x%0d, x%0d, %0d", scratch_reg[4], scratch_reg[4], pmp_granularity),
       // If masked_fault_addr != masked_pmpaddr[i] : mismatch, so continue looping
       format("bne x%0d, x%0d, 18b", scratch_reg[0], scratch_reg[4]),
       // If we get here there is an NAPOT address match, jump to <test_done> if
       // the entry is locked, otherwise modify access bits
       format("andi x%0d, x%0d, 128", scratch_reg[4], scratch_reg[3]),
       format("beqz x%0d, 29f", scratch_reg[4]),
       format("la x%0d, test_done", scratch_reg[0]),
       format("jalr x0, x%0d, 0", scratch_reg[0]),
       format("28: j 29f")];


    // This case statement creates a bitmask that enables the correct access permissions
    // and ORs it with the 8-bit configuration fields.
    switch  (fault_type) {
    case  exception_cause_t.INSTRUCTION_ACCESS_FAULT:
      instr ~= format("29: ori x%0d, x%0d, 4", scratch_reg[3], scratch_reg[3]);
      break;
    case  exception_cause_t.STORE_AMO_ACCESS_FAULT:
      // The combination of W:1 and R:0 is reserved, so if we are enabling write
      // permissions, also enable read permissions to adhere to the spec.
      instr ~= format("29: ori x%0d, x%0d, 3", scratch_reg[3], scratch_reg[3]);
      break;
    case exception_cause_t.LOAD_ACCESS_FAULT:
      instr ~= format("29: ori x%0d, x%0d, 1", scratch_reg[3], scratch_reg[3]);
      break;
    default:
      uvm_fatal(get_full_name(), "Invalid PMP fault type");
      break;
    }
    instr ~=
      [format("csrr x%0d, 0x%0x", scratch_reg[0], privileged_reg_t.MSCRATCH),
       // Calculate (loop_counter % cfg_per_csr) to find the index of the correct
       // entry in pmpcfg[i].
       //
       // Calculate XLEN - $clog2(cfg_per_csr) to give how many low order bits
       // of loop_counter we need to keep around
       format("li x%0d, %0d", scratch_reg[4], XLEN - clog2(cfg_per_csr)),
       // Now leftshift and rightshift loop_counter by this amount to clear all the upper
       // bits
       format("sll x%0d, x%0d, x%0d", scratch_reg[0], scratch_reg[0], scratch_reg[4]),
       format("srl x%0d, x%0d, x%0d", scratch_reg[0], scratch_reg[0], scratch_reg[4]),
       // Multiply the index by 8 to get the shift amount.
       format("slli x%0d, x%0d, 3", scratch_reg[4], scratch_reg[0]),
       // Shift the updated configuration byte to the proper alignment
       format("sll x%0d, x%0d, x%0d", scratch_reg[3], scratch_reg[3], scratch_reg[4]),
       // OR pmpcfg[i] with the updated configuration byte
       format("or x%0d, x%0d, x%0d", scratch_reg[2], scratch_reg[2], scratch_reg[3]),
       // Divide the loop counter by cfg_per_csr to determine which pmpcfg CSR to write to.
       format("csrr x%0d, 0x%0x", scratch_reg[0], privileged_reg_t.MSCRATCH),
       format("srli x%0d, x%0d, %0d", scratch_reg[0], scratch_reg[0], clog2(cfg_per_csr)),
       // Write the updated pmpcfg[i] to the CSR bank and exit the handler.
       //
       // Don't touch scratch_reg[2], as it contains the updated pmpcfg[i] to be written.
       // All other scratch_reg[*] can be used.
       // scratch_reg[0] contains the index of the correct pmpcfg CSR.
       // We simply check the index and then write to the correct pmpcfg CSR based on its value.
       format("beqz x%0d, 30f", scratch_reg[0]),
       format("li x%0d, 1", scratch_reg[4]),
       format("beq x%0d, x%0d, 31f", scratch_reg[0], scratch_reg[4]),
       format("li x%0d, 2", scratch_reg[4]),
       format("beq x%0d, x%0d, 32f", scratch_reg[0], scratch_reg[4]),
       format("li x%0d, 3", scratch_reg[4]),
       format("beq x%0d, x%0d, 33f", scratch_reg[0], scratch_reg[4]),
       format("30: csrw 0x%0x, x%0d", privileged_reg_t.PMPCFG0, scratch_reg[2]),
       format("j 34f"),
       format("31: csrw 0x%0x, x%0d", privileged_reg_t.PMPCFG1, scratch_reg[2]),
       format("j 34f"),
       format("32: csrw 0x%0x, x%0d", privileged_reg_t.PMPCFG2, scratch_reg[2]),
       format("j 34f"),
       format("33: csrw 0x%0x, x%0d", privileged_reg_t.PMPCFG3, scratch_reg[2]),
       // End the pmp handler with a labeled nop instruction, this provides a branch target
       // for the internal routine after it has "fixed" the pmp configuration CSR.
       format("34: nop")];
  }

  // This function is used for a directed PMP test to test writes to all the pmpcfg and pmpaddr
  // CSRs to test that writes succeed or fail appropriately.
  void gen_pmp_write_test(riscv_reg_t[2] scratch_reg,
			  ref string[] instr) {
    import esdl.base.rand: urandom;
    ubvec!12 pmp_addr;
    ubvec!12 pmpcfg_addr;
    ubvec!XLEN pmp_val;
    for (int i = 0; i < pmp_num_regions; i++) {
      pmp_addr.assign(base_pmp_addr + i);
      pmpcfg_addr.assign(base_pmpcfg_addr + (i / cfg_per_csr));
      // We randomize the lower 31 bits of pmp_val and then add this to the
      // address of <main>, guaranteeing that the random value written to
      // pmpaddr[i] doesn't interfere with the safe region.

      // `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(pmp_val, pmp_val[31] == 1'b0;)
      pmp_val = urandom!(ubvec!XLEN)();
      pmp_val[31] = false;

      instr ~= format("li x%0d, 0x%0x", scratch_reg[0], pmp_val);
      instr ~= format("la x%0d, main", scratch_reg[1]);
      instr ~= format("add x%0d, x%0d, x%0d",
		      scratch_reg[0], scratch_reg[0], scratch_reg[1]);
      // Write the randomized address to pmpaddr[i].
      // Original value of pmpaddr[i] will be written to scratch_reg[0].
      instr ~= format("csrrw x%0d, 0x%0x, x%0d",
		      scratch_reg[0], pmp_addr, scratch_reg[0]);
      // Restore the original address to pmpaddr[i].
      // New value of pmpaddr[i] will be written to scratch_reg[0].
      instr ~= format("csrrw x%0d, 0x%0x, x%0d",
		      scratch_reg[0], pmp_addr, scratch_reg[0]);
      // Randomize value to be written to pmpcfg CSR.
      //
      // TODO: support rv64.
      // `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(pmp_val,
      //                                    foreach (pmp_val[i]) {
      //                                      // constrain each Lock bit to 0
      //                                      if ((i+1) % 8 == 0) {
      //                                        pmp_val[i] == 1'b0;
      //                                      }
      //                                      // prevent W=1/R=0 combination
      //                                      if (i % 8 == 0) { // this is an R bit
      //                                        !((pmp_val[i] == 0) && (pmp_val[i+1] == 1'b1));
      // 					   }
      //                                    }
      //                                   )
      pmp_val = urandom!(ubvec!XLEN)();

      for (size_t j=0; j!=XLEN/8; ++j) {
	pmp_val[j*8+7] = false;
	ubvec!XLEN mask = ~ (toubvec!XLEN(0b11));
	ubvec!XLEN bits;
	uint r;

	switch (urandom(0, 3)) {
	case 0: bits[1] = false; bits[0] = false;
	  break;
	case 1: bits[1] = false; bits[0] = true;
	  break;
	case 2: bits[1] = true; bits[0] = true;
	  break;
	default: assert (false);
	}

	mask <<= j * 8;
	bits <<= j * 8;

	pmp_val &= mask;
	pmp_val |= bits;
      }

      // If we're writing to the pmpcfg CSR that contains region0 config information,
      // ensure that the "safe" region remains fully accessible.
      if (pmpcfg_addr == base_pmpcfg_addr) {
	pmp_val[0..8] = cast(ubyte) 0x0f;
      }
      instr ~= format("li x%0d, 0x%0x", scratch_reg[0], pmp_val);
      // Write the randomized address to pmpcfg[i].
      // Original value of pmpcfg[i] will be written to scratch_reg[0].
      instr ~= format("csrrw x%0d, 0x%0x, x%0d",
		      scratch_reg[0], pmpcfg_addr, scratch_reg[0]);
      // Restore the original address to pmpcfg[i].
      // New value of pmpcfg[i] will be written to scratch_reg[0].
      instr ~= format("csrrw x%0d, 0x%0x, x%0d",
		      scratch_reg[0], pmpcfg_addr, scratch_reg[0]);
    }
  }
}
