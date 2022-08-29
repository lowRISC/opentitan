/*
 * Copyright 2018 Google LLC
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

//----------------------------------------------------------------------------------------------
// Complete RISC-V page table generator
//
// This class is used to generate all the page tables and link them together.
// Below features are supported:
// - Multiple PTEs for each page table
// - Multiple tables at each level(except for root table)
// - Mixed leaf entry and non-leaf entry at any level
// - Allow injecting page table exceptions for any PTE
//----------------------------------------------------------------------------------------------
module riscv.gen.riscv_page_table_list;


import riscv.gen.riscv_instr_pkg: satp_mode_t, privileged_mode_t, riscv_reg_t,
  privileged_reg_t, pte_permission_t, pop_gpr_from_kernel_stack,
  MAX_USED_VADDR_BITS, MPRV_BIT_MASK;
import riscv.gen.target: XLEN, SATP_MODE;
import riscv.gen.riscv_page_table_exception_cfg: riscv_page_table_exception_cfg;
import riscv.gen.riscv_page_table_entry: riscv_page_table_entry;
import riscv.gen.riscv_page_table: riscv_page_table;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;
import std.string: format;

import esdl.data.bvec: ubvec, clog2;
import esdl.rand: constraint, rand, randomize_with, randomize;
import uvm;

version(CHECK_COMPILE) alias riscv_page_table_list_SV39 = riscv_page_table_list!(satp_mode_t.SV39);

class riscv_page_table_list(satp_mode_t MODE = satp_mode_t.SV39) : uvm_object
{
  mixin uvm_object_utils;

  enum int PteSize   = XLEN / 8;
  enum int PteCnt    = 4096 / PteSize;
  enum int PageLevel = (MODE == satp_mode_t.SV32) ? 2 : ((MODE == satp_mode_t.SV39) ? 3 : 4);
  enum int LinkPtePerTable = 2;
  enum int SuperLeafPtePerTable = 2;

  satp_mode_t mode = MODE;

  // Privileged mode of the program
  privileged_mode_t privileged_mode = privileged_mode_t.USER_MODE;

  // Starting physical address of the program.
  ubvec!XLEN start_pa = 0x80000000;

  // Num of page table per level
  uint[]  num_of_page_table;

  // Page table list, from highest level to the lowest level
  riscv_page_table!(MODE)[] page_table;

  // Root page table PTE idx for the init code entry
  uint  root_init_pte_idx;

  // Instruction generator configuration
  riscv_instr_gen_config cfg;

  // Allow exception or not
  bool enable_exception;
  riscv_page_table_exception_cfg exception_cfg;

  // Valid PTE entry for exception recovery
  riscv_page_table_entry!(MODE) valid_leaf_pte;
  riscv_page_table_entry!(MODE) valid_link_pte;
  riscv_page_table_entry!(MODE) valid_data_leaf_pte;
  riscv_page_table_entry!(MODE) illegal_pte;

  // Registers used for page table exception handling
  @rand riscv_reg_t level_reg;
  @rand riscv_reg_t fault_vaddr_reg;
  @rand riscv_reg_t pte_addr_reg;
  @rand riscv_reg_t pte_reg;
  @rand riscv_reg_t tmp_reg;
  @rand riscv_reg_t mask_reg;
  @rand riscv_reg_t mpp_reg;

  constraint! q{
    unique [level_reg, fault_vaddr_reg, pte_addr_reg,
            pte_reg, tmp_reg, mask_reg, mpp_reg];
    level_reg !inside [cfg.reserved_regs, riscv_reg_t.ZERO];
    fault_vaddr_reg !inside [cfg.reserved_regs, riscv_reg_t.ZERO];
    pte_addr_reg !inside [cfg.reserved_regs, riscv_reg_t.ZERO];
    pte_reg !inside [cfg.reserved_regs, riscv_reg_t.ZERO];
    mask_reg !inside [cfg.reserved_regs, riscv_reg_t.ZERO];
    mpp_reg !inside [cfg.reserved_regs, riscv_reg_t.ZERO];
    tmp_reg !inside [cfg.reserved_regs, riscv_reg_t.ZERO];
  } page_table_exception_handling_reg_c ;

  this(string name = "") {
    super(name);
    default_page_table_setting();
    exception_cfg = riscv_page_table_exception_cfg.type_id.create("exception_cfg");
    valid_leaf_pte = riscv_page_table_entry!(MODE).type_id.create("valid_leaf_pte");
    valid_link_pte = riscv_page_table_entry!(MODE).type_id.create("valid_link_pte");
    valid_data_leaf_pte = riscv_page_table_entry!(MODE).type_id.create("valid_data_leaf_pte");
    illegal_pte = riscv_page_table_entry!(MODE).type_id.create("illegal_pte");
  }

  // To avoid large numbers of page tables, by default we limit the number of non-leaf PTE
  // at higher level. To be more specific, all PTEs of level 0 page table is leaf PTE. For
  // higher level page table, only PTE[0] and PTE[1] is non-leaf PTE, all other PTEs are leaf
  // PTE. All leaf PTE should have PPN map to the real physical address of the instruction
  // or data. For non-leaf PTE, the PPN should map to the physical address of the next PTE.
  // Take SV39 for example: (PteSize = 8B)
  // Table size is 4KB, PteSize=8B, entry count = 4K/8 = 512
  // Level 2: Root table, 2 entries, PTE[0] and PTE[1] is non-leaf PTE, PTE[2] is leaf PTE, all
  //          other PTEs are invalid, totalling 1 page table with 3 PTEs at this level.
  // Level 1: Two page tables, map to PTE[0] and PTE[1] of the root table.
  //          Each table has 512 entries, PTE[0], PTE[1] are non-leaf PTE, cover 4MB memory
  //          space. PTE[2:511] are leaf PTE, cover 510 * 2MB memory space.
  // Level 0: 4 page tables at this level(map to PTE[0] and PTE[1] of the previous level),
  //          each table has 512 leaf PTE.
  // In summary, 7(1+2+4) tables are needed for SV39.
  // Similarly, 3 (1+2) page tables for SV32, 15 (1 + 2 + 4 + 8) page tables for SV48.
  // Note:
  // - The number of randomization call is optimized to improve performance
  // - PPN assignment is done at program run time
  void randomize_page_table() {
    int pte_index;
    exception_cfg.enable_exception = enable_exception;
    create_valid_pte();
    foreach (i, ptbl; page_table) {
      uvm_info(get_full_name(), format("Randomizing page table %0d, num of PTE: %0d",
				     i, ptbl.pte.length), UVM_LOW);
      if (i == 0) {
        pte_index = 0;
      }
      else if(ptbl.level != page_table[i-1].level) {
        pte_index = 0;
      }
      foreach (j, ref entry; ptbl.pte) {
	if (ptbl.level > 0) {
          // Superpage
          if (j < LinkPtePerTable) {
	    entry = cast(riscv_page_table_entry!MODE) valid_link_pte.clone();
            // First few super pages are link PTE to the next level
	    // $cast(page_table[i].pte[j], valid_link_pte.clone());
          }
	  else if (j < SuperLeafPtePerTable + LinkPtePerTable) {
	    entry = cast(riscv_page_table_entry!MODE) valid_leaf_pte.clone();
            // Non-link superpage table entry
	    //  $cast(page_table[i].pte[j], valid_leaf_pte.clone());
          }
	  else {
            // Invalid unused PTEs
            entry = riscv_page_table_entry!(MODE).type_id.
	      create(format("pte_%0d_%0d",i, j));
            entry.v = false;
          }
        }
	else {
	  entry = cast(riscv_page_table_entry!MODE) valid_leaf_pte.clone();
	  // Lowest level leaf pages
	  // $cast(page_table[i].pte[j], valid_leaf_pte.clone());
	}
	if (entry.xwr != pte_permission_t.NEXT_LEVEL_PAGE) {
          entry.set_ppn(start_pa, pte_index, ptbl.level);
        }
        pte_index++;
        if(enable_exception) {
	  inject_page_table_exception(entry, ptbl.level);
	}
        entry.pack_entry();
        uvm_info(get_full_name(), format("%0s PT_%0d_%0d: %0s", privileged_mode,
					 i, j, entry.convert2string()), UVM_HIGH);
      }
    }
  }

  // Create the basic legal page table entries
  void create_valid_pte() {
    valid_leaf_pte.randomize_with! q{
      if ($0 == $1) {
        u == true;
      }
      else {
        // Accessing user mode page from supervisor mode is only allowed when MSTATUS.SUM and
        // MSTATUS.MPRV are both 1
        if(!($2 && $3)) {
          u == false;
        }
      }
      // Set a,d bit to 1 avoid page/access fault exceptions
      a == true;
      d == true;
      // Default: Readable, writable, executable page
      @soft xwr == $4;
      // Page is valid
      v == true;
    } (privileged_mode, privileged_mode_t.USER_MODE,
       cfg.mstatus_sum, cfg.mstatus_mprv, pte_permission_t.R_W_EXECUTE_PAGE);
    valid_link_pte = cast(riscv_page_table_entry!(MODE)) valid_leaf_pte.clone;
    valid_data_leaf_pte = cast (riscv_page_table_entry!(MODE)) valid_leaf_pte.clone;
    illegal_pte.turn_off_default_constraint();
    valid_link_pte.xwr = pte_permission_t.NEXT_LEVEL_PAGE;
    valid_link_pte.pack_entry();
    // Set data page to read/write, but not executable
    valid_data_leaf_pte.xwr = pte_permission_t.READ_WRITE_PAGE;
    valid_data_leaf_pte.pack_entry();
  }

  void inject_page_table_exception(riscv_page_table_entry!(MODE) pte, int level) {
    exception_cfg.randomize();
    illegal_pte.randomize_with! q{ xwr !inside [$0, $1]; } (pte_permission_t.NEXT_LEVEL_PAGE,
							    pte_permission_t.R_W_EXECUTE_PAGE);
    // `DV_CHECK_RANDOMIZE_FATAL(exception_cfg)
    // `DV_CHECK_RANDOMIZE_WITH_FATAL(illegal_pte,
    //  !(xwr inside {NEXT_LEVEL_PAGE, R_W_EXECUTE_PAGE});)
    // Wrong privilege mode setting
    if (exception_cfg.allow_privileged_mode_exception) {
      pte.u = ! pte.u;
    }
    // Random access control
    // The link PTE is unchanged to avoid changing page table mappings
    if (exception_cfg.allow_page_access_control_exception &&
	(pte.xwr != pte_permission_t.NEXT_LEVEL_PAGE)) {
      pte.xwr = illegal_pte.xwr;
    }
    // Invalid page exception
    if (exception_cfg.allow_invalid_page_exception) {
      pte.v = 0;
    }
    // Set "access" bit to zero
    if (exception_cfg.allow_zero_access_bit_exception) {
      pte.a = 0;
    }
    // Set "dirty" bit to zero
    if (exception_cfg.allow_zero_dirty_bit_exception) {
      pte.d = 0;
    }
    // Unaligned super leaf PTE
    if (exception_cfg.allow_superpage_misaligned_exception &&
        (level > 0) && (pte.xwr != pte_permission_t.NEXT_LEVEL_PAGE)) {
      ubvec!(riscv_page_table_entry!(MODE).VPN_WIDTH) fault_ppn;
      fault_ppn.randomize();
      // `DV_CHECK_STD_RANDOMIZE_FATAL(fault_ppn)
      if (level == 3) {
        pte.ppn2.assign(fault_ppn);
      }
      else if (level == 2) {
        pte.ppn1 = fault_ppn;
      }
      else {
        pte.ppn0 = fault_ppn;
      }
    }
    // Illegal link PTE for the lowest level page table
    if (exception_cfg.allow_leaf_link_page_exception && (level == 0)) {
      pte.xwr = pte_permission_t.NEXT_LEVEL_PAGE;
    }
  }

  // Page fault handling routine
  // There are two types of page fault handling routine.
  // 1. For page table error injection test, fix all PTE related to the virtual address by walking
  //    through the page table with the fault address.
  // 2. For normal test, a page table fault typically means the program is accessing a large
  //    virtual address which currently not mapped a valid physical address. Need to do a
  //    memcpy to move data from lower physical address to the place the virtual address map to.
  // TODO: Refactor this part with new reserved GPR
  void gen_page_fault_handling_routine(ref string[] instr) {
    uint   level;
    string load_store_unit;
    ubvec!XLEN bit_mask = 1;

    if (MODE == satp_mode_t.SV48) {
      load_store_unit = "d";
      level = 3;
      bit_mask = bit_mask >> (riscv_page_table_entry!(MODE).RSVD_WIDTH +
                              riscv_page_table_entry!(MODE).PPN3_WIDTH);
    }
    else if (MODE == satp_mode_t.SV39) {
      load_store_unit = "d";
      level = 2;
      bit_mask = bit_mask >> (riscv_page_table_entry!(MODE).RSVD_WIDTH +
                              riscv_page_table_entry!(MODE).PPN2_WIDTH);
    }
    else if (MODE == satp_mode_t.SV32) {
      load_store_unit = "w";
      level = 1;
      bit_mask = bit_mask >> (riscv_page_table_entry!(MODE).PPN1_WIDTH);
    }
    else {
      uvm_fatal(get_full_name(), "Unsupported MODE");
    }

    if (cfg.mstatus_mprv && (SATP_MODE != satp_mode_t.BARE)) {
      // Check if mstatus.mpp equals to machine mode(0x11)
      // If MPP != Machine_mode and MSTATUS.MPRV = 1, load/store address translation is the same as
      // the mode indicated by MPP
      instr ~= format("csrr x%0d, 0x%0x // MSTATUS", mpp_reg, privileged_reg_t.MSTATUS);
      instr ~= format("srli x%0d, x%0d, 11", mpp_reg, mpp_reg);
      instr ~= format("andi x%0d, x%0d, 0x3", mpp_reg, mpp_reg);
      instr ~= format("xori x%0d, x%0d, 0x3", mpp_reg, mpp_reg);
    }

    // Flush TLB to force synchronization
    instr ~= "sfence.vma x0, x0";

    // Start from root level, top-down fix all related PTEs
    instr ~= format("li x%0d, %0d", level_reg, level);
    instr ~= format("li x%0d, 0x%0x", mask_reg, bit_mask);
    // Get the address that causes the page fault
    instr ~= format("csrr x%0d, 0x%0x # MTVAL", fault_vaddr_reg, privileged_reg_t.MTVAL);
    // Remove lower 4KB offset
    instr ~= format("srli x%0d, x%0d, 12", fault_vaddr_reg, fault_vaddr_reg);
    // Remove the virtual address spare bits, align the VPN to the msb
    instr ~= format("slli x%0d, x%0d, %0d", fault_vaddr_reg, fault_vaddr_reg,
		    riscv_page_table_entry!(MODE).VADDR_SPARE + 12);

    // Starting from the root table
    instr ~= format("la x%0d, page_table_0", pte_addr_reg);

    instr ~= "fix_pte:";
    // Get the VPN of the current level
    // Note the VPN under process is on the msb, right shift XLEN - VPN_WIDTH to get the VPN value
    instr ~= format("srli x%0d, x%0d, %0d",
		    tmp_reg, fault_vaddr_reg,
		    XLEN - riscv_page_table_entry!(MODE).VPN_WIDTH);
    // Get the actual address offset within the page table
    instr ~= format("slli x%0d, x%0d, %0d",
		    tmp_reg, tmp_reg, clog2(XLEN/8));
    // Add page table starting address and PTE offset to get PTE physical address
    instr ~= format("add x%0d, x%0d, x%0d",
		    pte_addr_reg, pte_addr_reg, tmp_reg);
    // Load the PTE from the memory
    instr ~= format("l%0s x%0d, 0(x%0d)",
		    load_store_unit, pte_reg, pte_addr_reg);
    // Check if the it's a link PTE (PTE[4:1] == 0)
    instr ~= format("slli x%0d, x%0d, %0d",
		    tmp_reg, pte_reg, XLEN - 4);
    instr ~= format("srli x%0d, x%0d, %0d",
		    tmp_reg, tmp_reg, XLEN - 3);
    instr ~= format("bne zero, x%0d, fix_leaf_pte", tmp_reg);

    // Handle link PTE exceptions
    // - If level == 0, change the link PTE to leaf PTE, and finish exception handling
    instr ~= format("beq zero, x%0d, fix_leaf_pte", level_reg);
    // - If level != 0, fix the link PTE, and move to the PTE it points to
    //   - Override the low 10 bits with the correct link PTE setting
    instr ~= format("srli x%0d, x%0d, 10", pte_reg, pte_reg);
    instr ~= format("slli x%0d, x%0d, 10", pte_reg, pte_reg);
    instr ~= format("li x%0d, 0x%0x", tmp_reg, valid_link_pte.bits);
    instr ~= format("or x%0d, x%0d, x%0d", pte_reg, pte_reg, tmp_reg);
    instr ~= format("s%0s x%0d, 0(x%0d)", load_store_unit, pte_reg, pte_addr_reg);
    //   - Zero out 10 lower access control bits
    instr ~= format("srli x%0d, x%0d, 10", pte_addr_reg, pte_reg);
    //   - Left shift 12 bits to create the physical address
    instr ~= format("slli x%0d, x%0d, 12", pte_addr_reg, pte_addr_reg);
    //   - Remove the VPN of the current level
    instr ~= format("slli x%0d, x%0d, %0d", fault_vaddr_reg, fault_vaddr_reg,
		    riscv_page_table_entry!(MODE).VPN_WIDTH);
    //   - Decrement the level, update the bit mask
    instr ~= format("addi x%0d, x%0d, -1", level_reg, level_reg);
    instr ~= format("srli x%0d, x%0d, %0d",
		    mask_reg, mask_reg, riscv_page_table_entry!(MODE).VPN_WIDTH);
    //   - Jump to fix the PTE of the next level
    instr ~= "j fix_pte";

    // fix_leaf_pte: Override the low 10 bits with the correct leaf PTE setting
    instr ~= "fix_leaf_pte:";
    // Use mask to zero out lower 10 bits and unaligned VPN
    instr ~= format("not x%0d, x%0d", mask_reg, mask_reg);
    instr ~= format("and x%0d, x%0d, x%0d", pte_reg, pte_reg, mask_reg);
    instr ~= format("li x%0d, 0x%0x", tmp_reg, valid_leaf_pte.bits);
    instr ~= format("or x%0d, x%0d, x%0d", pte_reg, pte_reg, tmp_reg);
    instr ~= format("s%0s x%0d, 0(x%0d)", load_store_unit, pte_reg, pte_addr_reg);
    instr ~= "j fix_kernel_leaf_pte";

    // Fix kernel leaf PTE
    instr ~= "fix_kernel_leaf_pte:";
    // - Load the starting virtual address of the kernel space
    instr ~= format("la x%0d, kernel_instr_start", tmp_reg);
    // TODO: Fix kernel instruction/data pages separatedly
    instr ~= format("slli x%0d, x%0d, %0d", tmp_reg, tmp_reg,
		    XLEN - MAX_USED_VADDR_BITS);
    instr ~= format("srli x%0d, x%0d, %0d", tmp_reg, tmp_reg,
		    XLEN - MAX_USED_VADDR_BITS);
    instr ~= format("csrr x%0d, 0x%0x # MTVAL", fault_vaddr_reg, privileged_reg_t.MTVAL);
    // - Check if the fault virtual address is in the kernel space
    instr ~= format("bgeu x%0d, x%0d, fix_pte_done", tmp_reg, fault_vaddr_reg);
    // - Set the PTE.u bit to 0 for kernel space PTE
    instr ~= format("li x%0d, 0x%0x", tmp_reg, 0x10); //`h10
    instr ~= format("not x%0d, x%0d", tmp_reg, tmp_reg);
    instr ~= format("and x%0d, x%0d, x%0d", pte_reg, tmp_reg, pte_reg);
    instr ~= format("s%0s x%0d, 0(x%0d)", load_store_unit, pte_reg, pte_addr_reg);

    // End of page table fault handling
    instr ~= "fix_pte_done:";
    // Make sure all outstanding memory access is completed
    instr ~= "sfence.vma";
    // Randomly decide if run some kernel program before exiting from exception handling
    // Use the low 2 bits of x30 to determine whether to skip it or not.
    instr ~= format("slli x30, x30, %0d", XLEN - 2);
    instr ~= "beqz x30, fix_pte_ret";
    // Randomly decide if set MPRV to 1
    instr ~= format("slli x31, x31, %0d", XLEN - 2);
    instr ~= "beqz x30, check_mprv";
    instr ~= format("csrr x%0d, 0x%0x", tmp_reg, privileged_reg_t.MSTATUS);
    instr ~= format("li x%0d, 0x%0x", mask_reg, MPRV_BIT_MASK);
    instr ~= format("not x%0d, x%0d", mask_reg, mask_reg);
    instr ~= format("or x%0d, x%0d, 0x%0x", tmp_reg, tmp_reg, mask_reg);
    instr ~= format("csrrw x%0d, 0x%0x, x%0d", tmp_reg, privileged_reg_t.MSTATUS, tmp_reg);
    // Run some kernel mode program before returning from exception handling
    // If MPRV = 0, jump to regular kernel mode program
    // If MPRV = 1, jump to kernel program with U mode mem load/store
    instr ~= format("check_mprv: li x%0d, 0x%0x", mask_reg, MPRV_BIT_MASK);
    instr ~= format("csrr x%0d, 0x%0x", tmp_reg, privileged_reg_t.MSTATUS);
    instr ~= format("and x%0d, x%0d, x%0d", tmp_reg, tmp_reg, mask_reg);
    instr ~= format("beqz x%0d, j_smode", tmp_reg);
    instr ~= "jal ra, smode_lsu_program";
    instr ~= "j fix_pte_ret";
    instr ~= "j_smode: jal ra, smode_program";
    instr ~= "fix_pte_ret:";
    // Recover the user mode GPR from kernal stack
    pop_gpr_from_kernel_stack(privileged_reg_t.MSTATUS, privileged_reg_t.MSCRATCH,
			      cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr ~= "mret";

    foreach (ref s; instr) {
      import std.uni: toLower;
      s = s.toLower();
    }

  }

  void default_page_table_setting() {
    num_of_page_table.length = PageLevel;
    foreach(i, num; num_of_page_table) {
      num = cast(int) (LinkPtePerTable ^^ (PageLevel - i - 1));
    }
  }

  void create_page_table_list() {
    import std.algorithm.iteration: sum;
    page_table.length = sum(num_of_page_table);
    foreach(i, ref page; page_table) {
      page = riscv_page_table!(MODE).type_id.create(format("page_table_%0d", cast(uint) i));
      page.init_page_table(PteCnt);
      page.table_id = cast(uint) i;
      page.level.assign(get_level(cast(uint) i));
    }
  }

  int get_1st_4k_table_id() {
    foreach (i, page; page_table) {
      if (page.level == 0) { return cast(int) i; }
    }
    return -1;
  }

  // Link page table
  void process_page_table(out string[] instr) {
    string load_store_unit;
    int pte_addr_offset;
    ubvec!XLEN ubit_mask = 1;
    ubit_mask[4] = 0; // U bit of PTE
    load_store_unit = (XLEN == 32) ? "w" : "d";
    // Assign the PPN of link PTE to link the page tables together
    foreach (i, ptbl; page_table) {
      if (ptbl.level == 0) break;
      instr ~=  format("la x%0d, page_table_%0d+2048 # Process PT_%0d",
		       cfg.gpr[1], i, i);
      foreach (j, entry; ptbl.pte) {
	if(j >= SuperLeafPtePerTable) continue;
	pte_addr_offset = cast(uint) ((j * PteSize) - 2048);
	uvm_info(get_full_name(), format("Processing PT_%0d_PTE_%0d, v = %0d, level = %0d",
					 i, j, entry.v, ptbl.level), UVM_LOW);
	if (entry.xwr == pte_permission_t.NEXT_LEVEL_PAGE)
	  {  instr ~=
	      format("l%0s x%0d, %0d(x%0d)",
		     load_store_unit, cfg.gpr[2], pte_addr_offset, cfg.gpr[1])
	      // Load the target page table physical address, PPN should be 0
	      ~ format("la x%0d, page_table_%0d # Link PT_%0d_PTE_%0d -> PT_%0d", cfg.gpr[0],
		       get_child_table_id(cast(int) i, cast(int) j), cast(int) i, cast(int) j,
		       get_child_table_id(cast(int) i, cast(int) j))
	      // Right shift the address for 2 bits to the correct PPN position in PTE
	      ~ format("srli x%0d, x%0d, 2", cfg.gpr[0], cfg.gpr[0])
	      // Assign PPN
	      ~  format("or x%0d, x%0d, x%0d", cfg.gpr[2], cfg.gpr[0], cfg.gpr[2])
	      // Store the new PTE value
	      ~  format("s%0s x%0d, %0d(x%0d)",
			load_store_unit, cfg.gpr[2], pte_addr_offset, cfg.gpr[1]);
	  }
      }
    }
    // ---------------------------------------------------------------------------
    // Set the kernel page u bit to 0 for supervisor mode instruction/data pages
    // ---------------------------------------------------------------------------
    if (cfg.support_supervisor_mode) {
      instr ~=
	// Process kernel instruction pages
	format("la x%0d, kernel_instr_start", cfg.gpr[0])
	~ format("la x%0d, kernel_instr_end", cfg.gpr[1])
	// Get the VPN of the physical address
	~ format("slli x%0d, x%0d, %0d",
		 cfg.gpr[0], cfg.gpr[0], XLEN - MAX_USED_VADDR_BITS)
	~ format("srli x%0d, x%0d, %0d",
		 cfg.gpr[0], cfg.gpr[0], XLEN - MAX_USED_VADDR_BITS + 12)
	~ format("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], clog2(XLEN))
	~ format("slli x%0d, x%0d, %0d", cfg.gpr[1], cfg.gpr[1],
		 XLEN - MAX_USED_VADDR_BITS)
	~ format("srli x%0d, x%0d, %0d", cfg.gpr[1], cfg.gpr[1],
		 XLEN - MAX_USED_VADDR_BITS + 12)
	~ format("slli x%0d, x%0d, %0d", cfg.gpr[1], cfg.gpr[1], clog2(XLEN))
	// Starting from the first 4KB leaf page table
	~ format("la x%0d, page_table_%0d", cfg.gpr[2], get_1st_4k_table_id())
	~ format("add x%0d, x%0d, x%0d", cfg.gpr[0], cfg.gpr[2], cfg.gpr[0])
	~ format("add x%0d, x%0d, x%0d", cfg.gpr[1], cfg.gpr[2], cfg.gpr[1])
	~ format("li x%0d, 0x%0x", cfg.gpr[2], ubit_mask)
	~ "1:"
	// Load the PTE from the memory
	~ format("l%0s x%0d, 0(x%0d)", load_store_unit, cfg.gpr[3], cfg.gpr[0])
	// Unset U bit
	~ format("and x%0d, x%0d, x%0d", cfg.gpr[3], cfg.gpr[3], cfg.gpr[2])
	// Save PTE back to memory
	~ format("s%0s x%0d, 0(x%0d)", load_store_unit, cfg.gpr[3], cfg.gpr[0])
	// Move to the next PTE
	~ format("addi x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN/8)
	// If not the end of the kernel space, process the next PTE
	~ format("ble x%0d, x%0d, 1b", cfg.gpr[0], cfg.gpr[1])
	// Process kernel data pages
	~ format("la x%0d, kernel_data_start", cfg.gpr[0])
	// Get the VPN of the physical address
	~ format("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0],
		 XLEN - MAX_USED_VADDR_BITS)
	~ format("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0],
		 XLEN - MAX_USED_VADDR_BITS + 12)
	~ format("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], clog2(XLEN))
	// Starting from the first 4KB leaf page table
	~ format("la x%0d, page_table_%0d", cfg.gpr[2], get_1st_4k_table_id())
	~ format("add x%0d, x%0d, x%0d", cfg.gpr[0], cfg.gpr[2], cfg.gpr[0])
	~ format("li x%0d, 0x%0x", cfg.gpr[2], ubit_mask)
	// Assume 20 PTEs for kernel data pages
	~ format("addi x%0d, x%0d, %0d", cfg.gpr[1], cfg.gpr[1], 20 * XLEN/8)
	~ "2:"
	// Load the PTE from the memory
	~ format("l%0s x%0d, 0(x%0d)", load_store_unit, cfg.gpr[3], cfg.gpr[0])
	// Unset U bit
	~ format("and x%0d, x%0d, x%0d", cfg.gpr[3], cfg.gpr[3], cfg.gpr[2])
	// Save PTE back to memory
	~ format("s%0s x%0d, 0(x%0d)", load_store_unit, cfg.gpr[3], cfg.gpr[0])
	// Move to the next PTE
	~ format("addi x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN/8)
	// If not the end of the kernel space, process the next PTE
	~ format("ble x%0d, x%0d, 2b", cfg.gpr[0], cfg.gpr[1]);
    }
    instr ~= "sfence.vma";
  }

  // If you want to create custom page table topology, override the below tasks to specify the
  // level and parent of each table.
  int get_level(int table_id) {
    for (int level = PageLevel - 1; level >= 0; level--) {
      if (table_id < num_of_page_table[level])
	return level;
      table_id -= num_of_page_table[level];
    }
    assert (false);
  }

  int get_child_table_id(int table_id, int pte_id) {
    return (table_id * LinkPtePerTable + pte_id + 1);
  }
}
