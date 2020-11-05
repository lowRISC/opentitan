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

class riscv_page_table_list#(satp_mode_t MODE = SV39) extends uvm_object;

  localparam int PteSize   = XLEN / 8;
  localparam int PteCnt    = 4096 / PteSize;
  localparam int PageLevel = (MODE == SV32) ? 2 : ((MODE == SV39) ? 3 : 4);
  localparam int LinkPtePerTable = 2;
  localparam int SuperLeafPtePerTable = 2;

  satp_mode_t mode = MODE;

  // Privileged mode of the program
  privileged_mode_t privileged_mode = USER_MODE;

  // Starting physical address of the program.
  bit [XLEN-1:0] start_pa = 'h8000_0000;

  // Num of page table per level
  int unsigned num_of_page_table[];

  // Page table list, from highest level to the lowest level
  riscv_page_table#(MODE) page_table[];

  // Root page table PTE idx for the init code entry
  int unsigned root_init_pte_idx;

  // Instruction generator configuration
  riscv_instr_gen_config cfg;

  // Allow exception or not
  bit enable_exception;
  riscv_page_table_exception_cfg exception_cfg;

  // Valid PTE entry for exception recovery
  riscv_page_table_entry#(MODE) valid_leaf_pte;
  riscv_page_table_entry#(MODE) valid_link_pte;
  riscv_page_table_entry#(MODE) valid_data_leaf_pte;
  riscv_page_table_entry#(MODE) illegal_pte;

  // Registers used for page table exception handling
  rand riscv_reg_t level_reg;
  rand riscv_reg_t fault_vaddr_reg;
  rand riscv_reg_t pte_addr_reg;
  rand riscv_reg_t pte_reg;
  rand riscv_reg_t tmp_reg;
  rand riscv_reg_t mask_reg;
  rand riscv_reg_t mpp_reg;

  constraint page_table_exception_handling_reg_c {
    unique {level_reg, fault_vaddr_reg, pte_addr_reg,
            pte_reg, tmp_reg, mask_reg, mpp_reg};
    !(level_reg inside {cfg.reserved_regs, ZERO});
    !(fault_vaddr_reg inside {cfg.reserved_regs, ZERO});
    !(pte_addr_reg inside {cfg.reserved_regs, ZERO});
    !(pte_reg inside {cfg.reserved_regs, ZERO});
    !(mask_reg inside {cfg.reserved_regs, ZERO});
    !(mpp_reg inside {cfg.reserved_regs, ZERO});
    !(tmp_reg inside {cfg.reserved_regs, ZERO});
  }

  `uvm_object_param_utils(riscv_page_table_list#(MODE))

  function new(string name = "");
    super.new(name);
    default_page_table_setting();
    exception_cfg = riscv_page_table_exception_cfg::type_id::create("exception_cfg");
    valid_leaf_pte = riscv_page_table_entry#(MODE)::type_id::create("valid_leaf_pte");
    valid_link_pte = riscv_page_table_entry#(MODE)::type_id::create("valid_link_pte");
    valid_data_leaf_pte = riscv_page_table_entry#(MODE)::type_id::create("valid_data_leaf_pte");
    illegal_pte = riscv_page_table_entry#(MODE)::type_id::create("illegal_pte");
  endfunction

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
  virtual function void randomize_page_table();
    int pte_index;
    exception_cfg.enable_exception = enable_exception;
    create_valid_pte();
    foreach(page_table[i]) begin
      `uvm_info(`gfn, $sformatf("Randomizing page table %0d, num of PTE: %0d",
                      i, page_table[i].pte.size()), UVM_LOW)
      if(i == 0) begin
        pte_index = 0;
      end else if(page_table[i].level != page_table[i-1].level) begin
        pte_index = 0;
      end
      foreach(page_table[i].pte[j]) begin
        if(page_table[i].level > 0) begin
          // Superpage
          if (j < LinkPtePerTable) begin
            // First few super pages are link PTE to the next level
            $cast(page_table[i].pte[j], valid_link_pte.clone());
          end else if (j < SuperLeafPtePerTable + LinkPtePerTable) begin
            // Non-link superpage table entry
            $cast(page_table[i].pte[j], valid_leaf_pte.clone());
          end else begin
            // Invalid unused PTEs
            page_table[i].pte[j] = riscv_page_table_entry#(MODE)::type_id::
                                   create($sformatf("pte_%0d_%0d",i, j));
            page_table[i].pte[j].v = 1'b0;
          end
        end else begin
          // Lowest level leaf pages
         $cast(page_table[i].pte[j], valid_leaf_pte.clone());
        end
        if(page_table[i].pte[j].xwr != NEXT_LEVEL_PAGE) begin
          page_table[i].pte[j].set_ppn(start_pa, pte_index, page_table[i].level);
        end
        pte_index++;
        if(enable_exception) begin
          inject_page_table_exception(page_table[i].pte[j], page_table[i].level);
        end
        page_table[i].pte[j].pack_entry();
        `uvm_info(`gfn, $sformatf("%0s PT_%0d_%0d: %0s", privileged_mode.name(),
                        i, j, page_table[i].pte[j].convert2string()), UVM_HIGH)
      end
    end
  endfunction

  // Create the basic legal page table entries
  virtual function void create_valid_pte();
    // Randomize a valid leaf PTE entry
    `DV_CHECK_RANDOMIZE_WITH_FATAL(valid_leaf_pte,
      // Set the correct privileged mode
      if(privileged_mode == USER_MODE) {
        u == 1'b1;
      } else {
        // Accessing user mode page from supervisor mode is only allowed when MSTATUS.SUM and
        // MSTATUS.MPRV are both 1
        if(!(cfg.mstatus_sum && cfg.mstatus_mprv)) {
          u == 1'b0;
        }
      }
      // Set a,d bit to 1 avoid page/access fault exceptions
      a == 1'b1;
      d == 1'b1;
      // Default: Readable, writable, executable page
      soft xwr == R_W_EXECUTE_PAGE;
      // Page is valid
      v == 1'b1;
    )
    $cast(valid_link_pte, valid_leaf_pte.clone());
    $cast(valid_data_leaf_pte, valid_leaf_pte.clone());
    illegal_pte.turn_off_default_constraint();
    valid_link_pte.xwr = NEXT_LEVEL_PAGE;
    valid_link_pte.pack_entry();
    // Set data page to read/write, but not executable
    valid_data_leaf_pte.xwr = READ_WRITE_PAGE;
    valid_data_leaf_pte.pack_entry();
  endfunction

  virtual function void inject_page_table_exception(riscv_page_table_entry#(MODE) pte, int level);
    `DV_CHECK_RANDOMIZE_FATAL(exception_cfg)
    `DV_CHECK_RANDOMIZE_WITH_FATAL(illegal_pte,
                                   !(xwr inside {NEXT_LEVEL_PAGE, R_W_EXECUTE_PAGE});)
    // Wrong privilege mode setting
    if(exception_cfg.allow_privileged_mode_exception) begin
      pte.u = ~pte.u;
    end
    // Random access control
    // The link PTE is unchanged to avoid changing page table mappings
    if(exception_cfg.allow_page_access_control_exception &&
       (pte.xwr != NEXT_LEVEL_PAGE)) begin
      pte.xwr = illegal_pte.xwr;
    end
    // Invalid page exception
    if(exception_cfg.allow_invalid_page_exception) begin
      pte.v = 0;
    end
    // Set "access" bit to zero
    if(exception_cfg.allow_zero_access_bit_exception) begin
      pte.a = 0;
    end
    // Set "dirty" bit to zero
    if(exception_cfg.allow_zero_dirty_bit_exception) begin
      pte.d = 0;
    end
    // Unaligned super leaf PTE
    if(exception_cfg.allow_superpage_misaligned_exception &&
       (level > 0) && (pte.xwr != NEXT_LEVEL_PAGE)) begin
      bit [riscv_page_table_entry#(MODE)::VPN_WIDTH-1:0] fault_ppn;
      `DV_CHECK_STD_RANDOMIZE_FATAL(fault_ppn)
      if(level == 3) begin
        pte.ppn2 = fault_ppn;
      end else if (level == 2) begin
        pte.ppn1 = fault_ppn;
      end else begin
        pte.ppn0 = fault_ppn;
      end
    end
    // Illegal link PTE for the lowest level page table
    if(exception_cfg.allow_leaf_link_page_exception && (level == 0)) begin
      pte.xwr = NEXT_LEVEL_PAGE;
    end
  endfunction

  // Page fault handling routine
  // There are two types of page fault handling routine.
  // 1. For page table error injection test, fix all PTE related to the virtual address by walking
  //    through the page table with the fault address.
  // 2. For normal test, a page table fault typically means the program is accessing a large
  //    virtual address which currently not mapped a valid physical address. Need to do a
  //    memcpy to move data from lower physical address to the place the virtual address map to.
  // TODO: Refactor this part with new reserved GPR
  virtual function void gen_page_fault_handling_routine(ref string instr[$]);
    int unsigned  level;
    string        load_store_unit;
    bit[XLEN-1:0] bit_mask = '1;

    if(MODE == SV48) begin
      load_store_unit = "d";
      level = 3;
      bit_mask = bit_mask >> (riscv_page_table_entry#(MODE)::RSVD_WIDTH +
                              riscv_page_table_entry#(MODE)::PPN3_WIDTH);
    end else if(MODE == SV39) begin
      load_store_unit = "d";
      level = 2;
      bit_mask = bit_mask >> (riscv_page_table_entry#(MODE)::RSVD_WIDTH +
                              riscv_page_table_entry#(MODE)::PPN2_WIDTH);
    end else if(MODE == SV32) begin
      load_store_unit = "w";
      level = 1;
      bit_mask = bit_mask >> (riscv_page_table_entry#(MODE)::PPN1_WIDTH);
    end else begin
      `uvm_fatal(`gfn, "Unsupported MODE")
    end

    if(cfg.mstatus_mprv && (SATP_MODE != BARE)) begin
      // Check if mstatus.mpp equals to machine mode(0x11)
      // If MPP != Machine_mode and MSTATUS.MPRV = 1, load/store address translation is the same as
      // the mode indicated by MPP
      instr.push_back($sformatf("csrr x%0d, 0x%0x // MSTATUS", mpp_reg, MSTATUS));
      instr.push_back($sformatf("srli x%0d, x%0d, 11", mpp_reg, mpp_reg));
      instr.push_back($sformatf("andi x%0d, x%0d, 0x3", mpp_reg, mpp_reg));
      instr.push_back($sformatf("xori x%0d, x%0d, 0x3", mpp_reg, mpp_reg));
    end

    // Flush TLB to force synchronization
    instr.push_back("sfence.vma x0, x0");

    // Start from root level, top-down fix all related PTEs
    instr.push_back($sformatf("li x%0d, %0d", level_reg, level));
    instr.push_back($sformatf("li x%0d, 0x%0x", mask_reg, bit_mask));
    // Get the address that causes the page fault
    instr.push_back($sformatf("csrr x%0d, 0x%0x # MTVAL", fault_vaddr_reg, MTVAL));
    // Remove lower 4KB offset
    instr.push_back($sformatf("srli x%0d, x%0d, 12", fault_vaddr_reg, fault_vaddr_reg));
    // Remove the virtual address spare bits, align the VPN to the msb
    instr.push_back($sformatf("slli x%0d, x%0d, %0d", fault_vaddr_reg, fault_vaddr_reg,
                    riscv_page_table_entry#(MODE)::VADDR_SPARE + 12));

    // Starting from the root table
    instr.push_back($sformatf("la x%0d, page_table_0", pte_addr_reg));

    instr.push_back("fix_pte:");
    // Get the VPN of the current level
    // Note the VPN under process is on the msb, right shift XLEN - VPN_WIDTH to get the VPN value
    instr.push_back($sformatf("srli x%0d, x%0d, %0d",
                    tmp_reg, fault_vaddr_reg,
                    XLEN - riscv_page_table_entry#(MODE)::VPN_WIDTH));
    // Get the actual address offset within the page table
    instr.push_back($sformatf("slli x%0d, x%0d, %0d",
                    tmp_reg, tmp_reg, $clog2(XLEN/8)));
    // Add page table starting address and PTE offset to get PTE physical address
    instr.push_back($sformatf("add x%0d, x%0d, x%0d",
                    pte_addr_reg, pte_addr_reg, tmp_reg));
    // Load the PTE from the memory
    instr.push_back($sformatf("l%0s x%0d, 0(x%0d)",
                    load_store_unit, pte_reg, pte_addr_reg));
    // Check if the it's a link PTE (PTE[4:1] == 0)
    instr.push_back($sformatf("slli x%0d, x%0d, %0d",
                    tmp_reg, pte_reg, XLEN - 4));
    instr.push_back($sformatf("srli x%0d, x%0d, %0d",
                    tmp_reg, tmp_reg, XLEN - 3));
    instr.push_back($sformatf("bne zero, x%0d, fix_leaf_pte", tmp_reg));

    // Handle link PTE exceptions
    // - If level == 0, change the link PTE to leaf PTE, and finish exception handling
    instr.push_back($sformatf("beq zero, x%0d, fix_leaf_pte", level_reg));
    // - If level != 0, fix the link PTE, and move to the PTE it points to
    //   - Override the low 10 bits with the correct link PTE setting
    instr.push_back($sformatf("srli x%0d, x%0d, 10", pte_reg, pte_reg));
    instr.push_back($sformatf("slli x%0d, x%0d, 10", pte_reg, pte_reg));
    instr.push_back($sformatf("li x%0d, 0x%0x", tmp_reg, valid_link_pte.bits));
    instr.push_back($sformatf("or x%0d, x%0d, x%0d", pte_reg, pte_reg, tmp_reg));
    instr.push_back($sformatf("s%0s x%0d, 0(x%0d)", load_store_unit, pte_reg, pte_addr_reg));
    //   - Zero out 10 lower access control bits
    instr.push_back($sformatf("srli x%0d, x%0d, 10", pte_addr_reg, pte_reg));
    //   - Left shift 12 bits to create the physical address
    instr.push_back($sformatf("slli x%0d, x%0d, 12", pte_addr_reg, pte_addr_reg));
    //   - Remove the VPN of the current level
    instr.push_back($sformatf("slli x%0d, x%0d, %0d", fault_vaddr_reg, fault_vaddr_reg,
                    riscv_page_table_entry#(MODE)::VPN_WIDTH));
    //   - Decrement the level, update the bit mask
    instr.push_back($sformatf("addi x%0d, x%0d, -1", level_reg, level_reg));
    instr.push_back($sformatf("srli x%0d, x%0d, %0d",
                    mask_reg, mask_reg, riscv_page_table_entry#(MODE)::VPN_WIDTH));
    //   - Jump to fix the PTE of the next level
    instr.push_back("j fix_pte");

    // fix_leaf_pte: Override the low 10 bits with the correct leaf PTE setting
    instr.push_back("fix_leaf_pte:");
    // Use mask to zero out lower 10 bits and unaligned VPN
    instr.push_back($sformatf("not x%0d, x%0d", mask_reg, mask_reg));
    instr.push_back($sformatf("and x%0d, x%0d, x%0d", pte_reg, pte_reg, mask_reg));
    instr.push_back($sformatf("li x%0d, 0x%0x", tmp_reg, valid_leaf_pte.bits));
    instr.push_back($sformatf("or x%0d, x%0d, x%0d", pte_reg, pte_reg, tmp_reg));
    instr.push_back($sformatf("s%0s x%0d, 0(x%0d)", load_store_unit, pte_reg, pte_addr_reg));
    instr.push_back("j fix_kernel_leaf_pte");

    // Fix kernel leaf PTE
    instr.push_back("fix_kernel_leaf_pte:");
    // - Load the starting virtual address of the kernel space
    instr.push_back($sformatf("la x%0d, kernel_instr_start", tmp_reg));
    // TODO: Fix kernel instruction/data pages separatedly
    instr.push_back($sformatf("slli x%0d, x%0d, %0d", tmp_reg, tmp_reg,
                    XLEN - MAX_USED_VADDR_BITS));
    instr.push_back($sformatf("srli x%0d, x%0d, %0d", tmp_reg, tmp_reg,
                    XLEN - MAX_USED_VADDR_BITS));
    instr.push_back($sformatf("csrr x%0d, 0x%0x # MTVAL", fault_vaddr_reg, MTVAL));
    // - Check if the fault virtual address is in the kernel space
    instr.push_back($sformatf("bgeu x%0d, x%0d, fix_pte_done", tmp_reg, fault_vaddr_reg));
    // - Set the PTE.u bit to 0 for kernel space PTE
    instr.push_back($sformatf("li x%0d, 0x%0x", tmp_reg, 'h10));
    instr.push_back($sformatf("not x%0d, x%0d", tmp_reg, tmp_reg));
    instr.push_back($sformatf("and x%0d, x%0d, x%0d", pte_reg, tmp_reg, pte_reg));
    instr.push_back($sformatf("s%0s x%0d, 0(x%0d)", load_store_unit, pte_reg, pte_addr_reg));

    // End of page table fault handling
    instr.push_back("fix_pte_done:");
    // Make sure all outstanding memory access is completed
    instr.push_back("sfence.vma");
    // Randomly decide if run some kernel program before exiting from exception handling
    // Use the low 2 bits of x30 to determine whether to skip it or not.
    instr.push_back($sformatf("slli x30, x30, %0d", XLEN - 2));
    instr.push_back("beqz x30, fix_pte_ret");
    // Randomly decide if set MPRV to 1
    instr.push_back($sformatf("slli x31, x31, %0d", XLEN - 2));
    instr.push_back("beqz x30, check_mprv");
    instr.push_back($sformatf("csrr x%0d, 0x%0x", tmp_reg, MSTATUS));
    instr.push_back($sformatf("li x%0d, 0x%0x", mask_reg, MPRV_BIT_MASK));
    instr.push_back($sformatf("not x%0d, x%0d", mask_reg, mask_reg));
    instr.push_back($sformatf("or x%0d, x%0d, 0x%0x", tmp_reg, tmp_reg, mask_reg));
    instr.push_back($sformatf("csrrw x%0d, 0x%0x, x%0d", tmp_reg, MSTATUS, tmp_reg));
    // Run some kernel mode program before returning from exception handling
    // If MPRV = 0, jump to regular kernel mode program
    // If MPRV = 1, jump to kernel program with U mode mem load/store
    instr.push_back($sformatf("check_mprv: li x%0d, 0x%0x", mask_reg, MPRV_BIT_MASK));
    instr.push_back($sformatf("csrr x%0d, 0x%0x", tmp_reg, MSTATUS));
    instr.push_back($sformatf("and x%0d, x%0d, x%0d", tmp_reg, tmp_reg, mask_reg));
    instr.push_back($sformatf("beqz x%0d, j_smode", tmp_reg));
    instr.push_back("jal ra, smode_lsu_program");
    instr.push_back("j fix_pte_ret");
    instr.push_back("j_smode: jal ra, smode_program");
    instr.push_back("fix_pte_ret:");
    // Recover the user mode GPR from kernal stack
    pop_gpr_from_kernel_stack(MSTATUS, MSCRATCH, cfg.mstatus_mprv, cfg.sp, cfg.tp, instr);
    instr.push_back("mret");

    foreach(instr[i]) begin
      instr[i] = instr[i].tolower();
    end

  endfunction

  virtual function void default_page_table_setting();
    num_of_page_table = new[PageLevel];
    foreach(num_of_page_table[i]) begin
      num_of_page_table[i] = LinkPtePerTable ** (PageLevel - i - 1);
    end
  endfunction

  virtual function void create_page_table_list();
    page_table = new[num_of_page_table.sum()];
    foreach(page_table[i]) begin
      page_table[i] = riscv_page_table#(MODE)::type_id::create($sformatf("page_table_%0d",i));
      page_table[i].init_page_table(PteCnt);
      page_table[i].table_id = i;
      page_table[i].level = get_level(i);
    end
  endfunction

  virtual function int get_1st_4k_table_id();
    foreach(page_table[i]) begin
      if(page_table[i].level == 0) return i;
    end
    return -1;
  endfunction

  // Link page table
  virtual function void process_page_table(output string instr[$]);
    string load_store_unit;
    int pte_addr_offset;
    bit [XLEN-1:0] ubit_mask = '1;
    ubit_mask[4] = 1'b0; // U bit of PTE
    load_store_unit = (XLEN == 32) ? "w" : "d";
    // Assign the PPN of link PTE to link the page tables together
    foreach(page_table[i]) begin
      if (page_table[i].level == 0) break;
      instr = {instr, $sformatf("la x%0d, page_table_%0d+2048 # Process PT_%0d",
                                cfg.gpr[1], i, i)};
      foreach(page_table[i].pte[j]) begin
        if(j >= SuperLeafPtePerTable) continue;
        pte_addr_offset = (j * PteSize) - 2048;
        `uvm_info(`gfn, $sformatf("Processing PT_%0d_PTE_%0d, v = %0d, level = %0d",
                        i, j, page_table[i].pte[j].v, page_table[i].level), UVM_LOW)
        if(page_table[i].pte[j].xwr == NEXT_LEVEL_PAGE) begin
          // Use the target table address as PPN of this PTE
          // x%0d holds the target table physical address
          instr = {instr,
                   // Load the current PTE value
                   $sformatf("l%0s x%0d, %0d(x%0d)",
                             load_store_unit, cfg.gpr[2], pte_addr_offset, cfg.gpr[1]),
                   // Load the target page table physical address, PPN should be 0
                   $sformatf("la x%0d, page_table_%0d # Link PT_%0d_PTE_%0d -> PT_%0d", cfg.gpr[0],
                             get_child_table_id(i, j), i, j, get_child_table_id(i, j)),
                   // Right shift the address for 2 bits to the correct PPN position in PTE
                   $sformatf("srli x%0d, x%0d, 2", cfg.gpr[0], cfg.gpr[0]),
                   // Assign PPN
                   $sformatf("or x%0d, x%0d, x%0d", cfg.gpr[2], cfg.gpr[0], cfg.gpr[2]),
                   // Store the new PTE value
                   $sformatf("s%0s x%0d, %0d(x%0d)",
                   load_store_unit, cfg.gpr[2], pte_addr_offset, cfg.gpr[1])};
        end
      end
    end
    // ---------------------------------------------------------------------------
    // Set the kernel page u bit to 0 for supervisor mode instruction/data pages
    // ---------------------------------------------------------------------------
    if (cfg.support_supervisor_mode) begin
      instr = {instr,
               // Process kernel instruction pages
               $sformatf("la x%0d, kernel_instr_start", cfg.gpr[0]),
               $sformatf("la x%0d, kernel_instr_end", cfg.gpr[1]),
               // Get the VPN of the physical address
               $sformatf("slli x%0d, x%0d, %0d",
                         cfg.gpr[0], cfg.gpr[0], XLEN - MAX_USED_VADDR_BITS),
               $sformatf("srli x%0d, x%0d, %0d",
                         cfg.gpr[0], cfg.gpr[0], XLEN - MAX_USED_VADDR_BITS + 12),
               $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], $clog2(XLEN)),
               $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[1], cfg.gpr[1],
                         XLEN - MAX_USED_VADDR_BITS),
               $sformatf("srli x%0d, x%0d, %0d", cfg.gpr[1], cfg.gpr[1],
                         XLEN - MAX_USED_VADDR_BITS + 12),
               $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[1], cfg.gpr[1], $clog2(XLEN)),
               // Starting from the first 4KB leaf page table
               $sformatf("la x%0d, page_table_%0d", cfg.gpr[2], get_1st_4k_table_id()),
               $sformatf("add x%0d, x%0d, x%0d", cfg.gpr[0], cfg.gpr[2], cfg.gpr[0]),
               $sformatf("add x%0d, x%0d, x%0d", cfg.gpr[1], cfg.gpr[2], cfg.gpr[1]),
               $sformatf("li x%0d, 0x%0x", cfg.gpr[2], ubit_mask),
               "1:",
               // Load the PTE from the memory
               $sformatf("l%0s x%0d, 0(x%0d)", load_store_unit, cfg.gpr[3], cfg.gpr[0]),
               // Unset U bit
               $sformatf("and x%0d, x%0d, x%0d", cfg.gpr[3], cfg.gpr[3], cfg.gpr[2]),
               // Save PTE back to memory
               $sformatf("s%0s x%0d, 0(x%0d)", load_store_unit, cfg.gpr[3], cfg.gpr[0]),
               // Move to the next PTE
               $sformatf("addi x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN/8),
               // If not the end of the kernel space, process the next PTE
               $sformatf("ble x%0d, x%0d, 1b", cfg.gpr[0], cfg.gpr[1]),
               // Process kernel data pages
               $sformatf("la x%0d, kernel_data_start", cfg.gpr[0]),
               // Get the VPN of the physical address
               $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0],
                         XLEN - MAX_USED_VADDR_BITS),
               $sformatf("srli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0],
                         XLEN - MAX_USED_VADDR_BITS + 12),
               $sformatf("slli x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], $clog2(XLEN)),
               // Starting from the first 4KB leaf page table
               $sformatf("la x%0d, page_table_%0d", cfg.gpr[2], get_1st_4k_table_id()),
               $sformatf("add x%0d, x%0d, x%0d", cfg.gpr[0], cfg.gpr[2], cfg.gpr[0]),
               $sformatf("li x%0d, 0x%0x", cfg.gpr[2], ubit_mask),
               // Assume 20 PTEs for kernel data pages
               $sformatf("addi x%0d, x%0d, %0d", cfg.gpr[1], cfg.gpr[1], 20 * XLEN/8),
               "2:",
               // Load the PTE from the memory
               $sformatf("l%0s x%0d, 0(x%0d)", load_store_unit, cfg.gpr[3], cfg.gpr[0]),
               // Unset U bit
               $sformatf("and x%0d, x%0d, x%0d", cfg.gpr[3], cfg.gpr[3], cfg.gpr[2]),
               // Save PTE back to memory
               $sformatf("s%0s x%0d, 0(x%0d)", load_store_unit, cfg.gpr[3], cfg.gpr[0]),
               // Move to the next PTE
               $sformatf("addi x%0d, x%0d, %0d", cfg.gpr[0], cfg.gpr[0], XLEN/8),
               // If not the end of the kernel space, process the next PTE
               $sformatf("ble x%0d, x%0d, 2b", cfg.gpr[0], cfg.gpr[1])};
    end
    instr = {instr, "sfence.vma"};
  endfunction

  // If you want to create custom page table topology, override the below tasks to specify the
  // level and parent of each table.
  virtual function int get_level(int table_id);
    for(int level = PageLevel - 1; level >= 0; level--) begin
      if(table_id < num_of_page_table[level]) return level;
      table_id -= num_of_page_table[level];
    end
  endfunction

  virtual function int get_child_table_id(int table_id, int pte_id);
    return table_id * LinkPtePerTable + pte_id + 1;
  endfunction

endclass
