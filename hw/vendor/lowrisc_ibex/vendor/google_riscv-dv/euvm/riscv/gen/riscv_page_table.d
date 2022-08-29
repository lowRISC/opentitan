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

// RISC-V page table class
// This class is defined based on RISC-V privileged spec 1.10, three page table structure is
// supported: SV32, SV39, SV48
// This class is used by riscv_page_table_list to generate all page tables the program

module riscv.gen.riscv_page_table;

import riscv.gen.riscv_instr_pkg: satp_mode_t;
import riscv.gen.riscv_page_table_entry: riscv_page_table_entry;
import riscv.gen.target: XLEN;
import std.string: format;
import esdl.data.bvec: ubvec;
import esdl.rand: rand;
import uvm;

version(CHECK_COMPILE) alias riscv_page_table_SV39 = riscv_page_table!(satp_mode_t.SV39);

class riscv_page_table(satp_mode_t MODE): uvm_object
{
  uint                        num_of_pte;    // Number of page table entry
  uint                        table_id;      // Page table ID
  ubvec!2                     level;         // Page table level
  ubvec!XLEN []               pte_binary;    // Page table entry in binary format
  @rand riscv_page_table_entry!(MODE)[] pte;         // List of all page table//  entries

  mixin uvm_object_utils;

  this(string name = "") {
    super(name);
  }

  // `uvm_object_param_utils(riscv_page_table#(MODE))
  // `uvm_object_new

  // Init page table
  void init_page_table(uint num_of_pte = 1) {
    this.num_of_pte = num_of_pte;
    pte.length = num_of_pte;
    pte_binary.length = num_of_pte;
  }

  // Generate the page table binary
  void gen_page_table_binary() {
    foreach (i, p; pte) {
      pte_binary[i] = p.bits;
    }
  }

  // Generate the page table section in the output assembly program
  // Basically it's like a data section with all PTE binaries.
  void gen_page_table_section(out string [] instr) {
    string str;
    this.gen_page_table_binary();
    // Align the page table to 4K boundary
    instr = instr ~ ".align 12" ~ format("%0s:", get_name());
    foreach (i, pte; pte_binary) {
      if (i % 8 == 0) {
	if (XLEN == 64) {
	  str = format(".dword 0x%0x", pte);
	}
	else {
	  str = format(".word 0x%0x", pte);
	}
      }
      else {
	str = str ~ format(", 0x%0x", pte);
      }
      if (((i + 1) % 8 == 0) || (i == pte_binary.length - 1)) {
	instr ~= str;
      }
    }
  }

}
