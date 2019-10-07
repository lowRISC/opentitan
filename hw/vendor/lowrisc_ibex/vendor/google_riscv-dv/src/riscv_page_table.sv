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

// RISC-V page table class
// This class is defined based on RISC-V privileged spec 1.10, three page table structure is
// supported: SV32, SV39, SV48
// This class is used by riscv_page_table_list to generate all page tables the program
class riscv_page_table#(satp_mode_t MODE = SV39) extends uvm_object;

  int unsigned                        num_of_pte;    // Number of page table entry
  int unsigned                        table_id;      // Page table ID
  bit [1:0]                           level;         // Page table level
  bit [XLEN-1:0]                      pte_binary[];  // Page table entry in binary format
  rand riscv_page_table_entry#(MODE)  pte[];         // List of all page table entries

  `uvm_object_param_utils(riscv_page_table#(MODE))
  `uvm_object_new

  // Init page table
  function void init_page_table(int unsigned num_of_pte = 1);
    this.num_of_pte = num_of_pte;
    pte = new[num_of_pte];
    pte_binary = new[num_of_pte];
  endfunction

  // Generate the page table binary
  function void gen_page_table_binary();
    foreach(pte[i]) begin
      pte_binary[i] = pte[i].bits;
    end
  endfunction

  // Generate the page table section in the output assembly program
  // Basically it's like a data section with all PTE binaries.
  function void gen_page_table_section(output string instr[$]);
    string str;
    this.gen_page_table_binary();
    // Align the page table to 4K boundary
    instr = {instr,
             ".align 12",
             $sformatf("%0s:", get_name())};
    foreach(pte_binary[i]) begin
      if (i % 8 == 0) begin
        if (XLEN == 64) begin
          str = $sformatf(".dword 0x%0x", pte_binary[i]);
        end else begin
          str = $sformatf(".word 0x%0x", pte_binary[i]);
        end
      end else begin
        str = {str, $sformatf(", 0x%0x", pte_binary[i])};
      end
      if (((i + 1) % 8 == 0) || (i == pte_binary.size() - 1)) begin
        instr.push_back(str);
      end
    end
  endfunction

endclass
