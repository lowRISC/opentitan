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

//--------------------------------------------------------------------------------------------
// RISC-V Page Table Entry(PTE)
//
// Support SV32, SV39, SV48 PTE format defined in RISC-V privileged spec 1.10.
// -------------------------------------------------------------------------------------------

class riscv_page_table_entry#(satp_mode_t MODE = SV39) extends uvm_object;

  // Note that only SV32, SV39, SV48 are supported
  parameter int PPN0_WIDTH  = (MODE == SV32) ? 10 : 9;
  parameter int PPN1_WIDTH  = (MODE == SV32) ? 12 : 9;
  parameter int PPN2_WIDTH  = (MODE == SV39) ? 26 : ((MODE == SV48) ? 9 : 1);
  parameter int PPN3_WIDTH  = (MODE == SV48) ? 9  : 1;
  parameter int RSVD_WIDTH  = (MODE == SV32) ? 1  : 10;
  parameter int VPN_WIDTH   = (MODE == SV32) ? 10 : 9;
  // Spare bits in virtual address = XLEN - used virtual address bits
  parameter int VADDR_SPARE = (MODE == SV32) ? 0  : (MODE == SV39) ? 25 : 16;
  // Virtual address bit width
  parameter int VADDR_WIDTH = (MODE == SV32) ? 31 : (MODE == SV39) ? 38 : 48;

  rand bit                    v;     // PTE is valid
  rand pte_permission_t       xwr;   // PTE execute-write-read permission
  rand bit                    u;     // Accessible in User Mode
  rand bit                    g;     // Gloabal mapping
  rand bit                    a;     // Accessed flag
  rand bit                    d;     // Dirty flag
  rand bit [1:0]              rsw;   // Reserved for future use
  rand bit [PPN0_WIDTH-1:0]   ppn0;
  rand bit [PPN1_WIDTH-1:0]   ppn1;
  rand bit [PPN2_WIDTH-1:0]   ppn2;
  rand bit [PPN3_WIDTH-1:0]   ppn3;
  rand bit [XLEN-1:0]         bits;
  rand bit [RSVD_WIDTH-1:0]   rsvd;
  int                         child_table_id;
  bit      [XLEN-1:0]         starting_pa; // Starting physical address
  bit      [XLEN-1:0]         starting_va; // Starting virtual address offset

  // This two bits are implementation specific, set them to 1 to avoid mismatching
  constraint access_dirty_bit_c {
    soft a    == 1'b1;
    soft d    == 1'b1;
  }

  // Set reserved fields to 0
  constraint reserved_bits_c {
    soft rsw  == '0;
    soft rsvd == '0;
  }

  // PPN is assigned in the post-process
  constraint ppn_zero_c {
    soft ppn0 == '0;
    soft ppn1 == '0;
    soft ppn2 == '0;
    soft ppn3 == '0;
  }

  constraint sw_legal_c {
    // If the PTE is not a leaf page, U,A,D must be cleared by SW for future compatibility
    if(xwr == NEXT_LEVEL_PAGE) {
      u == 1'b0;
      a == 1'b0;
      d == 1'b0;
    }
  }

  `uvm_object_param_utils(riscv_page_table_entry#(MODE))
  `uvm_object_new

  virtual function void turn_off_default_constraint();
    access_dirty_bit_c.constraint_mode(0);
    reserved_bits_c.constraint_mode(0);
    ppn_zero_c.constraint_mode(0);
    sw_legal_c.constraint_mode(0);
  endfunction

  function void post_randomize();
    pack_entry();
  endfunction

  virtual function void do_copy(uvm_object rhs);
    riscv_page_table_entry#(MODE) rhs_;
    super.do_copy(rhs);
    `DV_CHECK_FATAL($cast(rhs_, rhs), "Cast to page_table_entry failed!")
    this.v = rhs_.v;
    this.xwr = rhs_.xwr;
    this.u = rhs_.u;
    this.g = rhs_.g;
    this.a = rhs_.a;
    this.d = rhs_.d;
    this.rsw = rhs_.rsw;
    this.ppn0 = rhs_.ppn0;
    this.ppn1 = rhs_.ppn1;
    this.ppn2 = rhs_.ppn2;
    this.ppn3 = rhs_.ppn3;
    this.bits = rhs_.bits;
    this.rsvd = rhs_.rsvd;
    this.starting_pa = rhs_.starting_pa;
    this.starting_va = rhs_.starting_va;
    this.child_table_id = rhs_.child_table_id;
  endfunction

  virtual function string convert2string();
    string str;
    str = $sformatf("xwr: %0s, (v)alid:%0d, u: %0d, pa:0x%0x, va:0x%0x",
                     xwr.name(), v, u, starting_pa, starting_va);
    case(MODE)
      SV32: str = {str, $sformatf(", ppn[1:0] = %0d/%0d", ppn1, ppn0)};
      SV39: str = {str, $sformatf(", ppn[2:0] = %0d/%0d/%0d", ppn2, ppn1, ppn0)};
      SV48: str = {str, $sformatf(", ppn[3:0] = %0d/%0d/%0d/%0d", ppn3, ppn2, ppn1, ppn0)};
      default: `uvm_fatal(get_full_name(), $sformatf("Unsupported mode %0x", MODE))
    endcase
    return str;
  endfunction

  // Pack the PTE to bit stream
  virtual function void pack_entry();
    case(MODE)
      SV32: bits = {ppn1,ppn0,rsw,d,a,g,u,xwr,v};
      SV39: bits = {rsvd,ppn2,ppn1,ppn0,rsw,d,a,g,u,xwr,v};
      SV48: bits = {rsvd,ppn3,ppn2,ppn1,ppn0,rsw,d,a,g,u,xwr,v};
      default: `uvm_fatal(get_full_name(), $sformatf("Unsupported mode %0x", MODE))
    endcase
  endfunction

  // Return the PPN field offset based on the page level
  function int get_ppn_offset(bit [1:0] page_level);
    case(page_level)
      0 : return 0;
      1 : return PPN0_WIDTH;
      2 : return PPN0_WIDTH + PPN1_WIDTH;
      3 : return PPN0_WIDTH + PPN1_WIDTH + PPN2_WIDTH;
      default: `uvm_fatal(`gfn, $sformatf("Unsupported page_level %0x", page_level))
    endcase
  endfunction

  // Assign each PPN field based on the input physical address. This function is used to setup the
  // leaf PTE to map to the target physical address.
  // start_pa   : Start phyical address.
  // pte_index  : The PTE index of the input page level.
  // page_level : The page level that this PTE belongs to.
  function void set_ppn(bit [XLEN-1:0] base_pa, int pte_index, bit[1:0] page_level);
    int pte_incr[4];
    int pte_per_table = 4096 / (XLEN/8);
    ppn0 = base_pa[12 +: PPN0_WIDTH];
    ppn1 = base_pa[12 +  PPN0_WIDTH +: PPN1_WIDTH];
    if(MODE == SV39) begin
      ppn2 = base_pa[12 + PPN0_WIDTH + PPN1_WIDTH +: PPN2_WIDTH];
    end else if (MODE == SV48) begin
      ppn2 = base_pa[12 + PPN0_WIDTH + PPN1_WIDTH +: PPN2_WIDTH];
      ppn3 = base_pa[12 + PPN0_WIDTH + PPN1_WIDTH +  PPN2_WIDTH +: PPN3_WIDTH];
    end
    foreach(pte_incr[i]) begin
      if(i >= page_level) begin
        pte_incr[i] = pte_index % pte_per_table;
        pte_index = pte_index / pte_per_table;
      end
    end
    ppn0 += pte_incr[0];
    ppn1 += pte_incr[1];
    ppn2 += pte_incr[2];
    ppn3 += pte_incr[3];
    starting_pa = get_starting_pa();
    starting_va = starting_pa - base_pa;
  endfunction

  // Get the starting physical address covered by this PTE
  function bit[XLEN-1:0] get_starting_pa();
    case(MODE)
      SV32: get_starting_pa = {ppn1, ppn0};
      SV39: get_starting_pa = {ppn2, ppn1, ppn0};
      SV48: get_starting_pa = {ppn3, ppn2, ppn1, ppn0};
      default: `uvm_fatal(get_full_name(), $sformatf("Unsupported mode %0x", MODE))
    endcase
    get_starting_pa = get_starting_pa << 12;
  endfunction

endclass
