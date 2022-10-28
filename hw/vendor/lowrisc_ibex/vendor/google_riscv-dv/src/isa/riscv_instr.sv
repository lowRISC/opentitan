/*
 * Copyright 2019 Google LLC
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

class riscv_instr extends uvm_object;

  // All derived instructions
  static bit                 instr_registry[riscv_instr_name_t];

  // Instruction list
  static riscv_instr_name_t  instr_names[$];

  // Categorized instruction list
  static riscv_instr_name_t  instr_group[riscv_instr_group_t][$];
  static riscv_instr_name_t  instr_category[riscv_instr_category_t][$];
  static riscv_instr_name_t  basic_instr[$];
  static riscv_instr         instr_template[riscv_instr_name_t];


  riscv_instr_gen_config     m_cfg;

  // Instruction attributes
  riscv_instr_group_t        group;
  riscv_instr_format_t       format;
  riscv_instr_category_t     category;
  riscv_instr_name_t         instr_name;
  imm_t                      imm_type;
  bit [4:0]                  imm_len;

  // Operands
  rand bit [11:0]            csr;
  rand riscv_reg_t           rs2;
  rand riscv_reg_t           rs1;
  rand riscv_reg_t           rd;
  rand bit [31:0]            imm;

  // Helper fields
  bit [31:0]                 imm_mask = 32'hFFFF_FFFF;
  bit                        is_branch_target;
  bit                        has_label = 1'b1;
  bit                        atomic = 0;
  bit                        branch_assigned;
  bit                        process_load_store = 1'b1;
  bit                        is_compressed;
  bit                        is_illegal_instr;
  bit                        is_hint_instr;
  bit                        is_floating_point;
  string                     imm_str;
  string                     comment;
  string                     label;
  bit                        is_local_numeric_label;
  int                        idx = -1;
  bit                        has_rs1 = 1'b1;
  bit                        has_rs2 = 1'b1;
  bit                        has_rd = 1'b1;
  bit                        has_imm = 1'b1;

  constraint imm_c {
    if (instr_name inside {SLLIW, SRLIW, SRAIW}) {
      imm[11:5] == 0;
    }
    if (instr_name inside {SLLI, SRLI, SRAI}) {
      if (XLEN == 32) {
        imm[11:5] == 0;
      } else {
        imm[11:6] == 0;
      }
    }
  }


  `uvm_object_utils(riscv_instr)
  `uvm_object_new

  static function bit register(riscv_instr_name_t instr_name);
    `uvm_info("riscv_instr", $sformatf("Registering %0s", instr_name.name()), UVM_LOW)
    instr_registry[instr_name] = 1;
    return 1;
  endfunction : register

  // Create the list of instructions based on the supported ISA extensions and configuration of the
  // generator.
  static function void create_instr_list(riscv_instr_gen_config cfg);
    instr_names.delete();
    instr_group.delete();
    instr_category.delete();
    foreach (instr_registry[instr_name]) begin
      riscv_instr instr_inst;
      if (instr_name inside {unsupported_instr}) continue;
      instr_inst = create_instr(instr_name);
      instr_template[instr_name] = instr_inst;
      if (!instr_inst.is_supported(cfg)) continue;
      // C_JAL is RV32C only instruction
      if ((XLEN != 32) && (instr_name == C_JAL)) continue;
      if ((SP inside {cfg.reserved_regs}) && (instr_name inside {C_ADDI16SP})) begin
        continue;
      end
      if (!cfg.enable_sfence && instr_name == SFENCE_VMA) continue;
      if (cfg.no_fence && (instr_name inside {FENCE, FENCE_I, SFENCE_VMA})) continue;
      if ((instr_inst.group inside {supported_isa}) &&
          !(cfg.disable_compressed_instr &&
            (instr_inst.group inside {RV32C, RV64C, RV32DC, RV32FC, RV128C})) &&
          !(!cfg.enable_floating_point &&
            (instr_inst.group inside {RV32F, RV64F, RV32D, RV64D})) &&
          !(!cfg.enable_vector_extension &&
            (instr_inst.group inside {RVV})) &&
          !(cfg.vector_instr_only &&
            !(instr_inst.group inside {RVV}))
          ) begin
        instr_category[instr_inst.category].push_back(instr_name);
        instr_group[instr_inst.group].push_back(instr_name);
        instr_names.push_back(instr_name);
      end
    end
    build_basic_instruction_list(cfg);
  endfunction : create_instr_list

  virtual function bit is_supported(riscv_instr_gen_config cfg);
    return 1;
  endfunction

  static function riscv_instr create_instr(riscv_instr_name_t instr_name);
    uvm_object obj;
    riscv_instr inst;
    string instr_class_name;
    uvm_coreservice_t coreservice = uvm_coreservice_t::get();
    uvm_factory factory = coreservice.get_factory();
    instr_class_name = {"riscv_", instr_name.name(), "_instr"};
    obj = factory.create_object_by_name(instr_class_name, "riscv_instr", instr_class_name);
    if (obj == null) begin
      `uvm_fatal("riscv_instr", $sformatf("Failed to create instr: %0s", instr_class_name))
    end
    if (!$cast(inst, obj)) begin
      `uvm_fatal("riscv_instr", $sformatf("Failed to cast instr: %0s", instr_class_name))
    end
    return inst;
  endfunction : create_instr

  static function void build_basic_instruction_list(riscv_instr_gen_config cfg);
    basic_instr = {instr_category[SHIFT], instr_category[ARITHMETIC],
                   instr_category[LOGICAL], instr_category[COMPARE]};
    if (!cfg.no_ebreak) begin
      basic_instr = {basic_instr, EBREAK};
      foreach (riscv_instr_pkg::supported_isa[i]) begin
        if (RV32C inside {riscv_instr_pkg::supported_isa[i]} &&
            !cfg.disable_compressed_instr) begin
          basic_instr = {basic_instr, C_EBREAK};
          break;
        end
      end
    end
    if (!cfg.no_ecall) begin
      basic_instr = {basic_instr, ECALL};
    end
    if (cfg.no_dret == 0) begin
      basic_instr = {basic_instr, DRET};
    end
    if (cfg.no_fence == 0) begin
      basic_instr = {basic_instr, instr_category[SYNCH]};
    end
    if ((cfg.no_csr_instr == 0) && (cfg.init_privileged_mode == MACHINE_MODE)) begin
      basic_instr = {basic_instr, instr_category[CSR]};
    end
    if (cfg.no_wfi == 0) begin
      basic_instr = {basic_instr, WFI};
    end
  endfunction : build_basic_instruction_list

  static function riscv_instr get_rand_instr(riscv_instr instr_h = null,
                                             riscv_instr_name_t include_instr[$] = {},
                                             riscv_instr_name_t exclude_instr[$] = {},
                                             riscv_instr_category_t include_category[$] = {},
                                             riscv_instr_category_t exclude_category[$] = {},
                                             riscv_instr_group_t include_group[$] = {},
                                             riscv_instr_group_t exclude_group[$] = {});
     int unsigned idx;
     riscv_instr_name_t name;
     riscv_instr_name_t allowed_instr[$];
     riscv_instr_name_t disallowed_instr[$];
     riscv_instr_category_t allowed_categories[$];
     foreach (include_category[i]) begin
       allowed_instr = {allowed_instr, instr_category[include_category[i]]};
     end
     foreach (exclude_category[i]) begin
       if (instr_category.exists(exclude_category[i])) begin
         disallowed_instr = {disallowed_instr, instr_category[exclude_category[i]]};
       end
     end
     foreach (include_group[i]) begin
       allowed_instr = {allowed_instr, instr_group[include_group[i]]};
     end
     foreach (exclude_group[i]) begin
       if (instr_group.exists(exclude_group[i])) begin
         disallowed_instr = {disallowed_instr, instr_group[exclude_group[i]]};
       end
     end
     disallowed_instr = {disallowed_instr, exclude_instr};
     if (disallowed_instr.size() == 0) begin
       if (include_instr.size() > 0) begin
         idx = $urandom_range(0, include_instr.size()-1);
         name = include_instr[idx];
       end else if (allowed_instr.size() > 0) begin
         idx = $urandom_range(0, allowed_instr.size()-1);
         name = allowed_instr[idx];
       end else begin
         idx = $urandom_range(0, instr_names.size()-1);
         name = instr_names[idx];
       end
     end else begin
       if (!std::randomize(name) with {
          name inside {instr_names};
          if (include_instr.size() > 0) {
            name inside {include_instr};
          }
          if (allowed_instr.size() > 0) {
            name inside {allowed_instr};
          }
          if (disallowed_instr.size() > 0) {
            !(name inside {disallowed_instr});
          }
       }) begin
         `uvm_fatal("riscv_instr", "Cannot generate random instruction")
       end
     end
     // Shallow copy for all relevant fields, avoid using create() to improve performance
     instr_h = new instr_template[name];
     return instr_h;
  endfunction : get_rand_instr

  static function riscv_instr get_load_store_instr(riscv_instr_name_t load_store_instr[$] = {});
     riscv_instr instr_h;
     int unsigned idx;
     int unsigned i;
     riscv_instr_name_t name;
     if (load_store_instr.size() == 0) begin
       load_store_instr = {instr_category[LOAD], instr_category[STORE]};
     end
     // Filter out unsupported load/store instruction
     if (unsupported_instr.size() > 0) begin
       while (i < load_store_instr.size()) begin
         if (load_store_instr[i] inside {unsupported_instr}) begin
           load_store_instr.delete(i);
         end else begin
           i++;
         end
       end
     end
     if (load_store_instr.size() == 0) begin
       $error("Cannot find available load/store instruction");
       $fatal(1);
     end
     idx = $urandom_range(0, load_store_instr.size()-1);
     name = load_store_instr[idx];
     // Shallow copy for all relevant fields, avoid using create() to improve performance
     instr_h = new instr_template[name];
     return instr_h;
  endfunction : get_load_store_instr

  static function riscv_instr get_instr(riscv_instr_name_t name);
     riscv_instr instr_h;
     if (!instr_template.exists(name)) begin
       `uvm_fatal("riscv_instr", $sformatf("Cannot get instr %0s", name.name()))
     end
     // Shallow copy for all relevant fields, avoid using create() to improve performance
     instr_h = new instr_template[name];
     return instr_h;
  endfunction : get_instr

  // Disable the rand mode for unused operands to randomization performance
  virtual function void set_rand_mode();
    case (format) inside
      R_FORMAT : has_imm = 1'b0;
      I_FORMAT : has_rs2 = 1'b0;
      S_FORMAT, B_FORMAT : has_rd = 1'b0;
      U_FORMAT, J_FORMAT : begin
        has_rs1 = 1'b0;
        has_rs2 = 1'b0;
      end
    endcase
  endfunction

  function void pre_randomize();
    rs1.rand_mode(has_rs1);
    rs2.rand_mode(has_rs2);
    rd.rand_mode(has_rd);
    imm.rand_mode(has_imm);
    if (category != CSR) begin
      csr.rand_mode(0);
    end
  endfunction

  virtual function void set_imm_len();
    if(format inside {U_FORMAT, J_FORMAT}) begin
      imm_len = 20;
    end else if(format inside {I_FORMAT, S_FORMAT, B_FORMAT}) begin
      if(imm_type == UIMM) begin
        imm_len = 5;
      end else begin
        imm_len = 12;
      end
    end
    imm_mask = imm_mask << imm_len;
  endfunction

  virtual function void extend_imm();
    bit sign;
    imm = imm << (32 - imm_len);
    sign = imm[31];
    imm = imm >> (32 - imm_len);
    // Signed extension
    if (sign && !((format == U_FORMAT) || (imm_type inside {UIMM, NZUIMM}))) begin
      imm = imm_mask | imm;
    end
  endfunction : extend_imm

  function void post_randomize();
    extend_imm();
    update_imm_str();
  endfunction : post_randomize

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    if(category != SYSTEM) begin
      case(format)
        J_FORMAT, U_FORMAT : // instr rd,imm
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
        I_FORMAT: // instr rd,rs1,imm
          if(instr_name == NOP)
            asm_str = "nop";
          else if(instr_name == WFI)
            asm_str = "wfi";
          else if(instr_name == FENCE)
            asm_str = $sformatf("fence"); // TODO: Support all fence combinations
          else if(instr_name == FENCE_I)
            asm_str = "fence.i";
          else if(category == LOAD) // Use psuedo instruction format
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), get_imm());
        S_FORMAT, B_FORMAT: // instr rs1,rs2,imm
          if(category == STORE) // Use psuedo instruction format
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rs1.name(), rs2.name(), get_imm());
        R_FORMAT: // instr rd,rs1,rs2
          if(instr_name == SFENCE_VMA) begin
            asm_str = "sfence.vma x0, x0"; // TODO: Support all possible sfence
          end else begin
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), rs2.name());
          end
        default: `uvm_fatal(`gfn, $sformatf("Unsupported format %0s [%0s]",
                                            format.name(), instr_name.name()))
      endcase
    end else begin
      // For EBREAK,C.EBREAK, making sure pc+4 is a valid instruction boundary
      // This is needed to resume execution from epc+4 after ebreak handling
      if(instr_name == EBREAK) begin
        asm_str = ".4byte 0x00100073 # ebreak";
      end
    end
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction

  function bit [6:0] get_opcode();
    case (instr_name) inside
      LUI                                                          : get_opcode = 7'b0110111;
      AUIPC                                                        : get_opcode = 7'b0010111;
      JAL                                                          : get_opcode = 7'b1101111;
      JALR                                                         : get_opcode = 7'b1100111;
      BEQ, BNE, BLT, BGE, BLTU, BGEU                               : get_opcode = 7'b1100011;
      LB, LH, LW, LBU, LHU, LWU, LD                                : get_opcode = 7'b0000011;
      SB, SH, SW, SD                                               : get_opcode = 7'b0100011;
      ADDI, SLTI, SLTIU, XORI, ORI, ANDI, SLLI, SRLI, SRAI, NOP    : get_opcode = 7'b0010011;
      ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND, MUL,
      MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU                    : get_opcode = 7'b0110011;
      ADDIW, SLLIW, SRLIW, SRAIW                                   : get_opcode = 7'b0011011;
      MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU                    : get_opcode = 7'b0110011;
      FENCE, FENCE_I                                               : get_opcode = 7'b0001111;
      ECALL, EBREAK                                                : get_opcode = 7'b1110011;
      ADDW, SUBW, SLLW, SRLW, SRAW, MULW, DIVW, DIVUW, REMW, REMUW : get_opcode = 7'b0111011;
      ECALL, EBREAK, URET, SRET, MRET, DRET, WFI, SFENCE_VMA       : get_opcode = 7'b1110011;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  virtual function bit [2:0] get_func3();
    case (instr_name) inside
      JALR       : get_func3 = 3'b000;
      BEQ        : get_func3 = 3'b000;
      BNE        : get_func3 = 3'b001;
      BLT        : get_func3 = 3'b100;
      BGE        : get_func3 = 3'b101;
      BLTU       : get_func3 = 3'b110;
      BGEU       : get_func3 = 3'b111;
      LB         : get_func3 = 3'b000;
      LH         : get_func3 = 3'b001;
      LW         : get_func3 = 3'b010;
      LBU        : get_func3 = 3'b100;
      LHU        : get_func3 = 3'b101;
      SB         : get_func3 = 3'b000;
      SH         : get_func3 = 3'b001;
      SW         : get_func3 = 3'b010;
      ADDI       : get_func3 = 3'b000;
      NOP        : get_func3 = 3'b000;
      SLTI       : get_func3 = 3'b010;
      SLTIU      : get_func3 = 3'b011;
      XORI       : get_func3 = 3'b100;
      ORI        : get_func3 = 3'b110;
      ANDI       : get_func3 = 3'b111;
      SLLI       : get_func3 = 3'b001;
      SRLI       : get_func3 = 3'b101;
      SRAI       : get_func3 = 3'b101;
      ADD        : get_func3 = 3'b000;
      SUB        : get_func3 = 3'b000;
      SLL        : get_func3 = 3'b001;
      SLT        : get_func3 = 3'b010;
      SLTU       : get_func3 = 3'b011;
      XOR        : get_func3 = 3'b100;
      SRL        : get_func3 = 3'b101;
      SRA        : get_func3 = 3'b101;
      OR         : get_func3 = 3'b110;
      AND        : get_func3 = 3'b111;
      FENCE      : get_func3 = 3'b000;
      FENCE_I    : get_func3 = 3'b001;
      ECALL      : get_func3 = 3'b000;
      EBREAK     : get_func3 = 3'b000;
      LWU        : get_func3 = 3'b110;
      LD         : get_func3 = 3'b011;
      SD         : get_func3 = 3'b011;
      ADDIW      : get_func3 = 3'b000;
      SLLIW      : get_func3 = 3'b001;
      SRLIW      : get_func3 = 3'b101;
      SRAIW      : get_func3 = 3'b101;
      ADDW       : get_func3 = 3'b000;
      SUBW       : get_func3 = 3'b000;
      SLLW       : get_func3 = 3'b001;
      SRLW       : get_func3 = 3'b101;
      SRAW       : get_func3 = 3'b101;
      MUL        : get_func3 = 3'b000;
      MULH       : get_func3 = 3'b001;
      MULHSU     : get_func3 = 3'b010;
      MULHU      : get_func3 = 3'b011;
      DIV        : get_func3 = 3'b100;
      DIVU       : get_func3 = 3'b101;
      REM        : get_func3 = 3'b110;
      REMU       : get_func3 = 3'b111;
      MULW       : get_func3 = 3'b000;
      DIVW       : get_func3 = 3'b100;
      DIVUW      : get_func3 = 3'b101;
      REMW       : get_func3 = 3'b110;
      REMUW      : get_func3 = 3'b111;
      ECALL, EBREAK, URET, SRET, MRET, DRET, WFI, SFENCE_VMA : get_func3 = 3'b000;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  function bit [6:0] get_func7();
    case (instr_name)
      SLLI   : get_func7 = 7'b0000000;
      SRLI   : get_func7 = 7'b0000000;
      SRAI   : get_func7 = 7'b0100000;
      ADD    : get_func7 = 7'b0000000;
      SUB    : get_func7 = 7'b0100000;
      SLL    : get_func7 = 7'b0000000;
      SLT    : get_func7 = 7'b0000000;
      SLTU   : get_func7 = 7'b0000000;
      XOR    : get_func7 = 7'b0000000;
      SRL    : get_func7 = 7'b0000000;
      SRA    : get_func7 = 7'b0100000;
      OR     : get_func7 = 7'b0000000;
      AND    : get_func7 = 7'b0000000;
      FENCE  : get_func7 = 7'b0000000;
      FENCE_I : get_func7 = 7'b0000000;
      SLLIW  : get_func7 = 7'b0000000;
      SRLIW  : get_func7 = 7'b0000000;
      SRAIW  : get_func7 = 7'b0100000;
      ADDW   : get_func7 = 7'b0000000;
      SUBW   : get_func7 = 7'b0100000;
      SLLW   : get_func7 = 7'b0000000;
      SRLW   : get_func7 = 7'b0000000;
      SRAW   : get_func7 = 7'b0100000;
      MUL    : get_func7 = 7'b0000001;
      MULH   : get_func7 = 7'b0000001;
      MULHSU : get_func7 = 7'b0000001;
      MULHU  : get_func7 = 7'b0000001;
      DIV    : get_func7 = 7'b0000001;
      DIVU   : get_func7 = 7'b0000001;
      REM    : get_func7 = 7'b0000001;
      REMU   : get_func7 = 7'b0000001;
      MULW   : get_func7 = 7'b0000001;
      DIVW   : get_func7 = 7'b0000001;
      DIVUW  : get_func7 = 7'b0000001;
      REMW   : get_func7 = 7'b0000001;
      REMUW  : get_func7 = 7'b0000001;
      ECALL  : get_func7 = 7'b0000000;
      EBREAK : get_func7 = 7'b0000000;
      URET   : get_func7 = 7'b0000000;
      SRET   : get_func7 = 7'b0001000;
      MRET   : get_func7 = 7'b0011000;
      DRET   : get_func7 = 7'b0111101;
      WFI    : get_func7 = 7'b0001000;
      SFENCE_VMA: get_func7 = 7'b0001001;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2bin(string prefix = "");
    string binary;
    case(format)
      J_FORMAT: begin
          binary = $sformatf("%8h", {imm[20], imm[10:1], imm[11], imm[19:12], rd,  get_opcode()});
      end
      U_FORMAT: begin
          binary = $sformatf("%8h", {imm[31:12], rd,  get_opcode()});
      end
      I_FORMAT: begin
        if(instr_name inside {FENCE, FENCE_I})
          binary = $sformatf("%8h", {17'b0, get_func3(), 5'b0, get_opcode()});
        else if(instr_name == ECALL)
          binary = $sformatf("%8h", {get_func7(), 18'b0, get_opcode()});
        else if(instr_name inside {URET, SRET, MRET})
          binary = $sformatf("%8h", {get_func7(), 5'b00010, 13'b0, get_opcode()});
        else if(instr_name inside {DRET})
          binary = $sformatf("%8h", {get_func7(), 5'b10010, 13'b0, get_opcode()});
        else if(instr_name == EBREAK)
          binary = $sformatf("%8h", {get_func7(), 5'd1, 13'b0, get_opcode()});
        else if(instr_name == WFI)
          binary = $sformatf("%8h", {get_func7(), 5'b00101, 13'b0, get_opcode()});
        else
          binary = $sformatf("%8h", {imm[11:0], rs1, get_func3(), rd, get_opcode()});
      end
      S_FORMAT: begin
          binary = $sformatf("%8h", {imm[11:5], rs2, rs1, get_func3(), imm[4:0], get_opcode()});
      end
      B_FORMAT: begin
          binary = $sformatf("%8h",
                             {imm[12], imm[10:5], rs2, rs1, get_func3(),
                              imm[4:1], imm[11], get_opcode()});
      end
      R_FORMAT: begin
        if(instr_name == SFENCE_VMA)
          binary = $sformatf("%8h", {get_func7(), 18'b0, get_opcode()});
        else
          binary = $sformatf("%8h", {get_func7(), rs2, rs1, get_func3(), rd, get_opcode()});
      end
      default: `uvm_fatal(`gfn, $sformatf("Unsupported format %0s", format.name()))
    endcase
    return {prefix, binary};
  endfunction

  virtual function string get_instr_name();
    get_instr_name = instr_name.name();
    foreach(get_instr_name[i]) begin
      if (get_instr_name[i] == "_") begin
        get_instr_name[i] = ".";
      end
    end
    return get_instr_name;
  endfunction

  // Get RVC register name for CIW, CL, CS, CB format
  function bit [2:0] get_c_gpr(riscv_reg_t gpr);
    return gpr[2:0];
  endfunction

  // Default return imm value directly, can be overriden to use labels and symbols
  // Example: %hi(symbol), %pc_rel(label) ...
  virtual function string get_imm();
    return imm_str;
  endfunction

  virtual function void clear_unused_label();
    if(has_label && !is_branch_target && is_local_numeric_label) begin
      has_label = 1'b0;
    end
  endfunction

  virtual function void do_copy(uvm_object rhs);
    riscv_instr rhs_;
    super.copy(rhs);
    assert($cast(rhs_, rhs));
    this.group          = rhs_.group;
    this.format         = rhs_.format;
    this.category       = rhs_.category;
    this.instr_name     = rhs_.instr_name;
    this.rs2            = rhs_.rs2;
    this.rs1            = rhs_.rs1;
    this.rd             = rhs_.rd;
    this.imm            = rhs_.imm;
    this.imm_type       = rhs_.imm_type;
    this.imm_len        = rhs_.imm_len;
    this.imm_mask       = rhs_.imm_mask;
    this.imm_str        = rhs_.imm_str;
    this.imm_mask       = rhs_.imm_mask;
    this.is_compressed  = rhs_.is_compressed;
    this.has_rs2        = rhs_.has_rs2;
    this.has_rs1        = rhs_.has_rs1;
    this.has_rd         = rhs_.has_rd;
    this.has_imm        = rhs_.has_imm;
  endfunction : do_copy

  virtual function void update_imm_str();
    imm_str = $sformatf("%0d", $signed(imm));
  endfunction

  `include "isa/riscv_instr_cov.svh"

endclass
