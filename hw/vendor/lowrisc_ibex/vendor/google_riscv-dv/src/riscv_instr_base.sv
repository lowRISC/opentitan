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

class riscv_instr_base extends uvm_object;

  rand riscv_instr_group_t      group;
  rand riscv_instr_format_t     format;
  rand riscv_instr_category_t   category;
  rand riscv_instr_name_t       instr_name;
  rand bit [11:0]               csr;

  rand riscv_reg_t              rs2;
  rand riscv_reg_t              rs1;
  rand riscv_reg_t              rd;
  rand riscv_fpr_t              fs1;
  rand riscv_fpr_t              fs2;
  rand riscv_fpr_t              fs3;
  rand riscv_fpr_t              fd;
  rand bit [31:0]               imm;
  rand imm_t                    imm_type;
  rand bit [4:0]                imm_len;
  rand bit                      is_pseudo_instr;
  rand bit                      aq;
  rand bit                      rl;
  bit                           is_branch_target;
  bit                           has_label = 1'b1;
  bit                           atomic = 0;
  bit                           branch_assigned;
  bit                           process_load_store = 1'b1;
  bit                           is_compressed;
  bit                           is_illegal_instr;
  bit                           is_hint_instr;
  bit                           has_imm;
  bit                           has_rs1;
  bit                           has_rs2;
  bit                           has_rd;
  bit                           has_fs1;
  bit                           has_fs2;
  bit                           has_fs3;
  bit                           has_fd;
  bit                           is_floating_point;
  bit [31:0]                    imm_mask = '1;
  string                        imm_str;
  string                        comment;
  string                        label;
  bit                           is_local_numeric_label;
  int                           idx = -1;

  `uvm_object_utils(riscv_instr_base)

  constraint default_c {
    soft is_pseudo_instr == 0;
    instr_name != INVALID_INSTR;
  }

  // Immediate bit length for different instruction format
  constraint imm_len_c {
    solve imm_type before imm_len;
    if(format inside {U_FORMAT, J_FORMAT}) {
      imm_len == 20;
    }
    if(format inside {I_FORMAT, S_FORMAT, B_FORMAT}) {
      if(imm_type == UIMM) {
        imm_len == 5;
      } else {
        imm_len == 11;
      }
    }
    if(format inside {CI_FORMAT, CSS_FORMAT}) {
      // TODO: gcc compiler seems to not support 6 bits unsigned imm for c.lui,
      // hardcoded to 5 bits for now
      if(instr_name == C_LUI) {
        imm_len == 5;
      } else {
        imm_len == 6;
      }
    }
    if(format inside {CL_FORMAT, CS_FORMAT}) {
      imm_len == 5;
    }
    if(format inside {CJ_FORMAT}) {
      imm_len == 11;
    }
    if(format inside {CB_FORMAT, CIW_FORMAT}) {
      if(instr_name == C_ANDI) {
        imm_len == 6;
      } else {
        imm_len == 8;
      }
    }
    imm_len <= 20;
  }

  constraint legal_operand_c {
    (instr_name == C_LUI) -> (rd != SP);
  }

  constraint imm_val_c {
    if(imm_type inside {NZIMM, NZUIMM}) {
      imm != 0;
    }
  }

  constraint aq_rl_c {
    aq && rl == 0;
  }

  // Avoid generating HINT or illegal instruction by default as it's not supported by the compiler
  constraint no_hint_illegal_instr_c {
    if (instr_name inside {C_ADDI, C_ADDIW, C_LI, C_LUI, C_SLLI, C_SLLI64,
                           C_LQSP, C_LDSP, C_MV, C_ADD}) {
      rd != ZERO;
    }
    if (instr_name == C_JR) {
      rs1 != ZERO;
    }
    if (instr_name inside {C_ADD, C_MV}) {
      rs2 != ZERO;
    }
  }

  // Cannot shift more than the width of the bus
  constraint shift_imm_val_c {
    solve category before imm;
    if(category == SHIFT) {
      if(group == RV64I) {
        // The new instruction in RV64I only handles 32 bits value
        imm < 32;
      } else {
        imm < XLEN;
      }
    }
  }

  constraint load_store_c {
    if(category inside {LOAD, STORE}) {
      rs1 != ZERO; // x0 cannot be used to save the base address
    }
  }

  constraint nop_c {
    if(instr_name inside {NOP, C_NOP}) {
      rs1 == ZERO;
      rs2 == ZERO;
      rd  == ZERO;
    }
  }

  constraint jal_c {
    if (XLEN != 32) {
      soft instr_name != C_JAL;
    }
  }

  constraint system_instr_c {
    if (category inside {SYSTEM, SYNCH}) {
      rd  == ZERO;
      rs1 == ZERO;
    }
  }

  constraint rvc_csr_c {
    //  Registers specified by the three-bit rs1’, rs2’, and rd’
    if(format inside {CIW_FORMAT, CL_FORMAT, CS_FORMAT, CB_FORMAT, CA_FORMAT}) {
      rs1 inside {[S0:A5]};
      rs2 inside {[S0:A5]};
      rd  inside {[S0:A5]};
    }
    // C_ADDI16SP is only valid when rd == SP
    if(instr_name == C_ADDI16SP) {
      rd  == SP;
      rs1 == SP;
    }

    if(instr_name inside {C_JR, C_JALR}) {
      rs2 == ZERO;
      rs1 != ZERO;
    }
  }

  ////////////  RV32I instructions  //////////////
  // LOAD instructions
  `add_instr(LB,     I_FORMAT, LOAD, RV32I)
  `add_instr(LH,     I_FORMAT, LOAD, RV32I)
  `add_instr(LW,     I_FORMAT, LOAD, RV32I)
  `add_instr(LBU,    I_FORMAT, LOAD, RV32I)
  `add_instr(LHU,    I_FORMAT, LOAD, RV32I)
  // STORE instructions
  `add_instr(SB,     S_FORMAT, STORE, RV32I)
  `add_instr(SH,     S_FORMAT, STORE, RV32I)
  `add_instr(SW,     S_FORMAT, STORE, RV32I)
  // SHIFT intructions
  `add_instr(SLL,    R_FORMAT, SHIFT, RV32I)
  `add_instr(SLLI,   I_FORMAT, SHIFT, RV32I)
  `add_instr(SRL,    R_FORMAT, SHIFT, RV32I)
  `add_instr(SRLI,   I_FORMAT, SHIFT, RV32I)
  `add_instr(SRA,    R_FORMAT, SHIFT, RV32I)
  `add_instr(SRAI,   I_FORMAT, SHIFT, RV32I)
  // ARITHMETIC intructions
  `add_instr(ADD,    R_FORMAT, ARITHMETIC, RV32I)
  `add_instr(ADDI,   I_FORMAT, ARITHMETIC, RV32I)
  `add_instr(NOP,    I_FORMAT, ARITHMETIC, RV32I)
  `add_instr(SUB,    R_FORMAT, ARITHMETIC, RV32I)
  `add_instr(LUI,    U_FORMAT, ARITHMETIC, RV32I, UIMM)
  `add_instr(AUIPC,  U_FORMAT, ARITHMETIC, RV32I, UIMM)
  // LOGICAL instructions
  `add_instr(XOR,    R_FORMAT, LOGICAL, RV32I)
  `add_instr(XORI,   I_FORMAT, LOGICAL, RV32I)
  `add_instr(OR,     R_FORMAT, LOGICAL, RV32I)
  `add_instr(ORI,    I_FORMAT, LOGICAL, RV32I)
  `add_instr(AND,    R_FORMAT, LOGICAL, RV32I)
  `add_instr(ANDI,   I_FORMAT, LOGICAL, RV32I)
  // COMPARE instructions
  `add_instr(SLT,    R_FORMAT, COMPARE, RV32I)
  `add_instr(SLTI,   I_FORMAT, COMPARE, RV32I)
  `add_instr(SLTU,   R_FORMAT, COMPARE, RV32I)
  `add_instr(SLTIU,  I_FORMAT, COMPARE, RV32I)
  // BRANCH instructions
  `add_instr(BEQ,    B_FORMAT, BRANCH, RV32I)
  `add_instr(BNE,    B_FORMAT, BRANCH, RV32I)
  `add_instr(BLT,    B_FORMAT, BRANCH, RV32I)
  `add_instr(BGE,    B_FORMAT, BRANCH, RV32I)
  `add_instr(BLTU,   B_FORMAT, BRANCH, RV32I)
  `add_instr(BGEU,   B_FORMAT, BRANCH, RV32I)
  // JUMP instructions
  `add_instr(JAL,    J_FORMAT, JUMP, RV32I)
  `add_instr(JALR,   I_FORMAT, JUMP, RV32I)
  // SYNCH instructions
  `add_instr(FENCE,   I_FORMAT, SYNCH, RV32I)
  `add_instr(FENCE_I,  I_FORMAT, SYNCH, RV32I)
  // SYSTEM instructions
  `add_instr(ECALL,   I_FORMAT, SYSTEM, RV32I)
  `add_instr(EBREAK,  I_FORMAT, SYSTEM, RV32I)
  `add_instr(URET,    I_FORMAT, SYSTEM, RV32I)
  `add_instr(SRET,    I_FORMAT, SYSTEM, RV32I)
  `add_instr(MRET,    I_FORMAT, SYSTEM, RV32I)
  `add_instr(DRET,    I_FORMAT, SYSTEM, RV32I)
  `add_instr(WFI,     I_FORMAT, INTERRUPT, RV32I)
  // CSR instructions
  `add_instr(CSRRW,  R_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRS,  R_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRC,  R_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRWI, I_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRSI, I_FORMAT, CSR, RV32I, UIMM)
  `add_instr(CSRRCI, I_FORMAT, CSR, RV32I, UIMM)

  ////////////  RV32M instructions  //////////////
  `add_instr(MUL,    R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(MULH,   R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(MULHSU, R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(MULHU,  R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(DIV,    R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(DIVU,   R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(REM,    R_FORMAT, ARITHMETIC, RV32M)
  `add_instr(REMU,   R_FORMAT, ARITHMETIC, RV32M)

  ////////////  RV64M instructions  //////////////
  `add_instr(MULW,   R_FORMAT, ARITHMETIC, RV64M)
  `add_instr(DIVW,   R_FORMAT, ARITHMETIC, RV64M)
  `add_instr(DIVUW,  R_FORMAT, ARITHMETIC, RV64M)
  `add_instr(REMW,   R_FORMAT, ARITHMETIC, RV64M)
  `add_instr(REMUW,  R_FORMAT, ARITHMETIC, RV64M)

  ////////////  RV32F instructions  //////////////
  `add_instr(FLW,       I_FORMAT, LOAD, RV32F)
  `add_instr(FSW,       S_FORMAT, STORE, RV32F)
  `add_instr(FMADD_S,   R4_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMSUB_S,   R4_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FNMSUB_S,  R4_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FNMADD_S,  R4_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FADD_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSUB_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMUL_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FDIV_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSQRT_S,   I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSGNJ_S,   R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSGNJN_S,  R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FSGNJX_S,  R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMIN_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMAX_S,    R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FCVT_W_S,  I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FCVT_WU_S, I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMV_X_W,   I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FEQ_S,     R_FORMAT, COMPARE, RV32F)
  `add_instr(FLT_S,     R_FORMAT, COMPARE, RV32F)
  `add_instr(FLE_S,     R_FORMAT, COMPARE, RV32F)
  `add_instr(FCLASS_S,  R_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FCVT_S_W,  I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FCVT_S_WU, I_FORMAT, ARITHMETIC, RV32F)
  `add_instr(FMV_W_X,   I_FORMAT, ARITHMETIC, RV32F)

  /////////////  RV64F instruction /////////////////
  `add_instr(FCVT_L_S,  I_FORMAT, ARITHMETIC, RV64F)
  `add_instr(FCVT_LU_S, I_FORMAT, ARITHMETIC, RV64F)
  `add_instr(FCVT_S_L,  I_FORMAT, ARITHMETIC, RV64F)
  `add_instr(FCVT_S_LU, I_FORMAT, ARITHMETIC, RV64F)

  ////////////  RV32D instructions  ////////////////
  `add_instr(FLD,       I_FORMAT, LOAD, RV32D)
  `add_instr(FSD,       S_FORMAT, STORE, RV32D)
  `add_instr(FMADD_D,   R4_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FMSUB_D,   R4_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FNMSUB_D,  R4_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FNMADD_D,  R4_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FADD_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSUB_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FMUL_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FDIV_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSQRT_D,   I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSGNJ_D,   R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSGNJN_D,  R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FSGNJX_D,  R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FMIN_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FMAX_D,    R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_S_D,  I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_D_S,  I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FEQ_D,     R_FORMAT, COMPARE, RV32D)
  `add_instr(FLT_D,     R_FORMAT, COMPARE, RV32D)
  `add_instr(FLE_D,     R_FORMAT, COMPARE, RV32D)
  `add_instr(FCLASS_D,  R_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_W_D,  I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_WU_D, I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_D_W,  I_FORMAT, ARITHMETIC, RV32D)
  `add_instr(FCVT_D_WU, I_FORMAT, ARITHMETIC, RV32D)

  //////////////  RV64D instruction  ///////////////
  `add_instr(FMV_X_D,   I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FMV_D_X,   I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FCVT_L_D,  I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FCVT_LU_D, I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FCVT_D_L,  I_FORMAT, ARITHMETIC, RV64D)
  `add_instr(FCVT_D_LU, I_FORMAT, ARITHMETIC, RV64D)

  // RV64I instructions
  // LOAD/STORE instructions
  `add_instr(LWU,     I_FORMAT, LOAD, RV64I)
  `add_instr(LD,      I_FORMAT, LOAD, RV64I)
  `add_instr(SD,      S_FORMAT, STORE, RV64I)
  // SHIFT intructions
  `add_instr(SLLW,    R_FORMAT, SHIFT, RV64I)
  `add_instr(SLLIW,   I_FORMAT, SHIFT, RV64I)
  `add_instr(SRLW,    R_FORMAT, SHIFT, RV64I)
  `add_instr(SRLIW,   I_FORMAT, SHIFT, RV64I)
  `add_instr(SRAW,    R_FORMAT, SHIFT, RV64I)
  `add_instr(SRAIW,   I_FORMAT, SHIFT, RV64I)
  // ARITHMETIC intructions
  `add_instr(ADDW,    R_FORMAT, ARITHMETIC, RV64I)
  `add_instr(ADDIW,   I_FORMAT, ARITHMETIC, RV64I)
  `add_instr(SUBW,    R_FORMAT, ARITHMETIC, RV64I)

  // RV32IC
  `add_instr(C_LW,       CL_FORMAT, LOAD, RV32C, UIMM)
  `add_instr(C_SW,       CS_FORMAT, STORE, RV32C, UIMM)
  `add_instr(C_LWSP,     CI_FORMAT, LOAD, RV32C, UIMM)
  `add_instr(C_SWSP,     CSS_FORMAT, STORE, RV32C, UIMM)
  `add_instr(C_ADDI4SPN, CIW_FORMAT, ARITHMETIC, RV32C, NZUIMM)
  `add_instr(C_ADDI,     CI_FORMAT, ARITHMETIC, RV32C, NZIMM)
  `add_instr(C_ADDI16SP, CI_FORMAT, ARITHMETIC, RV32C, NZIMM)
  `add_instr(C_LI,       CI_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_LUI,      CI_FORMAT, ARITHMETIC, RV32C, NZUIMM)
  `add_instr(C_SUB,      CA_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_ADD,      CR_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_NOP,      CI_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_MV,       CR_FORMAT, ARITHMETIC, RV32C)
  `add_instr(C_ANDI,     CB_FORMAT, LOGICAL, RV32C)
  `add_instr(C_XOR,      CA_FORMAT, LOGICAL, RV32C)
  `add_instr(C_OR,       CA_FORMAT, LOGICAL, RV32C)
  `add_instr(C_AND,      CA_FORMAT, LOGICAL, RV32C)
  `add_instr(C_BEQZ,     CB_FORMAT, BRANCH, RV32C)
  `add_instr(C_BNEZ,     CB_FORMAT, BRANCH, RV32C)
  `add_instr(C_SRLI,     CB_FORMAT, SHIFT, RV32C, NZUIMM)
  `add_instr(C_SRAI,     CB_FORMAT, SHIFT, RV32C, NZUIMM)
  `add_instr(C_SLLI,     CI_FORMAT, SHIFT, RV32C, NZUIMM)
  `add_instr(C_J,        CJ_FORMAT, JUMP, RV32C)
  `add_instr(C_JAL,      CJ_FORMAT, JUMP, RV32C)
  `add_instr(C_JR,       CR_FORMAT, JUMP, RV32C)
  `add_instr(C_JALR,     CR_FORMAT, JUMP, RV32C)
  `add_instr(C_EBREAK,   CI_FORMAT, SYSTEM, RV32C)

  // RV64C
  `add_instr(C_ADDIW,  CI_FORMAT, ARITHMETIC, RV64C)
  `add_instr(C_SUBW,   CA_FORMAT, ARITHMETIC, RV64C)
  `add_instr(C_ADDW,   CA_FORMAT, ARITHMETIC, RV64C)
  `add_instr(C_LD,     CL_FORMAT, LOAD, RV64C, UIMM)
  `add_instr(C_SD,     CS_FORMAT, STORE, RV64C, UIMM)
  `add_instr(C_LDSP,   CI_FORMAT, LOAD, RV64C, UIMM)
  `add_instr(C_SDSP,   CSS_FORMAT, STORE, RV64C, UIMM)

  // RV128C
  `add_instr(C_SRLI64, CB_FORMAT, SHIFT, RV128C, NZUIMM)
  `add_instr(C_SRAI64, CB_FORMAT, SHIFT, RV128C, NZUIMM)
  `add_instr(C_SLLI64, CI_FORMAT, SHIFT, RV128C, NZUIMM)
  `add_instr(C_LQ,     CL_FORMAT, LOAD, RV32DC, UIMM)
  `add_instr(C_SQ,     CS_FORMAT, STORE, RV32DC, UIMM)
  `add_instr(C_LQSP,   CI_FORMAT, LOAD, RV32DC, UIMM)
  `add_instr(C_SQSP,   CSS_FORMAT, STORE, RV32DC, UIMM)

  // RV32FC
  `add_instr(C_FLW,   CL_FORMAT, LOAD, RV32FC, UIMM)
  `add_instr(C_FSW,   CS_FORMAT, STORE, RV32FC, UIMM)
  `add_instr(C_FLWSP, CI_FORMAT, LOAD, RV32FC, UIMM)
  `add_instr(C_FSWSP, CSS_FORMAT, STORE, RV32FC, UIMM)

  // RV32DC
  `add_instr(C_FLD,   CL_FORMAT, LOAD, RV32DC, UIMM)
  `add_instr(C_FSD,   CS_FORMAT, STORE, RV32DC, UIMM)
  `add_instr(C_FLDSP, CI_FORMAT, LOAD, RV32DC, UIMM)
  `add_instr(C_FSDSP, CSS_FORMAT, STORE, RV32DC, UIMM)

  // RV32A
  `add_instr(LR_W,      R_FORMAT, LOAD, RV32A)
  `add_instr(SC_W,      R_FORMAT, STORE, RV32A)
  `add_instr(AMOSWAP_W, R_FORMAT, AMO, RV32A)
  `add_instr(AMOADD_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOAND_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOOR_W,   R_FORMAT, AMO, RV32A)
  `add_instr(AMOXOR_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOMIN_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOMAX_W,  R_FORMAT, AMO, RV32A)
  `add_instr(AMOMINU_W, R_FORMAT, AMO, RV32A)
  `add_instr(AMOMAXU_W, R_FORMAT, AMO, RV32A)

  // RV64A
  `add_instr(LR_D,      R_FORMAT, LOAD, RV64A)
  `add_instr(SC_D,      R_FORMAT, STORE, RV64A)
  `add_instr(AMOSWAP_D, R_FORMAT, AMO, RV64A)
  `add_instr(AMOADD_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOAND_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOOR_D,   R_FORMAT, AMO, RV64A)
  `add_instr(AMOXOR_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOMIN_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOMAX_D,  R_FORMAT, AMO, RV64A)
  `add_instr(AMOMINU_D, R_FORMAT, AMO, RV64A)
  `add_instr(AMOMAXU_D, R_FORMAT, AMO, RV64A)

  // Supervisor Instructions
  `add_instr(SFENCE_VMA, R_FORMAT,SYNCH,RV32I)

  function void post_randomize();
    if (group inside {RV32C, RV64C, RV128C, RV32DC, RV32FC}) begin
      is_compressed = 1'b1;
    end
    if (!(format inside {R_FORMAT, CR_FORMAT})) begin
      imm_mask = '1;
      imm_mask = imm_mask << imm_len;
      has_imm = 1'b1;
      mask_imm();
      if (imm_str == "") begin
        update_imm_str();
      end
    end
    if (format inside {R_FORMAT, S_FORMAT, B_FORMAT, CSS_FORMAT,
                       CS_FORMAT, CR_FORMAT, CA_FORMAT}) begin
      has_rs2 = 1'b1;
    end
    if (!(format inside {J_FORMAT, U_FORMAT, CJ_FORMAT, CSS_FORMAT,
                         CA_FORMAT, CR_FORMAT, CI_FORMAT})) begin
      has_rs1 = 1'b1;
    end else if (instr_name inside {C_JR, C_JALR}) begin
      has_rs1 = 1'b1;
    end
    if (!(format inside {CJ_FORMAT, CB_FORMAT, CS_FORMAT, CSS_FORMAT, B_FORMAT, S_FORMAT})) begin
      has_rd = 1'b1;
    end
    if (category == CSR) begin
      has_rs2 = 1'b0;
      if (instr_name inside {CSRRWI, CSRRSI, CSRRCI}) begin
        has_rs1 = 1'b0;
      end
    end
    // TODO(taliu) Add support for compressed floating point format
    if (group inside {RV32F, RV64F, RV32D, RV64D, RV32FC, RV32DC}) begin
      is_floating_point = 1'b1;
      has_rs1 = 1'b0;
      has_rs2 = 1'b0;
      has_rd  = 1'b0;
      has_fs1 = 1'b1;
      if (format == R4_FORMAT) begin
        has_fs3 = 1'b1;
      end
      if (format != S_FORMAT) begin
        if ((category == COMPARE) || (instr_name inside {FCLASS_S, FCLASS_D})) begin
          has_rd = 1'b1;
        end else begin
          has_fd = 1'b1;
        end
      end
      if (format != I_FORMAT) begin
        has_fs2 = 1'b1;
      end
      if (instr_name inside {FMV_X_W, FMV_X_D, FCVT_W_S, FCVT_WU_S,
                             FCVT_L_S, FCVT_LU_S, FCVT_L_D, FCVT_LU_D, FCVT_LU_S,
                             FCVT_W_D, FCVT_WU_D}) begin
        // Floating point to integer operation
        has_rd = 1'b1;
        has_fs1 = 1'b1;
        has_fd = 1'b0;
      end else if (instr_name inside {FMV_W_X, FMV_D_X, FCVT_S_W, FCVT_S_WU,
                                      FCVT_S_L, FCVT_D_L, FCVT_S_LU, FCVT_D_W,
                                      FCVT_D_LU, FCVT_D_WU, FLW, FLD, FSW, FSD,
                                      C_FLW, C_FLD, C_FSW, C_FSD}) begin
        // Integer to floating point operation
        has_fd = 1'b1;
        has_fs1 = 1'b0;
        has_rs1 = 1'b1;
      end
    end
  endfunction

  function void mask_imm();
    // Process the immediate value and sign extension
    if (imm_type inside {UIMM, NZUIMM}) begin
      imm = imm & ~imm_mask;
    end else begin
      if (imm[imm_len-1]) begin
        imm = imm | imm_mask;
      end else begin
        imm = imm & ~imm_mask;
      end
    end
    // Give a random value if imm is zero after masking unexpectedly
    if((imm_type inside {NZIMM, NZUIMM}) && (imm == '0)) begin
      imm = $urandom_range(2 ** (imm_len-1) - 1, 1);
    end
  endfunction

  function void gen_rand_imm();
    if (!randomize(imm)) begin
      `uvm_fatal(`gfn, "Cannot randomize imm")
    end
    mask_imm();
    update_imm_str();
  endfunction

  function void update_imm_str();
    imm_str = $sformatf("%0d", $signed(imm));
  endfunction

  function void set_imm(int imm);
    this.imm = imm;
    mask_imm();
    update_imm_str();
  endfunction

  function riscv_reg_t gen_rand_gpr(riscv_reg_t included_reg[] = {},
                                    riscv_reg_t excluded_reg[] = {});
    riscv_reg_t gpr;
    int unsigned i;
    riscv_reg_t legal_gpr[$];
    if (included_reg.size() > 0) begin
      legal_gpr = included_reg;
      if (is_compressed && !(format inside {CR_FORMAT, CI_FORMAT, CSS_FORMAT})) begin
        while (i < legal_gpr.size()) begin
          if (legal_gpr[i] < S0 || legal_gpr[i] > A5) begin
            legal_gpr.delete(i);
          end else begin
            i++;
          end
        end
      end
    end else if (is_compressed &&
                 !(format inside {CR_FORMAT, CI_FORMAT, CSS_FORMAT})) begin
      legal_gpr = riscv_instr_pkg::compressed_gpr;
    end else begin
      legal_gpr = riscv_instr_pkg::all_gpr;
    end
    if (format inside {CR_FORMAT, CI_FORMAT}) begin
      excluded_reg = {excluded_reg, ZERO};
    end
    if (excluded_reg.size() > 0) begin
      i = 0;
      while (i < legal_gpr.size()) begin
        if (legal_gpr[i] inside {excluded_reg}) begin
          legal_gpr.delete(i);
        end else begin
          i++;
        end
      end
    end
    `DV_CHECK_FATAL(legal_gpr.size() > 0)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(i, i < legal_gpr.size();)
    gpr = legal_gpr[i];
    return gpr;
  endfunction

  function riscv_fpr_t gen_rand_fpr(riscv_fpr_t excluded_reg[] = {});
    riscv_fpr_t fpr;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(fpr,
                                       if (excluded_reg.size() > 0) {
                                         !(fpr inside {excluded_reg});
                                       }
                                       if (is_compressed) {
                                         fpr inside {[F8:F15]};
                                       });
    return fpr;
  endfunction

  function void gen_rand_csr(bit illegal_csr_instr = 0,
                             bit enable_floating_point = 0,
                             privileged_mode_t privileged_mode = MACHINE_MODE);
    privileged_reg_t preg[$];
    if (illegal_csr_instr) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(csr, !(csr inside {implemented_csr});)
    end else begin
      // Use scratch register to avoid the side effect of modifying other privileged mode CSR.
      if (privileged_mode == MACHINE_MODE)
        preg = {MSCRATCH};
      else if (privileged_mode == SUPERVISOR_MODE)
        preg = {SSCRATCH};
      else
        preg = {USCRATCH};
      if (enable_floating_point) begin
        preg = {preg, FFLAGS, FRM, FCSR};
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(csr, csr inside {preg};)
      end else begin
        csr = preg[0];
      end
    end
  endfunction

  function new(string name = "");
    super.new(name);
  endfunction

  // Convert the instruction to one-liner print message
  virtual function string convert2string();
    return convert2asm();
  endfunction

  virtual function void do_print (uvm_printer printer);
    `uvm_info(get_type_name(), convert2string(), UVM_LOW)
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    if (is_floating_point) begin
      case (format)
        I_FORMAT:
          if (category == LOAD) begin
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fd.name(), get_imm(), rs1.name());
          end else if (instr_name inside {FMV_X_W, FMV_X_D, FCVT_W_S, FCVT_WU_S,
                                          FCVT_L_S, FCVT_LU_S, FCVT_L_D, FCVT_LU_D, FCVT_LU_S,
                                          FCVT_W_D, FCVT_WU_D}) begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), fs1.name());
          end else if (instr_name inside {FMV_W_X, FMV_D_X, FCVT_S_W, FCVT_S_WU,
                                          FCVT_S_L, FCVT_D_L, FCVT_S_LU, FCVT_D_W,
                                          FCVT_D_LU, FCVT_D_WU}) begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, fd.name(), rs1.name());
          end else begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, fd.name(), fs1.name());
          end
        S_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fs2.name(), get_imm(), rs1.name());
        R_FORMAT:
          if (category == COMPARE) begin
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), fs1.name(), fs2.name());
          end else if (instr_name inside {FCLASS_S, FCLASS_D}) begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), fs1.name());
          end else begin
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, fd.name(), fs1.name(), fs2.name());
          end
        R4_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s, %0s, %0s", asm_str, fd.name(), fs1.name(),
                                                       fs2.name(), fs3.name());
        CL_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fd.name(), get_imm(), rs1.name());
        CS_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, fs2.name(), get_imm(), rs1.name());
        default:
          `uvm_fatal(`gfn, $sformatf("Unsupported floating point format: %0s", format.name()))
      endcase
    end else if((category != SYSTEM) && !(group inside {RV32A, RV64A})) begin
      case(format)
        J_FORMAT, U_FORMAT : // instr rd,imm
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
        I_FORMAT: // instr rd,rs1,imm
          if(instr_name == NOP)
            asm_str = "nop";
          else if(instr_name == C_NOP)
            asm_str = "c.nop";
          else if(instr_name == WFI)
            asm_str = "wfi";
          else if(instr_name == FENCE)
            asm_str = $sformatf("fence"); // TODO: Support all fence combinations
          else if(instr_name == FENCE_I)
            asm_str = "fence.i";
          else if(category == LOAD) // Use psuedo instruction format
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
          else if(category == CSR)
            asm_str = $sformatf("%0s%0s, 0x%0x, %0s", asm_str, rd.name(), csr, get_imm());
          else
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), get_imm());
        S_FORMAT, B_FORMAT: // instr rs1,rs2,imm
          if(category == STORE) // Use psuedo instruction format
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rs1.name(), rs2.name(), get_imm());
        R_FORMAT: // instr rd,rs1,rs2
          if(category == CSR) begin
            asm_str = $sformatf("%0s%0s, 0x%0x, %0s", asm_str, rd.name(), csr, rs1.name());
          end else if(instr_name == SFENCE_VMA) begin
            asm_str = "sfence.vma x0, x0"; // TODO: Support all possible sfence
          end else begin
            asm_str = $sformatf("%0s%0s, %0s, %0s", asm_str, rd.name(), rs1.name(), rs2.name());
          end
        CI_FORMAT, CIW_FORMAT:
          if(instr_name == C_NOP)
            asm_str = "c.nop";
          else if(instr_name == C_ADDI16SP)
            asm_str = $sformatf("%0ssp, %0s", asm_str, get_imm());
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
        CL_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
        CS_FORMAT:
          if(category == STORE)
            asm_str = $sformatf("%0s%0s, %0s(%0s)", asm_str, rs2.name(), get_imm(), rs1.name());
          else
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), rs2.name());
        CA_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
        CB_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rs1.name(), get_imm());
        CSS_FORMAT:
          asm_str = $sformatf("%0s%0s, %0s", asm_str, rs2.name(), get_imm());
        CR_FORMAT:
          if (instr_name inside {C_JR, C_JALR}) begin
            asm_str = $sformatf("%0s%0s", asm_str, rs1.name());
          end else begin
            asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), rs2.name());
          end
        CJ_FORMAT:
          asm_str = $sformatf("%0s%0s", asm_str, get_imm());
      endcase
    end else if (group inside {RV32A, RV64A}) begin
      if (instr_name inside {LR_W, LR_D}) begin
        asm_str = $sformatf("%0s %0s, (%0s)", asm_str, rd.name(), rs1.name());
      end else begin
        asm_str = $sformatf("%0s %0s, %0s, (%0s)", asm_str, rd.name(), rs2.name(), rs1.name());
      end
    end else begin
      // For EBREAK,C.EBREAK, making sure pc+4 is a valid instruction boundary
      // This is needed to resume execution from epc+4 after ebreak handling
      if(instr_name == EBREAK) begin
        asm_str = ".4byte 0x00100073 # ebreak";
      end else if(instr_name == C_EBREAK) begin
        asm_str = "c.ebreak;c.nop;";
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
      ECALL, EBREAK, CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI   : get_opcode = 7'b1110011;
      ADDW, SUBW, SLLW, SRLW, SRAW, MULW, DIVW, DIVUW, REMW, REMUW : get_opcode = 7'b0111011;
      ECALL, EBREAK, URET, SRET, MRET, DRET, WFI, SFENCE_VMA       : get_opcode = 7'b1110011;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  // Get opcode for compressed instruction
  function bit [1:0] get_c_opcode();
    case (instr_name) inside
      C_ADDI4SPN, C_FLD, C_FLD, C_LQ, C_LW, C_FLW,
      C_LD, C_FSD, C_SQ, C_SW, C_FSW, C_SD            : get_c_opcode = 2'b00;
      C_NOP, C_ADDI, C_JAL, C_ADDIW, C_LI, C_ADDI16SP,
      C_LUI, C_SRLI, C_SRLI64, C_SRAI, C_SRAI64,
      C_ANDI, C_SUB, C_XOR, C_OR, C_AND, C_SUBW,
      C_ADDW, C_J, C_BEQZ, C_BNEZ                     : get_c_opcode = 2'b01;
      C_SLLI, C_SLLI64, C_FLDSP, C_LQSP, C_LWSP,
      C_FLWSP, C_LDSP, C_JR, C_MV, C_EBREAK, C_JALR,
      C_ADD, C_FSDSP, C_SQSP, C_SWSP, C_FSWSP, C_SDSP : get_c_opcode = 2'b10;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
    endcase
  endfunction

  function bit [2:0] get_func3();
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
      CSRRW      : get_func3 = 3'b001;
      CSRRS      : get_func3 = 3'b010;
      CSRRC      : get_func3 = 3'b011;
      CSRRWI     : get_func3 = 3'b101;
      CSRRSI     : get_func3 = 3'b110;
      CSRRCI     : get_func3 = 3'b111;
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
      C_ADDI4SPN : get_func3 = 3'b000;
      C_FLD      : get_func3 = 3'b001;
      C_LQ       : get_func3 = 3'b001;
      C_LW       : get_func3 = 3'b010;
      C_FLW      : get_func3 = 3'b011;
      C_LD       : get_func3 = 3'b011;
      C_FSD      : get_func3 = 3'b101;
      C_SQ       : get_func3 = 3'b101;
      C_SW       : get_func3 = 3'b110;
      C_FSW      : get_func3 = 3'b111;
      C_SD       : get_func3 = 3'b111;
      C_NOP      : get_func3 = 3'b000;
      C_ADDI     : get_func3 = 3'b000;
      C_JAL      : get_func3 = 3'b001;
      C_ADDIW    : get_func3 = 3'b001;
      C_LI       : get_func3 = 3'b010;
      C_ADDI16SP : get_func3 = 3'b011;
      C_LUI      : get_func3 = 3'b011;
      C_SRLI     : get_func3 = 3'b100;
      C_SRLI64   : get_func3 = 3'b100;
      C_SRAI     : get_func3 = 3'b100;
      C_SRAI64   : get_func3 = 3'b100;
      C_ANDI     : get_func3 = 3'b100;
      C_SUB      : get_func3 = 3'b100;
      C_XOR      : get_func3 = 3'b100;
      C_OR       : get_func3 = 3'b100;
      C_AND      : get_func3 = 3'b100;
      C_SUBW     : get_func3 = 3'b100;
      C_ADDW     : get_func3 = 3'b100;
      C_J        : get_func3 = 3'b101;
      C_BEQZ     : get_func3 = 3'b110;
      C_BNEZ     : get_func3 = 3'b111;
      C_SLLI     : get_func3 = 3'b000;
      C_SLLI64   : get_func3 = 3'b000;
      C_FLDSP    : get_func3 = 3'b001;
      C_LQSP     : get_func3 = 3'b001;
      C_LWSP     : get_func3 = 3'b010;
      C_FLWSP    : get_func3 = 3'b011;
      C_LDSP     : get_func3 = 3'b011;
      C_JR       : get_func3 = 3'b100;
      C_MV       : get_func3 = 3'b100;
      C_EBREAK   : get_func3 = 3'b100;
      C_JALR     : get_func3 = 3'b100;
      C_ADD      : get_func3 = 3'b100;
      C_FSDSP    : get_func3 = 3'b101;
      C_SQSP     : get_func3 = 3'b101;
      C_SWSP     : get_func3 = 3'b110;
      C_FSWSP    : get_func3 = 3'b111;
      C_SDSP     : get_func3 = 3'b111;
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
    if (!is_compressed) begin
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
          else if(category == CSR)
            binary = $sformatf("%8h", {csr[10:0], imm[4:0], get_func3(), rd, get_opcode()});
          else if(instr_name == ECALL)
            binary = $sformatf("%8h", {get_func7(), 18'b0, get_opcode()});
          else if(instr_name inside {URET, SRET, MRET})
            binary = $sformatf("%8h", {get_func7(), 5'b10, 13'b0, get_opcode()});
          else if(instr_name inside {DRET})
            binary = $sformatf("%8h", {get_func7(), 5'b10010, 13'b0, get_opcode()});
          else if(instr_name == EBREAK)
            binary = $sformatf("%8h", {get_func7(), 5'b01, 13'b0, get_opcode()});
          else if(instr_name == WFI)
            binary = $sformatf("%8h", {get_func7(), 5'b101, 13'b0, get_opcode()});
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
          if(category == CSR)
            binary = $sformatf("%8h", {csr[10:0], rs1, get_func3(), rd, get_opcode()});
          else if(instr_name == SFENCE_VMA)
            binary = $sformatf("%8h", {get_func7(), 18'b0, get_opcode()});
          else
            binary = $sformatf("%8h", {get_func7(), rs2, rs1, get_func3(), rd, get_opcode()});
        end
      endcase
    end else begin
      case (instr_name) inside
        C_ADDI4SPN:
          binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[9:6],
                                     imm[2], imm[3], get_c_gpr(rd), get_c_opcode()});
        C_LQ:
          binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[8],
                                     get_c_gpr(rs1), imm[7:6], get_c_gpr(rd), get_c_opcode()});
        C_FLD, C_LD:
          binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                     imm[7:6], get_c_gpr(rd), get_c_opcode()});
        C_LW, C_FLW:
          binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                     imm[2], imm[6], get_c_gpr(rd), get_c_opcode()});
        C_SQ:
          binary = $sformatf("%4h", {get_func3(), imm[5:4], imm[8],
                                     get_c_gpr(rs1), imm[7:6], get_c_gpr(rs2), get_c_opcode()});
        C_FSD, C_SD:
          binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                     imm[7:6], get_c_gpr(rs2), get_c_opcode()});
        C_SW, C_FSW:
          binary = $sformatf("%4h", {get_func3(), imm[5:3], get_c_gpr(rs1),
                                     imm[2], imm[6], get_c_gpr(rs2), get_c_opcode()});
        C_NOP, C_ADDI, C_LI, C_ADDIW:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
        C_JAL, C_J:
          binary = $sformatf("%4h", {get_func3(), imm[11], imm[4], imm[9:8],
                                     imm[10], imm[6], imm[7], imm[3:1], imm[5], get_c_opcode()});
        C_ADDI16SP:
          binary = $sformatf("%4h", {get_func3(), imm[9], 5'b10,
                                     imm[4], imm[6], imm[8:7], imm[5], get_c_opcode()});
        C_LUI:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
        C_SRLI:
          binary = $sformatf("%4h", {get_func3(), imm[5],
                                     2'b0, get_c_gpr(rd), imm[4:0], get_c_opcode()});
        C_SRLI64:
          binary = $sformatf("%4h", {get_func3(), 3'b0, get_c_gpr(rd), 5'b0, get_c_opcode()});
        C_SRAI:
          binary = $sformatf("%4h", {get_func3(), imm[5],
                                     2'b01, get_c_gpr(rd), imm[4:0], get_c_opcode()});
        C_SRAI64:
          binary = $sformatf("%4h", {get_func3(), 3'b001,
                                     get_c_gpr(rd), 5'b0, get_c_opcode()});
        C_ANDI:
          binary = $sformatf("%4h", {get_func3(), imm[5],
                                     2'b10, get_c_gpr(rd), imm[4:0], get_c_opcode()});
        C_SUB:
          binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                     2'b00, get_c_gpr(rs2), get_c_opcode()});
        C_XOR:
          binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                     2'b01, get_c_gpr(rs2), get_c_opcode()});
        C_OR:
          binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                     2'b10, get_c_gpr(rs2), get_c_opcode()});
        C_AND:
          binary = $sformatf("%4h", {get_func3(), 3'b011, get_c_gpr(rd),
                                     2'b11, get_c_gpr(rs2), get_c_opcode()});
        C_SUBW:
          binary = $sformatf("%4h", {get_func3(), 3'b111, get_c_gpr(rd),
                                     2'b00, get_c_gpr(rs2), get_c_opcode()});
        C_ADDW:
          binary = $sformatf("%4h", {get_func3(), 3'b111, get_c_gpr(rd),
                                     2'b01, get_c_gpr(rs2), get_c_opcode()});
        C_BEQZ, C_BNEZ:
          binary = $sformatf("%4h", {get_func3(), imm[8], imm[4:3],
                                     get_c_gpr(rs1), imm[7:6], imm[2:1], imm[5], get_c_opcode()});
        C_SLLI:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:0], get_c_opcode()});
        C_SLLI64:
          binary = $sformatf("%4h", {get_func3(), 1'b0, rd, 5'b0, get_c_opcode()});
        C_FLDSP, C_LDSP:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:3], imm[8:6], get_c_opcode()});
        C_LQSP:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4], imm[9:6], get_c_opcode()});
        C_LWSP, C_FLWSP:
          binary = $sformatf("%4h", {get_func3(), imm[5], rd, imm[4:2], imm[7:6], get_c_opcode()});
        C_JR:
          binary = $sformatf("%4h", {get_func3(), 1'b0, rs1, 5'b0, get_c_opcode()});
        C_MV:
          binary = $sformatf("%4h", {get_func3(), 1'b0, rd, rs2, get_c_opcode()});
        C_EBREAK:
          binary = $sformatf("%4h", {get_func3(), 1'b1, 10'b0, get_c_opcode()});
        C_JALR:
          binary = $sformatf("%4h", {get_func3(), 1'b1, 10'b0, get_c_opcode()});
        C_ADD:
          binary = $sformatf("%4h", {get_func3(), 1'b1, rd, rs2, get_c_opcode()});
        C_FSDSP, C_SDSP:
          binary = $sformatf("%4h", {get_func3(), 1'b0, imm[5:3], imm[8:6], rs2, get_c_opcode()});
        C_SQSP:
          binary = $sformatf("%4h", {get_func3(), 1'b0, imm[5:4], imm[9:6], rs2, get_c_opcode()});
        C_SWSP, C_FSWSP:
          binary = $sformatf("%4h", {get_func3(), 1'b0, imm[5:2], imm[7:6], rs2, get_c_opcode()});
        default : `uvm_fatal(`gfn, $sformatf("Unsupported instruction %0s", instr_name.name()))
      endcase
    end
    return {prefix, binary};
  endfunction

  virtual function string get_instr_name();
    get_instr_name = instr_name.name();
    if(get_instr_name.substr(0, 1) == "C_") begin
      get_instr_name = {"c.", get_instr_name.substr(2, get_instr_name.len() - 1)};
    end else if (group == RV32A) begin
      get_instr_name = {get_instr_name.substr(0, get_instr_name.len() - 3), ".w"};
      get_instr_name = aq ? {get_instr_name, ".aq"} :
                       rl ? {get_instr_name, ".rl"} : get_instr_name;
    end else if (group == RV64A) begin
      get_instr_name = {get_instr_name.substr(0, get_instr_name.len() - 3), ".d"};
      get_instr_name = aq ? {get_instr_name, ".aq"} :
                       rl ? {get_instr_name, ".rl"} : get_instr_name;
    end else if (group inside {RV32F, RV64F, RV32D, RV64D}) begin
      foreach(get_instr_name[i]) begin
        if (get_instr_name[i] == "_") begin
          get_instr_name[i] = ".";
        end
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

  // Copy the rand fields of the base instruction
  virtual function void copy_base_instr(riscv_instr_base obj);
    this.group             = obj.group;
    this.format            = obj.format;
    this.category          = obj.category;
    this.instr_name        = obj.instr_name;
    this.rs2               = obj.rs2;
    this.rs1               = obj.rs1;
    this.rd                = obj.rd;
    this.imm               = obj.imm;
    this.imm_type          = obj.imm_type;
    this.imm_len           = obj.imm_len;
    this.imm_mask          = obj.imm_mask;
    this.imm_str           = obj.imm_str;
    this.is_pseudo_instr   = obj.is_pseudo_instr;
    this.aq                = obj.aq;
    this.rl                = obj.rl;
    this.is_compressed     = obj.is_compressed;
    this.has_imm           = obj.has_imm;
    this.has_rs1           = obj.has_rs1;
    this.has_rs2           = obj.has_rs2;
    this.has_rd            = obj.has_rd;
    this.fs3               = obj.fs3;
    this.fs2               = obj.fs2;
    this.fs1               = obj.fs1;
    this.fd                = obj.fd;
    this.has_fs1           = obj.has_fs1;
    this.has_fs2           = obj.has_fs2;
    this.has_fs3           = obj.has_fs3;
    this.has_fd            = obj.has_fd;
    this.is_floating_point = obj.is_floating_point;
  endfunction

endclass

// Psuedo instructions are used to simplify assembly program writing
class riscv_pseudo_instr extends riscv_instr_base;

  rand riscv_pseudo_instr_name_t  pseudo_instr_name;

  constraint default_c {
    is_pseudo_instr == 1'b1;
  }

  `add_pseudo_instr(LI,    I_FORMAT, LOAD, RV32I)
  `add_pseudo_instr(LA,    I_FORMAT, LOAD, RV32I)

  `uvm_object_utils(riscv_pseudo_instr)

  function new(string name = "");
    super.new(name);
    process_load_store = 0;
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    asm_str = format_string(get_instr_name(), MAX_INSTR_STR_LEN);
    // instr rd,imm
    asm_str = $sformatf("%0s%0s, %0s", asm_str, rd.name(), get_imm());
    if(comment != "")
      asm_str = {asm_str, " #",comment};
    return asm_str.tolower();
  endfunction

  virtual function string get_instr_name();
    return pseudo_instr_name.name();
  endfunction

endclass
