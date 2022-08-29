/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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


module riscv.gen.riscv_instr_pkg;

import riscv.gen.target: XLEN, NUM_HARTS, SATP_MODE, implemented_csr;
import std.traits: EnumMembers;

import esdl.data.bvec: bvec, ubvec;
import esdl.rand: rand;
import uvm;

// Data section setting

// use uvm_cmdline_processor.get_inst() directly
// uvm_cmdline_processor  inst;


struct mem_region_t
{
  string     name;
  uint       size_in_bytes;
  ubvec!3    xwr; // Excutable,Writable,Readale
}

enum vreg_init_method_t: ubyte {
  SAME_VALUES_ALL_ELEMS,
  RANDOM_VALUES_VMV,
  RANDOM_VALUES_LOAD
}

enum satp_mode_t: ubyte {
  BARE = 0b0000,
  SV32 = 0b0001,
  SV39 = 0b1000,
  SV48 = 0b1001,
  SV57 = 0b1010,
  SV64 = 0b1011
}

enum f_rounding_mode_t: ubyte {
  RNE = 0b000,
  RTZ = 0b001,
  RDN = 0b010,
  RUP = 0b011,
  RMM = 0b100
}

enum mtvec_mode_t: ubyte {
  DIRECT   = 0b00,
  VECTORED = 0b01
}

enum imm_t: ubyte {
  IMM,    // Signed immediate
  UIMM,   // Unsigned immediate
  NZUIMM, // Non-zero unsigned immediate
  NZIMM   // Non-zero signed immediate
}

// Privileged mode
enum privileged_mode_t: ubyte {
  USER_MODE       = 0b00,
  SUPERVISOR_MODE = 0b01,
  RESERVED_MODE   = 0b10,
  MACHINE_MODE    = 0b11
}

enum riscv_instr_group_t: ubyte {
  RV32I,
  RV64I,
  RV32M,
  RV64M,
  RV32A,
  RV64A,
  RV32F,
  RV32FC,
  RV64F,
  RV32D,
  RV32DC,
  RV64D,
  RV32C,
  RV64C,
  RV128I,
  RV128C,
  RVV,
  RV32B,
  RV32ZBA,
  RV32ZBB,
  RV32ZBC,
  RV32ZBS,
  RV64B,
  RV64ZBA,
  RV64ZBB,
  RV64ZBC,
  RV64ZBS,
  RV32X,
  RV64X
}


enum riscv_instr_name_t: ushort  {
  // RV32I instructions
  LUI,
  AUIPC,
  JAL,
  JALR,
  BEQ,
  BNE,
  BLT,
  BGE,
  BLTU,
  BGEU,
  LB,
  LH,
  LW,
  LBU,
  LHU,
  SB,
  SH,
  SW,
  ADDI,
  SLTI,
  SLTIU,
  XORI,
  ORI,
  ANDI,
  SLLI,
  SRLI,
  SRAI,
  ADD,
  SUB,
  SLL,
  SLT,
  SLTU,
  XOR,
  SRL,
  SRA,
  OR,
  AND,
  NOP,
  FENCE,
  FENCE_I,
  ECALL,
  EBREAK,
  CSRRW,
  CSRRS,
  CSRRC,
  CSRRWI,
  CSRRSI,
  CSRRCI,
  // RV32ZBA instructions
  SH1ADD,
  SH2ADD,
  SH3ADD,
  // RV32ZBB instructions
  ANDN,
  CLZ,
  CPOP,
  CTZ,
  MAX,
  MAXU,
  MIN,
  MINU,
  ORC_B,
  ORN,
  REV8,
  ROL,
  ROR,
  RORI,
  SEXT_B,
  SEXT_H,
  XNOR,
  ZEXT_H,
  // RV32ZBC instructions
  CLMUL,
  CLMULH,
  CLMULR,
  // RV32ZBS instructions
  BCLR,
  BCLRI,
  BEXT,
  BEXTI,
  BINV,
  BINVI,
  BSET,
  BSETI,
  // RV32B instructions
  // Remaining bitmanip instructions of draft v.0.93 not ratified in v.1.00 (Zba, Zbb, Zbc, Zbs).
  GORC,
  GORCI,
  CMIX,
  CMOV,
  PACK,
  PACKU,
  PACKH,
  XPERM_N,
  XPERM_B,
  XPERM_H,
  SLO,
  SRO,
  SLOI,
  SROI,
  GREV,
  GREVI,
  FSL,
  FSR,
  FSRI,
  CRC32_B,
  CRC32_H,
  CRC32_W,
  CRC32C_B,
  CRC32C_H,
  CRC32C_W,
  SHFL,
  UNSHFL,
  SHFLI,
  UNSHFLI,
  BCOMPRESS,
  BDECOMPRESS,
  BFP,
  // RV64ZBA instructions
  ADD_UW,
  SH1ADD_UW,
  SH2ADD_UW,
  SH3ADD_UW,
  SLLI_UW,
  // RV64ZBB instructions
  CLZW,
  CPOPW,
  CTZW,
  ROLW,
  RORW,
  RORIW,
  //RV64B instructions
  // Remaining bitmanip instructions of draft v.0.93 not ratified in v.1.00 (Zba, Zbb, Zbc, Zbs).
  BMATOR,
  BMATXOR,
  BMATFLIP,
  CRC32_D,
  CRC32C_D,
  SHFLW,
  UNSHFLW,
  BCOMPRESSW,
  BDECOMPRESSW,
  BFPW,
  SLOW,
  SROW,
  SLOIW,
  SROIW,
  GREVW,
  GREVIW,
  FSLW,
  FSRW,
  FSRIW,
  GORCW,
  GORCIW,
  PACKW,
  PACKUW,
  XPERM_W,
  // RV32M instructions
  MUL,
  MULH,
  MULHSU,
  MULHU,
  DIV,
  DIVU,
  REM,
  REMU,
  // RV64M instructions
  MULW,
  DIVW,
  DIVUW,
  REMW,
  REMUW,
  // RV32F instructions
  FLW,
  FSW,
  FMADD_S,
  FMSUB_S,
  FNMSUB_S,
  FNMADD_S,
  FADD_S,
  FSUB_S,
  FMUL_S,
  FDIV_S,
  FSQRT_S,
  FSGNJ_S,
  FSGNJN_S,
  FSGNJX_S,
  FMIN_S,
  FMAX_S,
  FCVT_W_S,
  FCVT_WU_S,
  FMV_X_W,
  FEQ_S,
  FLT_S,
  FLE_S,
  FCLASS_S,
  FCVT_S_W,
  FCVT_S_WU,
  FMV_W_X,
  // RV64F instruction
  FCVT_L_S,
  FCVT_LU_S,
  FCVT_S_L,
  FCVT_S_LU,
  // RV32D instructions
  FLD,
  FSD,
  FMADD_D,
  FMSUB_D,
  FNMSUB_D,
  FNMADD_D,
  FADD_D,
  FSUB_D,
  FMUL_D,
  FDIV_D,
  FSQRT_D,
  FSGNJ_D,
  FSGNJN_D,
  FSGNJX_D,
  FMIN_D,
  FMAX_D,
  FCVT_S_D,
  FCVT_D_S,
  FEQ_D,
  FLT_D,
  FLE_D,
  FCLASS_D,
  FCVT_W_D,
  FCVT_WU_D,
  FCVT_D_W,
  FCVT_D_WU,
  // RV64D
  FCVT_L_D,
  FCVT_LU_D,
  FMV_X_D,
  FCVT_D_L,
  FCVT_D_LU,
  FMV_D_X,
  // RV64I
  LWU,
  LD,
  SD,
  ADDIW,
  SLLIW,
  SRLIW,
  SRAIW,
  ADDW,
  SUBW,
  SLLW,
  SRLW,
  SRAW,
  // RV32C
  C_LW,
  C_SW,
  C_LWSP,
  C_SWSP,
  C_ADDI4SPN,
  C_ADDI,
  C_LI,
  C_ADDI16SP,
  C_LUI,
  C_SRLI,
  C_SRAI,
  C_ANDI,
  C_SUB,
  C_XOR,
  C_OR,
  C_AND,
  C_BEQZ,
  C_BNEZ,
  C_SLLI,
  C_MV,
  C_EBREAK,
  C_ADD,
  C_NOP,
  C_J,
  C_JAL,
  C_JR,
  C_JALR,
  // RV64C
  C_ADDIW,
  C_SUBW,
  C_ADDW,
  C_LD,
  C_SD,
  C_LDSP,
  C_SDSP,
  // RV128C
  C_SRLI64,
  C_SRAI64,
  C_SLLI64,
  C_LQ,
  C_SQ,
  C_LQSP,
  C_SQSP,
  // RV32FC
  C_FLW,
  C_FSW,
  C_FLWSP,
  C_FSWSP,
  // RV32DC
  C_FLD,
  C_FSD,
  C_FLDSP,
  C_FSDSP,
  // RV32A
  LR_W,
  SC_W,
  AMOSWAP_W,
  AMOADD_W,
  AMOAND_W,
  AMOOR_W,
  AMOXOR_W,
  AMOMIN_W,
  AMOMAX_W,
  AMOMINU_W,
  AMOMAXU_W,
  // RV64A
  LR_D,
  SC_D,
  AMOSWAP_D,
  AMOADD_D,
  AMOAND_D,
  AMOOR_D,
  AMOXOR_D,
  AMOMIN_D,
  AMOMAX_D,
  AMOMINU_D,
  AMOMAXU_D,
  // Vector instructions
  VSETVL,
  VSETVLI,
  VADD,
  VSUB,
  VRSUB,
  VWADDU,
  VWSUBU,
  VWADD,
  VWSUB,
  VADC,
  VMADC,
  VSBC,
  VMSBC,
  VAND,
  VOR,
  VXOR,
  VSLL,
  VSRL,
  VSRA,
  VNSRL,
  VNSRA,
  VMSEQ,
  VMSNE,
  VMSLTU,
  VMSLT,
  VMSLEU,
  VMSLE,
  VMSGTU,
  VMSGT,
  VMINU,
  VMIN,
  VMAXU,
  VMAX,
  VMUL,
  VMULH,
  VMULHU,
  VMULHSU,
  VDIVU,
  VDIV,
  VREMU,
  VREM,
  VWMUL,
  VWMULU,
  VWMULSU,
  VMACC,
  VNMSAC,
  VMADD,
  VNMSUB,
  VWMACCU,
  VWMACC,
  VWMACCSU,
  VWMACCUS,
  //VQMACCU,
  //VQMACC,
  //VQMACCSU,
  //VQMACCUS,
  VMERGE,
  VMV,
  VSADDU,
  VSADD,
  VSSUBU,
  VSSUB,
  VAADDU,
  VAADD,
  VASUBU,
  VASUB,
  VSSRL,
  VSSRA,
  VNCLIPU,
  VNCLIP,
  // 14. Vector Floating-Point Instructions
  VFADD,
  VFSUB,
  VFRSUB,
  VFMUL,
  VFDIV,
  VFRDIV,
  VFWMUL,
  VFMACC,
  VFNMACC,
  VFMSAC,
  VFNMSAC,
  VFMADD,
  VFNMADD,
  VFMSUB,
  VFNMSUB,
  VFWMACC,
  VFWNMACC,
  VFWMSAC,
  VFWNMSAC,
  VFSQRT_V,
  VFMIN,
  VFMAX,
  VFSGNJ,
  VFSGNJN,
  VFSGNJX,
  VMFEQ,
  VMFNE,
  VMFLT,
  VMFLE,
  VMFGT,
  VMFGE,
  VFCLASS_V,
  VFMERGE,
  VFMV,
  VFCVT_XU_F_V,
  VFCVT_X_F_V,
  VFCVT_F_XU_V,
  VFCVT_F_X_V,
  VFWCVT_XU_F_V,
  VFWCVT_X_F_V,
  VFWCVT_F_XU_V,
  VFWCVT_F_X_V,
  VFWCVT_F_F_V,
  VFNCVT_XU_F_W,
  VFNCVT_X_F_W,
  VFNCVT_F_XU_W,
  VFNCVT_F_X_W,
  VFNCVT_F_F_W,
  VFNCVT_ROD_F_F_W,
  // 15. Vector reduction instruction
  VREDSUM_VS,
  VREDMAXU_VS,
  VREDMAX_VS,
  VREDMINU_VS,
  VREDMIN_VS,
  VREDAND_VS,
  VREDOR_VS,
  VREDXOR_VS,
  VWREDSUMU_VS,
  VWREDSUM_VS,
  VFREDOSUM_VS,
  VFREDSUM_VS,
  VFREDMAX_VS,
  VFWREDOSUM_VS,
  VFWREDSUM_VS,
  // Vector mask instruction
  VMAND_MM,
  VMNAND_MM,
  VMANDNOT_MM,
  VMXOR_MM,
  VMOR_MM,
  VMNOR_MM,
  VMORNOT_MM,
  VMXNOR_MM,
  VPOPC_M,
  VFIRST_M,
  VMSBF_M,
  VMSIF_M,
  VMSOF_M,
  VIOTA_M,
  VID_V,
  // Vector permutation instruction
  VMV_X_S,
  VMV_S_X,
  VFMV_F_S,
  VFMV_S_F,
  VSLIDEUP,
  VSLIDEDOWN,
  VSLIDE1UP,
  VSLIDE1DOWN,
  VRGATHER,
  VCOMPRESS,
  VMV1R_V,
  VMV2R_V,
  VMV4R_V,
  VMV8R_V,
  // Vector load/store instruction
  VLE_V,
  VSE_V,
  VLSE_V,
  VSSE_V,
  VLXEI_V,
  VSXEI_V,
  VSUXEI_V,
  VLEFF_V,
  // Segmented load/store instruction
  VLSEGE_V,
  VSSEGE_V,
  VLSEGEFF_V,
  VLSSEGE_V,
  VSSSEGE_V,
  VLXSEGEI_V,
  VSXSEGEI_V,
  VSUXSEGEI_V,
  // Vector AMO instruction
  // EEW vector AMOs
  VAMOSWAPE_V,
  VAMOADDE_V,
  VAMOXORE_V,
  VAMOANDE_V,
  VAMOORE_V,
  VAMOMINE_V,
  VAMOMAXE_V,
  VAMOMINUE_V,
  VAMOMAXUE_V,
  // Supervisor instruction
  DRET,
  MRET,
  URET,
  SRET,
  WFI,
  SFENCE_VMA,
  // Custom instructions
  // `include "isa/custom/riscv_custom_instr_enum.sv"
  // You can add other instructions here
  INVALID_INSTR
}

// Maximum virtual address bits used by the program
enum uint MAX_USED_VADDR_BITS = 30;

enum uint SINGLE_PRECISION_FRACTION_BITS = 23;
enum uint DOUBLE_PRECISION_FRACTION_BITS = 52;


enum riscv_reg_t: ubyte {	// 5'b
  ZERO = 0b00000,
  RA, SP, GP, TP, T0, T1, T2, S0, S1, A0, A1, A2, A3, A4, A5, A6, A7,
  S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, T3, T4, T5, T6
}

enum riscv_fpr_t: ubyte { 	// 5'b
  FT0, FT1, FT2, FT3, FT4, FT5, FT6, FT7, FS0, FS1, FA0, FA1, FA2, FA3, FA4, FA5,
  FA6, FA7, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11, FT8, FT9, FT10, FT11
}

enum riscv_vreg_t: ubyte {
  V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15,
  V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31
}


enum riscv_instr_format_t: ubyte {	// 6'b
  J_FORMAT = 0,
  U_FORMAT,
  I_FORMAT,
  B_FORMAT,
  R_FORMAT,
  S_FORMAT,
  R4_FORMAT,
  // Compressed instruction format
  CI_FORMAT,
  CB_FORMAT,
  CJ_FORMAT,
  CR_FORMAT,
  CA_FORMAT,
  CL_FORMAT,
  CS_FORMAT,
  CSS_FORMAT,
  CIW_FORMAT,
  // Vector instruction format
  VSET_FORMAT,
  VA_FORMAT,
  VS2_FORMAT, // op vd,vs2
  VL_FORMAT,
  VS_FORMAT,
  VLX_FORMAT,
  VSX_FORMAT,
  VLS_FORMAT,
  VSS_FORMAT,
  VAMO_FORMAT
}


// Vector arithmetic instruction variant
enum va_variant_t: ubyte {
  VV,
  VI,
  VX,
  VF,
  WV,
  WI,
  WX,
  VVM,
  VIM,
  VXM,
  VFM,
  VS,
  VM
}

enum riscv_instr_category_t: ubyte {	// 6'b
  LOAD = 0,
  STORE,
  SHIFT,
  ARITHMETIC,
  LOGICAL,
  COMPARE,
  BRANCH,
  JUMP,
  SYNCH,
  SYSTEM,
  COUNTER,
  CSR,
  CHANGELEVEL,
  TRAP,
  INTERRUPT,
  // `VECTOR_INCLUDE("riscv_instr_pkg_inc_riscv_instr_category_t.sv")
  AMO // (last one)
}

alias riscv_csr_t = ubvec!12;

enum privileged_reg_t: ushort {	// 12'b
    // User mode register
    USTATUS         = 0x000,  // User status
    UIE             = 0x004,  // User interrupt-enable register
    UTVEC           = 0x005,  // User trap-handler base address
    USCRATCH        = 0x040,  // Scratch register for user trap handlers
    UEPC            = 0x041,  // User exception program counter
    UCAUSE          = 0x042,  // User trap cause
    UTVAL           = 0x043,  // User bad address or instruction
    UIP             = 0x044,  // User interrupt pending
    // Unprivileged Floating-Point CSRs
    FFLAGS          = 0x001,  // Floating-Point Accrued Exceptions
    FRM             = 0x002,  // Floating-Point Dynamic Rounding Mode
    FCSR            = 0x003,  // Floating-Point Control/Status Register (FRM + FFLAGS)
    // Unprivileged Counter/Timers
    CYCLE           = 0xC00,  // Cycle counter for RDCYCLE instruction
    TIME            = 0xC01,  // Timer for RDTIME instruction
    INSTRET         = 0xC02,  // Instructions-retired counter for RDINSTRET instruction
    HPMCOUNTER3     = 0xC03,  // Performance-monitoring counter
    HPMCOUNTER4     = 0xC04,  // Performance-monitoring counter
    HPMCOUNTER5     = 0xC05,  // Performance-monitoring counter
    HPMCOUNTER6     = 0xC06,  // Performance-monitoring counter
    HPMCOUNTER7     = 0xC07,  // Performance-monitoring counter
    HPMCOUNTER8     = 0xC08,  // Performance-monitoring counter
    HPMCOUNTER9     = 0xC09,  // Performance-monitoring counter
    HPMCOUNTER10    = 0xC0A,  // Performance-monitoring counter
    HPMCOUNTER11    = 0xC0B,  // Performance-monitoring counter
    HPMCOUNTER12    = 0xC0C,  // Performance-monitoring counter
    HPMCOUNTER13    = 0xC0D,  // Performance-monitoring counter
    HPMCOUNTER14    = 0xC0E,  // Performance-monitoring counter
    HPMCOUNTER15    = 0xC0F,  // Performance-monitoring counter
    HPMCOUNTER16    = 0xC10,  // Performance-monitoring counter
    HPMCOUNTER17    = 0xC11,  // Performance-monitoring counter
    HPMCOUNTER18    = 0xC12,  // Performance-monitoring counter
    HPMCOUNTER19    = 0xC13,  // Performance-monitoring counter
    HPMCOUNTER20    = 0xC14,  // Performance-monitoring counter
    HPMCOUNTER21    = 0xC15,  // Performance-monitoring counter
    HPMCOUNTER22    = 0xC16,  // Performance-monitoring counter
    HPMCOUNTER23    = 0xC17,  // Performance-monitoring counter
    HPMCOUNTER24    = 0xC18,  // Performance-monitoring counter
    HPMCOUNTER25    = 0xC19,  // Performance-monitoring counter
    HPMCOUNTER26    = 0xC1A,  // Performance-monitoring counter
    HPMCOUNTER27    = 0xC1B,  // Performance-monitoring counter
    HPMCOUNTER28    = 0xC1C,  // Performance-monitoring counter
    HPMCOUNTER29    = 0xC1D,  // Performance-monitoring counter
    HPMCOUNTER30    = 0xC1E,  // Performance-monitoring counter
    HPMCOUNTER31    = 0xC1F,  // Performance-monitoring counter
    CYCLEH          = 0xC80,  // Upper 32 bits of CYCLE, RV32I only
    TIMEH           = 0xC81,  // Upper 32 bits of TIME, RV32I only
    INSTRETH        = 0xC82,  // Upper 32 bits of INSTRET, RV32I only
    HPMCOUNTER3H    = 0xC83,  // Upper 32 bits of HPMCOUNTER3, RV32I only
    HPMCOUNTER4H    = 0xC84,  // Upper 32 bits of HPMCOUNTER4, RV32I only
    HPMCOUNTER5H    = 0xC85,  // Upper 32 bits of HPMCOUNTER5, RV32I only
    HPMCOUNTER6H    = 0xC86,  // Upper 32 bits of HPMCOUNTER6, RV32I only
    HPMCOUNTER7H    = 0xC87,  // Upper 32 bits of HPMCOUNTER7, RV32I only
    HPMCOUNTER8H    = 0xC88,  // Upper 32 bits of HPMCOUNTER8, RV32I only
    HPMCOUNTER9H    = 0xC89,  // Upper 32 bits of HPMCOUNTER9, RV32I only
    HPMCOUNTER10H   = 0xC8A,  // Upper 32 bits of HPMCOUNTER10, RV32I only
    HPMCOUNTER11H   = 0xC8B,  // Upper 32 bits of HPMCOUNTER11, RV32I only
    HPMCOUNTER12H   = 0xC8C,  // Upper 32 bits of HPMCOUNTER12, RV32I only
    HPMCOUNTER13H   = 0xC8D,  // Upper 32 bits of HPMCOUNTER13, RV32I only
    HPMCOUNTER14H   = 0xC8E,  // Upper 32 bits of HPMCOUNTER14, RV32I only
    HPMCOUNTER15H   = 0xC8F,  // Upper 32 bits of HPMCOUNTER15, RV32I only
    HPMCOUNTER16H   = 0xC90,  // Upper 32 bits of HPMCOUNTER16, RV32I only
    HPMCOUNTER17H   = 0xC91,  // Upper 32 bits of HPMCOUNTER17, RV32I only
    HPMCOUNTER18H   = 0xC92,  // Upper 32 bits of HPMCOUNTER18, RV32I only
    HPMCOUNTER19H   = 0xC93,  // Upper 32 bits of HPMCOUNTER19, RV32I only
    HPMCOUNTER20H   = 0xC94,  // Upper 32 bits of HPMCOUNTER20, RV32I only
    HPMCOUNTER21H   = 0xC95,  // Upper 32 bits of HPMCOUNTER21, RV32I only
    HPMCOUNTER22H   = 0xC96,  // Upper 32 bits of HPMCOUNTER22, RV32I only
    HPMCOUNTER23H   = 0xC97,  // Upper 32 bits of HPMCOUNTER23, RV32I only
    HPMCOUNTER24H   = 0xC98,  // Upper 32 bits of HPMCOUNTER24, RV32I only
    HPMCOUNTER25H   = 0xC99,  // Upper 32 bits of HPMCOUNTER25, RV32I only
    HPMCOUNTER26H   = 0xC9A,  // Upper 32 bits of HPMCOUNTER26, RV32I only
    HPMCOUNTER27H   = 0xC9B,  // Upper 32 bits of HPMCOUNTER27, RV32I only
    HPMCOUNTER28H   = 0xC9C,  // Upper 32 bits of HPMCOUNTER28, RV32I only
    HPMCOUNTER29H   = 0xC9D,  // Upper 32 bits of HPMCOUNTER29, RV32I only
    HPMCOUNTER30H   = 0xC9E,  // Upper 32 bits of HPMCOUNTER30, RV32I only
    HPMCOUNTER31H   = 0xC9F,  // Upper 32 bits of HPMCOUNTER31, RV32I only
    // Supervisor mode register
    // Supervisor Trap Setup
    SSTATUS         = 0x100,  // Supervisor status
    SEDELEG         = 0x102,  // Supervisor exception delegation register
    SIDELEG         = 0x103,  // Supervisor interrupt delegation register
    SIE             = 0x104,  // Supervisor interrupt-enable register
    STVEC           = 0x105,  // Supervisor trap-handler base address
    SCOUNTEREN      = 0x106,  // Supervisor counter enable
    // Supervisor Configuration
    SENVCFG         = 0x10A,  // Supervisor environment configuration register
    // Supervisor Trap Handling
    SSCRATCH        = 0x140,  // Scratch register for supervisor trap handlers
    SEPC            = 0x141,  // Supervisor exception program counter
    SCAUSE          = 0x142,  // Supervisor trap cause
    STVAL           = 0x143,  // Supervisor bad address or instruction
    SIP             = 0x144,  // Supervisor interrupt pending
    // Supervisor Protection and Translation
    SATP            = 0x180,  // Supervisor address translation and protection
    // Supervisor Debug/Trace Register
    SCONTEXT        = 0x5A8,  // Supervisor environment configuration register.
    // Hypervisor Trap Setup register
    HSTATUS         = 0x600,  // Hypervisor status register
    HEDELEG         = 0x602,  // Hypervisor exception delegation register
    HIDELEG         = 0x603,  // Hypervisor interrupt delegation register
    HIE             = 0x604,  // Hypervisor interrupt-enable register
    HCOUNTEREN      = 0x606,  // Hypervisor counter enable
    HGEIE           = 0x607,  // Hypervisor guest external interrupt-enable register
    // Hypervisor Trap Handling
    HTVAL           = 0x643,  // Hypervisor bad guest physical address
    HIP             = 0x644,  // Hypervisor interrupt pending
    HVIP            = 0x645,  // Hypervisor virtual interrupt pending
    HTINST          = 0x64A,  // Hypervisor trap instruction (transformed)
    HGEIP           = 0xE12,  // Hypervisor guest external interrupt pending
    // Hypervisor configuration
    HENVCFG         = 0x60A,  // Hypervisor environment configuration register
    HENVCFGH        = 0x61A,  // Additional hypervisor env. conf. register, RV32 only
    // Hypervisor guest address translation and protection
    HGATP           = 0x680,  // Hypervisor guest address translation and protection
    // Hypervisor Debug/Trace registers
    HCONTEXT        = 0x6A8,  // Hypervisor-mode context register
    // Hypervisor Counter/Timer Virtualization Registers
    HTIMEDELTA      = 0x605,  // Delta for VS/VU-mode timer
    HTIMEDELTAH     = 0x615,  // Upper 32 bits of htimedelta, HSXLEN=32 only
    // Virtual Supervisor Registers
    VSSTATUS        = 0x200,  // Virtual supervisor status register
    VSIE            = 0x204,  // Virtual supervisor interrupt-enable register
    VSTVEC          = 0x205,  // Virtual supervisor trap handler base address
    VSSCRATCH       = 0x240,  // Virtual supervisor scratch register
    VSEPC           = 0x241,  // Virtual supervisor exception program counter
    VSCAUSE         = 0x242,  // Virtual supervisor trap cause
    VSTVAL          = 0x243,  // Virtual supervisor bad address or instruction
    VSIP            = 0x244,  // Virtual supervisor interrupt pending
    VSATP           = 0x280,  // Virtual supervisor address translation and protection
    // Machine mode registers
    // Machine Information Registers
    MVENDORID       = 0xF11,  // Vendor ID
    MARCHID         = 0xF12,  // Architecture ID
    MIMPID          = 0xF13,  // Implementation ID
    MHARTID         = 0xF14,  // Hardware thread ID
    MCONFIGPTR      = 0xF15,  // Pointer to configuration data structure
    // Machine Trap Setup
    MSTATUS         = 0x300,  // Machine status
    MISA            = 0x301,  // ISA and extensions
    MEDELEG         = 0x302,  // Machine exception delegation register
    MIDELEG         = 0x303,  // Machine interrupt delegation register
    MIE             = 0x304,  // Machine interrupt-enable register
    MTVEC           = 0x305,  // Machine trap-handler base address
    MCOUNTEREN      = 0x306,  // Machine counter enable
    MSTATUSH        = 0x310,  // Additional machine status register, RV32 only
    // Machine Trap Handling
    MSCRATCH        = 0x340,  // Scratch register for machine trap handlers
    MEPC            = 0x341,  // Machine exception program counter
    MCAUSE          = 0x342,  // Machine trap cause
    MTVAL           = 0x343,  // Machine bad address or instruction
    MIP             = 0x344,  // Machine interrupt pending
    // Machine Configuration
    MENVCFG         = 0x30A,  // Machine environment configuration register
    MENVCFGH        = 0x31A,  // Additional machine env. conf. register, RV32 only
    MSECCFG         = 0x747,  // Machine security configuration register
    MSECCFGH        = 0x757,  // Additional machine security conf. register, RV32 only
    // Machine Memory Protection
    PMPCFG0         = 0x3A0,  // Physical memory protection configuration
    PMPCFG1         = 0x3A1,  // Physical memory protection configuration, RV32 only
    PMPCFG2         = 0x3A2,  // Physical memory protection configuration
    PMPCFG3         = 0x3A3,  // Physical memory protection configuration, RV32 only
    PMPCFG4         = 0x3A4,  // Physical memory protection configuration
    PMPCFG5         = 0x3A5,  // Physical memory protection configuration, RV32 only
    PMPCFG6         = 0x3A6,  // Physical memory protection configuration
    PMPCFG7         = 0x3A7,  // Physical memory protection configuration, RV32 only
    PMPCFG8         = 0x3A8,  // Physical memory protection configuration
    PMPCFG9         = 0x3A9,  // Physical memory protection configuration, RV32 only
    PMPCFG10        = 0x3AA,  // Physical memory protection configuration
    PMPCFG11        = 0x3AB,  // Physical memory protection configuration, RV32 only
    PMPCFG12        = 0x3AC,  // Physical memory protection configuration
    PMPCFG13        = 0x3AD,  // Physical memory protection configuration, RV32 only
    PMPCFG14        = 0x3AE,  // Physical memory protection configuration
    PMPCFG15        = 0x3AF,  // Physical memory protection configuration, RV32 only
    PMPADDR0        = 0x3B0,  // Physical memory protection address register
    PMPADDR1        = 0x3B1,  // Physical memory protection address register
    PMPADDR2        = 0x3B2,  // Physical memory protection address register
    PMPADDR3        = 0x3B3,  // Physical memory protection address register
    PMPADDR4        = 0x3B4,  // Physical memory protection address register
    PMPADDR5        = 0x3B5,  // Physical memory protection address register
    PMPADDR6        = 0x3B6,  // Physical memory protection address register
    PMPADDR7        = 0x3B7,  // Physical memory protection address register
    PMPADDR8        = 0x3B8,  // Physical memory protection address register
    PMPADDR9        = 0x3B9,  // Physical memory protection address register
    PMPADDR10       = 0x3BA,  // Physical memory protection address register
    PMPADDR11       = 0x3BB,  // Physical memory protection address register
    PMPADDR12       = 0x3BC,  // Physical memory protection address register
    PMPADDR13       = 0x3BD,  // Physical memory protection address register
    PMPADDR14       = 0x3BE,  // Physical memory protection address register
    PMPADDR15       = 0x3BF,  // Physical memory protection address register
    PMPADDR16       = 0x4C0,  // Physical memory protection address register
    PMPADDR17       = 0x3C1,  // Physical memory protection address register
    PMPADDR18       = 0x3C2,  // Physical memory protection address register
    PMPADDR19       = 0x3C3,  // Physical memory protection address register
    PMPADDR20       = 0x3C4,  // Physical memory protection address register
    PMPADDR21       = 0x3C5,  // Physical memory protection address register
    PMPADDR22       = 0x3C6,  // Physical memory protection address register
    PMPADDR23       = 0x3C7,  // Physical memory protection address register
    PMPADDR24       = 0x3C8,  // Physical memory protection address register
    PMPADDR25       = 0x3C9,  // Physical memory protection address register
    PMPADDR26       = 0x3CA,  // Physical memory protection address register
    PMPADDR27       = 0x3CB,  // Physical memory protection address register
    PMPADDR28       = 0x3CC,  // Physical memory protection address register
    PMPADDR29       = 0x3CD,  // Physical memory protection address register
    PMPADDR30       = 0x3CE,  // Physical memory protection address register
    PMPADDR31       = 0x3CF,  // Physical memory protection address register
    PMPADDR32       = 0x4D0,  // Physical memory protection address register
    PMPADDR33       = 0x3D1,  // Physical memory protection address register
    PMPADDR34       = 0x3D2,  // Physical memory protection address register
    PMPADDR35       = 0x3D3,  // Physical memory protection address register
    PMPADDR36       = 0x3D4,  // Physical memory protection address register
    PMPADDR37       = 0x3D5,  // Physical memory protection address register
    PMPADDR38       = 0x3D6,  // Physical memory protection address register
    PMPADDR39       = 0x3D7,  // Physical memory protection address register
    PMPADDR40       = 0x3D8,  // Physical memory protection address register
    PMPADDR41       = 0x3D9,  // Physical memory protection address register
    PMPADDR42       = 0x3DA,  // Physical memory protection address register
    PMPADDR43       = 0x3DB,  // Physical memory protection address register
    PMPADDR44       = 0x3DC,  // Physical memory protection address register
    PMPADDR45       = 0x3DD,  // Physical memory protection address register
    PMPADDR46       = 0x3DE,  // Physical memory protection address register
    PMPADDR47       = 0x3DF,  // Physical memory protection address register
    PMPADDR48       = 0x4E0,  // Physical memory protection address register
    PMPADDR49       = 0x3E1,  // Physical memory protection address register
    PMPADDR50       = 0x3E2,  // Physical memory protection address register
    PMPADDR51       = 0x3E3,  // Physical memory protection address register
    PMPADDR52       = 0x3E4,  // Physical memory protection address register
    PMPADDR53       = 0x3E5,  // Physical memory protection address register
    PMPADDR54       = 0x3E6,  // Physical memory protection address register
    PMPADDR55       = 0x3E7,  // Physical memory protection address register
    PMPADDR56       = 0x3E8,  // Physical memory protection address register
    PMPADDR57       = 0x3E9,  // Physical memory protection address register
    PMPADDR58       = 0x3EA,  // Physical memory protection address register
    PMPADDR59       = 0x3EB,  // Physical memory protection address register
    PMPADDR60       = 0x3EC,  // Physical memory protection address register
    PMPADDR61       = 0x3ED,  // Physical memory protection address register
    PMPADDR62       = 0x3EE,  // Physical memory protection address register
    PMPADDR63       = 0x3EF,  // Physical memory protection address register
    MCYCLE          = 0xB00,  // Machine cycle counter
    MINSTRET        = 0xB02,  // Machine instructions-retired counter
    MHPMCOUNTER3    = 0xB03,  // Machine performance-monitoring counter
    MHPMCOUNTER4    = 0xB04,  // Machine performance-monitoring counter
    MHPMCOUNTER5    = 0xB05,  // Machine performance-monitoring counter
    MHPMCOUNTER6    = 0xB06,  // Machine performance-monitoring counter
    MHPMCOUNTER7    = 0xB07,  // Machine performance-monitoring counter
    MHPMCOUNTER8    = 0xB08,  // Machine performance-monitoring counter
    MHPMCOUNTER9    = 0xB09,  // Machine performance-monitoring counter
    MHPMCOUNTER10   = 0xB0A,  // Machine performance-monitoring counter
    MHPMCOUNTER11   = 0xB0B,  // Machine performance-monitoring counter
    MHPMCOUNTER12   = 0xB0C,  // Machine performance-monitoring counter
    MHPMCOUNTER13   = 0xB0D,  // Machine performance-monitoring counter
    MHPMCOUNTER14   = 0xB0E,  // Machine performance-monitoring counter
    MHPMCOUNTER15   = 0xB0F,  // Machine performance-monitoring counter
    MHPMCOUNTER16   = 0xB10,  // Machine performance-monitoring counter
    MHPMCOUNTER17   = 0xB11,  // Machine performance-monitoring counter
    MHPMCOUNTER18   = 0xB12,  // Machine performance-monitoring counter
    MHPMCOUNTER19   = 0xB13,  // Machine performance-monitoring counter
    MHPMCOUNTER20   = 0xB14,  // Machine performance-monitoring counter
    MHPMCOUNTER21   = 0xB15,  // Machine performance-monitoring counter
    MHPMCOUNTER22   = 0xB16,  // Machine performance-monitoring counter
    MHPMCOUNTER23   = 0xB17,  // Machine performance-monitoring counter
    MHPMCOUNTER24   = 0xB18,  // Machine performance-monitoring counter
    MHPMCOUNTER25   = 0xB19,  // Machine performance-monitoring counter
    MHPMCOUNTER26   = 0xB1A,  // Machine performance-monitoring counter
    MHPMCOUNTER27   = 0xB1B,  // Machine performance-monitoring counter
    MHPMCOUNTER28   = 0xB1C,  // Machine performance-monitoring counter
    MHPMCOUNTER29   = 0xB1D,  // Machine performance-monitoring counter
    MHPMCOUNTER30   = 0xB1E,  // Machine performance-monitoring counter
    MHPMCOUNTER31   = 0xB1F,  // Machine performance-monitoring counter
    MCYCLEH         = 0xB80,  // Upper 32 bits of MCYCLE, RV32I only
    MINSTRETH       = 0xB82,  // Upper 32 bits of MINSTRET, RV32I only
    MHPMCOUNTER3H   = 0xB83,  // Upper 32 bits of HPMCOUNTER3, RV32I only
    MHPMCOUNTER4H   = 0xB84,  // Upper 32 bits of HPMCOUNTER4, RV32I only
    MHPMCOUNTER5H   = 0xB85,  // Upper 32 bits of HPMCOUNTER5, RV32I only
    MHPMCOUNTER6H   = 0xB86,  // Upper 32 bits of HPMCOUNTER6, RV32I only
    MHPMCOUNTER7H   = 0xB87,  // Upper 32 bits of HPMCOUNTER7, RV32I only
    MHPMCOUNTER8H   = 0xB88,  // Upper 32 bits of HPMCOUNTER8, RV32I only
    MHPMCOUNTER9H   = 0xB89,  // Upper 32 bits of HPMCOUNTER9, RV32I only
    MHPMCOUNTER10H  = 0xB8A,  // Upper 32 bits of HPMCOUNTER10, RV32I only
    MHPMCOUNTER11H  = 0xB8B,  // Upper 32 bits of HPMCOUNTER11, RV32I only
    MHPMCOUNTER12H  = 0xB8C,  // Upper 32 bits of HPMCOUNTER12, RV32I only
    MHPMCOUNTER13H  = 0xB8D,  // Upper 32 bits of HPMCOUNTER13, RV32I only
    MHPMCOUNTER14H  = 0xB8E,  // Upper 32 bits of HPMCOUNTER14, RV32I only
    MHPMCOUNTER15H  = 0xB8F,  // Upper 32 bits of HPMCOUNTER15, RV32I only
    MHPMCOUNTER16H  = 0xB90,  // Upper 32 bits of HPMCOUNTER16, RV32I only
    MHPMCOUNTER17H  = 0xB91,  // Upper 32 bits of HPMCOUNTER17, RV32I only
    MHPMCOUNTER18H  = 0xB92,  // Upper 32 bits of HPMCOUNTER18, RV32I only
    MHPMCOUNTER19H  = 0xB93,  // Upper 32 bits of HPMCOUNTER19, RV32I only
    MHPMCOUNTER20H  = 0xB94,  // Upper 32 bits of HPMCOUNTER20, RV32I only
    MHPMCOUNTER21H  = 0xB95,  // Upper 32 bits of HPMCOUNTER21, RV32I only
    MHPMCOUNTER22H  = 0xB96,  // Upper 32 bits of HPMCOUNTER22, RV32I only
    MHPMCOUNTER23H  = 0xB97,  // Upper 32 bits of HPMCOUNTER23, RV32I only
    MHPMCOUNTER24H  = 0xB98,  // Upper 32 bits of HPMCOUNTER24, RV32I only
    MHPMCOUNTER25H  = 0xB99,  // Upper 32 bits of HPMCOUNTER25, RV32I only
    MHPMCOUNTER26H  = 0xB9A,  // Upper 32 bits of HPMCOUNTER26, RV32I only
    MHPMCOUNTER27H  = 0xB9B,  // Upper 32 bits of HPMCOUNTER27, RV32I only
    MHPMCOUNTER28H  = 0xB9C,  // Upper 32 bits of HPMCOUNTER28, RV32I only
    MHPMCOUNTER29H  = 0xB9D,  // Upper 32 bits of HPMCOUNTER29, RV32I only
    MHPMCOUNTER30H  = 0xB9E,  // Upper 32 bits of HPMCOUNTER30, RV32I only
    MHPMCOUNTER31H  = 0xB9F,  // Upper 32 bits of HPMCOUNTER31, RV32I only
    MCOUNTINHIBIT   = 0x320,  // Machine counter-inhibit register
    MHPMEVENT3      = 0x323,  // Machine performance-monitoring event selector
    MHPMEVENT4      = 0x324,  // Machine performance-monitoring event selector
    MHPMEVENT5      = 0x325,  // Machine performance-monitoring event selector
    MHPMEVENT6      = 0x326,  // Machine performance-monitoring event selector
    MHPMEVENT7      = 0x327,  // Machine performance-monitoring event selector
    MHPMEVENT8      = 0x328,  // Machine performance-monitoring event selector
    MHPMEVENT9      = 0x329,  // Machine performance-monitoring event selector
    MHPMEVENT10     = 0x32A,  // Machine performance-monitoring event selector
    MHPMEVENT11     = 0x32B,  // Machine performance-monitoring event selector
    MHPMEVENT12     = 0x32C,  // Machine performance-monitoring event selector
    MHPMEVENT13     = 0x32D,  // Machine performance-monitoring event selector
    MHPMEVENT14     = 0x32E,  // Machine performance-monitoring event selector
    MHPMEVENT15     = 0x32F,  // Machine performance-monitoring event selector
    MHPMEVENT16     = 0x330,  // Machine performance-monitoring event selector
    MHPMEVENT17     = 0x331,  // Machine performance-monitoring event selector
    MHPMEVENT18     = 0x332,  // Machine performance-monitoring event selector
    MHPMEVENT19     = 0x333,  // Machine performance-monitoring event selector
    MHPMEVENT20     = 0x334,  // Machine performance-monitoring event selector
    MHPMEVENT21     = 0x335,  // Machine performance-monitoring event selector
    MHPMEVENT22     = 0x336,  // Machine performance-monitoring event selector
    MHPMEVENT23     = 0x337,  // Machine performance-monitoring event selector
    MHPMEVENT24     = 0x338,  // Machine performance-monitoring event selector
    MHPMEVENT25     = 0x339,  // Machine performance-monitoring event selector
    MHPMEVENT26     = 0x33A,  // Machine performance-monitoring event selector
    MHPMEVENT27     = 0x33B,  // Machine performance-monitoring event selector
    MHPMEVENT28     = 0x33C,  // Machine performance-monitoring event selector
    MHPMEVENT29     = 0x33D,  // Machine performance-monitoring event selector
    MHPMEVENT30     = 0x33E,  // Machine performance-monitoring event selector
    MHPMEVENT31     = 0x33F,  // Machine performance-monitoring event selector
    // Debug/Trace Registers (shared with Debug Mode)
    TSELECT         = 0x7A0,  // Debug/Trace trigger register select
    TDATA1          = 0x7A1,  // First Debug/Trace trigger data register
    TDATA2          = 0x7A2,  // Second Debug/Trace trigger data register
    TDATA3          = 0x7A3,  // Third Debug/Trace trigger data register
    TINFO           = 0x7A4,  // Debug trigger info register
    TCONTROL        = 0x7A5,  // Debug trigger control register
    MCONTEXT        = 0x7A8,  // Machine mode trigger context register
    MSCONTEXT       = 0x7AA,  // Supervisor mode trigger context register
    // Debug Mode Registers
    DCSR            = 0x7B0,  // Debug control and status register
    DPC             = 0x7B1,  // Debug PC
    DSCRATCH0       = 0x7B2,  // Debug scratch register
    DSCRATCH1       = 0x7B3,  // Debug scratch register (last one)
    VSTART          = 0x008,  // Vector start position
    VXSTAT          = 0x009,  // Fixed point saturate flag
    VXRM            = 0x00A,  // Fixed point rounding mode
    VL              = 0xC20,  // Vector length
    VTYPE           = 0xC21,  // Vector data type register
    VLENB           = 0xC22   // VLEN/8 (vector register length in bytes)
}

enum privileged_reg_fld_t: ubyte {
  RSVD,       // Reserved field
  MXL,        // mis.mxl
  EXTENSION,  // mis.extension
  MODE,       // satp.mode
  ASID,       // satp.asid
  PPN         // satp.ppn
}

enum privileged_level_t: ubyte {
  M_LEVEL = 0b11,  // Machine mode
  S_LEVEL = 0b01,  // Supervisor mode
  U_LEVEL = 0b00   // User mode
}

enum reg_field_access_t: ubyte {
  WPRI, // Reserved Writes Preserve Values, Reads Ignore Value
  WLRL, // Write/Read Only Legal Values
  WARL  // Write Any Values, Reads Legal Values
}

//Pseudo instructions
enum riscv_pseudo_instr_name_t: ubyte {
  LI = 0,
  LA
}

// Data pattern of the memory model
enum data_pattern_t: ubyte {
  RAND_DATA = 0,
  ALL_ZERO,
  INCR_VAL
}

enum pte_permission_t: ubyte {
  NEXT_LEVEL_PAGE   = 0b000, // Pointer to next level of page table.
  READ_ONLY_PAGE    = 0b001, // Read-only page.
  READ_WRITE_PAGE   = 0b011, // Read-write page.
  EXECUTE_ONLY_PAGE = 0b100, // Execute-only page.
  READ_EXECUTE_PAGE = 0b101, // Read-execute page.
  R_W_EXECUTE_PAGE  = 0b111  // Read-write-execute page
}

enum interrupt_cause_t: ubyte {
  U_SOFTWARE_INTR  = 0x0,
  S_SOFTWARE_INTR  = 0x1,
  M_SOFTWARE_INTR  = 0x3,
  U_TIMER_INTR     = 0x4,
  S_TIMER_INTR     = 0x5,
  M_TIMER_INTR     = 0x7,
  U_EXTERNAL_INTR  = 0x8,
  S_EXTERNAL_INTR  = 0x9,
  M_EXTERNAL_INTR  = 0xB
}

enum exception_cause_t: ubyte {
  INSTRUCTION_ADDRESS_MISALIGNED = 0x0,
  INSTRUCTION_ACCESS_FAULT       = 0x1,
  ILLEGAL_INSTRUCTION            = 0x2,
  BREAKPOINT                     = 0x3,
  LOAD_ADDRESS_MISALIGNED        = 0x4,
  LOAD_ACCESS_FAULT              = 0x5,
  STORE_AMO_ADDRESS_MISALIGNED   = 0x6,
  STORE_AMO_ACCESS_FAULT         = 0x7,
  ECALL_UMODE                    = 0x8,
  ECALL_SMODE                    = 0x9,
  ECALL_MMODE                    = 0xB,
  INSTRUCTION_PAGE_FAULT         = 0xC,
  LOAD_PAGE_FAULT                = 0xD,
  STORE_AMO_PAGE_FAULT           = 0xF
}

enum  misa_ext_t: int {
  MISA_EXT_A = 0,
  MISA_EXT_B,
  MISA_EXT_C,
  MISA_EXT_D,
  MISA_EXT_E,
  MISA_EXT_F,
  MISA_EXT_G,
  MISA_EXT_H,
  MISA_EXT_I,
  MISA_EXT_J,
  MISA_EXT_K,
  MISA_EXT_L,
  MISA_EXT_M,
  MISA_EXT_N,
  MISA_EXT_O,
  MISA_EXT_P,
  MISA_EXT_Q,
  MISA_EXT_R,
  MISA_EXT_S,
  MISA_EXT_T,
  MISA_EXT_U,
  MISA_EXT_V,
  MISA_EXT_W,
  MISA_EXT_X,
  MISA_EXT_Y,
  MISA_EXT_Z
}

enum hazard_e: ubyte {
  NO_HAZARD,
  RAW_HAZARD,
  WAR_HAZARD,
  WAW_HAZARD
}

// `include "riscv_core_setting.sv"

// PMP address matching mode
enum pmp_addr_mode_t: ubyte {
  OFF   = 0b00,
  TOR   = 0b01,
  NA4   = 0b10,
  NAPOT = 0b11
}

//   // PMP configuration register layout
//   // This configuration struct includes the pmp address for simplicity
//   // TODO (udinator) allow a full 34 bit address for rv32?
// `ifdef _VCP //GRK958
//   typedef struct packed {
//     bit                   l;
//     bit [1:0]                  zero;
//     pmp_addr_mode_t       a;
//     bit                   x;
//     bit                   w;
//     bit                   r;
//     // RV32: the pmpaddr is the top 32 bits of a 34 bit PMP address
//     // RV64: the pmpaddr is the top 54 bits of a 56 bit PMP address
//     bit [XLEN - 1 : 0]    addr;
//     // The offset from the address of <main> - automatically populated by the
//     // PMP generation routine.
//     bit [XLEN - 1 : 0]    offset;
// `else
struct pmp_cfg_reg_t {
  @rand bool                   l;
  ubvec!2                      zero;
  @rand pmp_addr_mode_t        a;
  @rand bool                   x;
  @rand bool                   w;
  @rand bool                   r;
  // RV32: the pmpaddr is the top 32 bits of a 34 bit PMP address
  // RV64: the pmpaddr is the top 54 bits of a 56 bit PMP address
  ubvec!XLEN    addr;
  // The offset from the address of <main> - automatically populated by the
  // PMP generation routine.
  @rand ubvec!XLEN    offset;
}


string hart_prefix(int hart = 0) {
  if (NUM_HARTS <= 1) {
    return "";
  }
  else {
    import std.string: format;
    return format("h%0d_", hart);
  }
}

string get_label(string label, int hart = 0) {
  return hart_prefix(hart) ~ label;
}

struct vtype_t {
  @UVM_DEFAULT {
    @rand bool ill;
    @rand bool fractional_lmul;
    @rand ubvec!(XLEN-8) reserved;
    @rand uint vediv;
    @rand uint vsew;
    @rand uint vlmul;
  }
}


enum vxrm_t: ubyte {
  RoundToNearestUp,
  RoundToNearestEven,
  RoundDown,
  RoundToOdd
}

enum  b_ext_group_t: int {
  ZBA,
  ZBB,
  ZBS,
  ZBP,
  ZBE,
  ZBF,
  ZBC,
  ZBR,
  ZBM,
  ZBT,
  ZB_TMP // for uncategorized instructions
}

// `VECTOR_INCLUDE("riscv_instr_pkg_inc_variables.sv")

alias program_id_t = ubvec!16;

// xSTATUS bit mask
enum ubvec!XLEN MPRV_BIT_MASK = 0x1 << 17;
enum ubvec!XLEN SUM_BIT_MASK  = 0x1 << 18;
enum ubvec!XLEN MPP_BIT_MASK  = 0x3 << 11;

enum int IMM25_WIDTH = 25;
enum int IMM12_WIDTH = 12;
enum int INSTR_WIDTH = 32;
enum int DATA_WIDTH  = 32;

// Enum Ints for output assembly program formatting
enum int MAX_INSTR_STR_LEN = 13;
enum int LABEL_STR_LEN     = 18;

// Enum Int for program generation
enum int MAX_CALLSTACK_DEPTH = 20;
enum int MAX_SUB_PROGRAM_CNT = 20;
enum int MAX_CALL_PER_FUNC   = 5;

template SPACES(uint spaces) {
  static if (spaces == 0) enum SPACES = "";
  else enum SPACES = SPACES!(spaces-1) ~ " ";
}

string spaces_string(uint len) {
  import std.algorithm: fill;
  char[] str = new char[len];
  fill(str, ' ');
  return cast(string) str;
}

enum string indent = SPACES!LABEL_STR_LEN;

// Format the string to a fixed length
string format_string(string str, int len = 10) {
  if (len < str.length) return str;
  else {
    static string spaces;
    if (spaces.length == 0) spaces = spaces_string(len);
    string formatted_str = str ~ spaces[0..len-str.length];
    return formatted_str;
  }
}

// Print the data in the following format
// 0xabcd, 0x1234, 0x3334 ...

string format_data(ubyte[] data, uint byte_per_group=4) {
  import std.string: format;
  string str = "0x";
  foreach (i, d; data) {
    if ((i % byte_per_group == 0) && (i != data.length - 1) && (i != 0)) {
      str ~= ", 0x";
    }
    str ~= format("%02x", d);
  }
  return str;
}

// Get the instr name enum from a string
riscv_instr_name_t get_instr_name(string str) {
  import std.string: toUpper;
  alias enum_wrapper = uvm_enum_wrapper!riscv_instr_name_t;
  riscv_instr_name_t value;
  if (enum_wrapper.from_name(toUpper(str), value)) {
    return value;
  }
  else {
    return riscv_instr_name_t.INVALID_INSTR;
  }
}

// Push general purpose register to stack, this is needed before trap handling4
void push_gpr_to_kernel_stack(privileged_reg_t status,
			      privileged_reg_t scratch,
			      bool mprv,
			      riscv_reg_t sp,
			      riscv_reg_t tp,
			      ref string[] instr) {
  import std.algorithm: canFind;
  import std.string: format;

  string store_instr = (XLEN == 32) ? "sw" : "sd";
  if (canFind(implemented_csr, scratch)) {
    // Use kernal stack for handling exceptions
    // Save the user mode stack pointer to the scratch register
    instr ~= format("csrrw x%0d, 0x%0x, x%0d", sp, scratch, sp);
    // Move TP to SP
    instr ~= format("add x%0d, x%0d, zero", sp, tp);
  }
  // If MPRV is set and MPP is S/U mode, it means the address translation and memory protection
  // for load/store instruction is the same as the mode indicated by MPP. In this case, we
  // need to use the virtual address to access the kernel stack.
  if ((status == privileged_reg_t.MSTATUS) && (SATP_MODE != satp_mode_t.BARE)) {
    // We temporarily use tp to check mstatus to avoid changing other GPR. The value of sp has
    // been saved to xScratch and can be restored later.
    if (mprv) {
      instr ~= format("csrr x%0d, 0x%0x // MSTATUS", tp, status);
      instr ~= format("srli x%0d, x%0d, 11", tp, tp);  // Move MPP to bit 0
      instr ~= format("andi x%0d, x%0d, 0x3", tp, tp); // keep the MPP bits
      // Check if MPP equals to M-mode('b11)
      instr ~= format("xori x%0d, x%0d, 0x3", tp, tp); // Check if MPP equals to M-mode('b11)
      instr ~= format("bnez x%0d, 1f", tp);      // Use physical address for kernel SP
      // Use virtual address for stack pointer
      instr ~= format("slli x%0d, x%0d, %0d", sp, sp, XLEN - MAX_USED_VADDR_BITS);
      instr ~= format("srli x%0d, x%0d, %0d", sp, sp, XLEN - MAX_USED_VADDR_BITS);
    }
  }
  // Reserve space from kernel stack to save all 32 GPR except for x0
  instr ~= format("1: addi x%0d, x%0d, -%0d", sp, sp, 31 * (XLEN/8));
  // Push all GPRs to kernel stack
  for (int i = 1; i < 32; i++) {
    instr ~= format("%0s  x%0d, %0d(x%0d)", store_instr, i, i * (XLEN/8), sp);
  }
}

// Pop general purpose register from stack, this is needed before returning to user program
void pop_gpr_from_kernel_stack(privileged_reg_t status,
			       privileged_reg_t scratch,
			       bool mprv,
			       riscv_reg_t sp,
			       riscv_reg_t tp,
			       ref string[] instr) {
  import std.algorithm: canFind;
  import std.string: format;

  string load_instr = (XLEN == 32) ? "lw" : "ld";
  // Pop user mode GPRs from kernel stack
  for (int i = 1; i < 32; i++) {
    instr ~= format("%0s  x%0d, %0d(x%0d)", load_instr, i, i * (XLEN/8), sp);
  }
  // Restore kernel stack pointer
  instr ~= format("addi x%0d, x%0d, %0d", sp, sp, 31 * (XLEN/8));
  if (canFind(implemented_csr, scratch)) {
    // Move SP to TP
    instr ~= format("add x%0d, x%0d, zero", tp, sp);
    // Restore user mode stack pointer
    instr ~= format("csrrw x%0d, 0x%0x, x%0d", sp, scratch, sp);
  }
}

void get_int_arg_value(string cmdline_str, ref int val) {
  import std.conv: to;
  string s;
  if (uvm_cmdline_processor.get_inst().get_arg_value(cmdline_str, s)) {
    val = s.to!int;
  }
}


// Get a bool argument from comand line
void get_bool_arg_value(string cmdline_str, ref bool val) {
  import std.conv: to;
  string s;
  if (uvm_cmdline_processor.get_inst().get_arg_value(cmdline_str, s)) {
    val = s.to!bool;
  }
}

// Get a hex argument from command line
void get_hex_arg_value(string cmdline_str, ref int val) {
  import std.conv: to;
  string s;
  if(uvm_cmdline_processor.get_inst().get_arg_value(cmdline_str, s)) {
    val = s.to!int(16);
  }
}


class cmdline_enum_processor(T)
{
  static void get_array_values(string cmdline_str, ref T[] vals) {
    import std.format: format;
    string s;
    uvm_cmdline_processor.get_inst().get_arg_value(cmdline_str, s);
    if (s != "") {
      string[] cmdline_list;
      T value;
      uvm_string_split(s, ',', cmdline_list);
      vals.length = cmdline_list.length;
      foreach (i, str; cmdline_list) {
	import std.string: toUpper;
	if (uvm_enum_wrapper!T.from_name(toUpper(str), value)) {
	  vals[i] = value;
	}
	else {
	  uvm_fatal("riscv_instr_pkg",
		    format("Invalid value (%0s) specified in command line: %0s",
			   str, cmdline_str));
	}
      }
    }
  }
}

enum riscv_reg_t[] all_gpr = [EnumMembers!riscv_reg_t];

enum riscv_reg_t[] compressed_gpr = [riscv_reg_t.S0, riscv_reg_t.S1,
				     riscv_reg_t.A0, riscv_reg_t.A1,
				     riscv_reg_t.A2, riscv_reg_t.A3,
				     riscv_reg_t.A4, riscv_reg_t.A5];

enum riscv_instr_category_t[] all_categories =
  [EnumMembers!riscv_instr_category_t];

void get_val(string str, out bvec!XLEN val, bool hex = 0) {
  import std.string: format;
  import std.conv: to;
  if (str[0..2] == "0x") {
    str = str[2..$];
    val = str.to!int(16);
    return;
  }

  if (hex) {
    val = str.to!int(16);
  }
  else {
    if (str[0] == '-') {
      str = str[1..$];
      val = -(str.to!int());
    }
    else {
      val = str.to!int();
    }
  }
  uvm_info("riscv_instr_pkg", format("imm:%0s -> 0x%0x/%0d", str, val,
				     cast(bvec!XLEN) val), UVM_FULL);
}
