"""
Copyright 2020 Google LLC
Copyright 2020 PerfectVIPs Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.

"""

import logging
from enum import Enum, IntEnum, auto
from bitstring import BitArray
from importlib import import_module


class mem_region_t:
    name = 0
    size_in_bytes = auto()
    xwr = auto()


class satp_mode_t(IntEnum):
    BARE = 0b0000
    SV32 = 0b0001
    SV39 = 0b1000
    SV48 = 0b1001
    SV57 = 0b1010
    SV64 = 0b1011


class f_rounding_mode_t(IntEnum):
    RNE = 0b000
    RTZ = 0b001
    RDN = 0b010
    RUP = 0b011
    RMM = 0b100


class mtvec_mode_t(IntEnum):
    DIRECT = 0b00
    VECTORED = 0b01


class imm_t(IntEnum):
    IMM = 0
    UIMM = auto()
    NZUIMM = auto()
    NZIMM = auto()


class privileged_mode_t(IntEnum):
    USER_MODE = 0b00
    SUPERVISOR_MODE = 0b01
    RESERVED_MODE = 0b10
    MACHINE_MODE = 0b11


class riscv_instr_group_t(IntEnum):
    RV32I = 0
    RV64I = auto()
    RV32M = auto()
    RV64M = auto()
    RV32A = auto()
    RV64A = auto()
    RV32F = auto()
    RV32FC = auto()
    RV64F = auto()
    RV32D = auto()
    RV32DC = auto()
    RV64D = auto()
    RV32C = auto()
    RV64C = auto()
    RV128I = auto()
    RV128C = auto()
    RV32V = auto()
    RV32B = auto()
    RV64V = auto()
    RV64B = auto()
    RV32X = auto()
    RV64X = auto()
    RVV = auto()


class riscv_instr_name_t(IntEnum):
    LUI = 0
    AUIPC = auto()
    JAL = auto()
    JALR = auto()
    BEQ = auto()
    BNE = auto()
    BLT = auto()
    BGE = auto()
    BLTU = auto()
    BGEU = auto()
    LB = auto()
    LH = auto()
    LW = auto()
    LBU = auto()
    LHU = auto()
    SB = auto()
    SH = auto()
    SW = auto()
    ADDI = auto()
    SLTI = auto()
    SLTIU = auto()
    XORI = auto()
    ORI = auto()
    ANDI = auto()
    SLLI = auto()
    SRLI = auto()
    SRAI = auto()
    ADD = auto()
    SUB = auto()
    SLL = auto()
    SLT = auto()
    SLTU = auto()
    XOR = auto()
    SRL = auto()
    SRA = auto()
    OR = auto()
    AND = auto()
    NOP = auto()
    FENCE = auto()
    FENCE_I = auto()
    ECALL = auto()
    EBREAK = auto()
    CSRRW = auto()
    CSRRS = auto()
    CSRRC = auto()
    CSRRWI = auto()
    CSRRSI = auto()
    CSRRCI = auto()
    ANDN = auto()
    ORN = auto()
    XNOR = auto()
    GORC = auto()
    SLO = auto()
    SRO = auto()
    ROL = auto()
    ROR = auto()
    SBCLR = auto()
    SBSET = auto()
    SBINV = auto()
    SBEXT = auto()
    GREV = auto()
    SLOI = auto()
    SROI = auto()
    RORI = auto()
    SBCLRI = auto()
    SBSETI = auto()
    SBINVI = auto()
    SBEXTI = auto()
    GORCI = auto()
    GREVI = auto()
    CMIX = auto()
    CMOV = auto()
    FSL = auto()
    FSR = auto()
    FSRI = auto()
    CLZ = auto()
    CTZ = auto()
    PCNT = auto()
    SEXT_B = auto()
    SEXT_H = auto()
    CRC32_B = auto()
    CRC32_H = auto()
    CRC32_W = auto()
    CRC32C_B = auto()
    CRC32C_H = auto()
    CRC32C_W = auto()
    CLMUL = auto()
    CLMULR = auto()
    CLMULH = auto()
    MIN = auto()
    MAX = auto()
    MINU = auto()
    MAXU = auto()
    SHFL = auto()
    UNSHFL = auto()
    BDEP = auto()
    BEXT = auto()
    PACK = auto()
    PACKU = auto()
    BMATOR = auto()
    BMATXOR = auto()
    PACKH = auto()
    BFP = auto()
    SHFLI = auto()
    UNSHFLI = auto()
    ADDIWU = auto()
    SLLIU_W = auto()
    ADDWU = auto()
    SUBWU = auto()
    BMATFLIP = auto()
    CRC32_D = auto()
    CRC32C_D = auto()
    ADDU_W = auto()
    SUBU_W = auto()
    SLOW = auto()
    SROW = auto()
    ROLW = auto()
    RORW = auto()
    SBCLRW = auto()
    SBSETW = auto()
    SBINVW = auto()
    SBEXTW = auto()
    GORCW = auto()
    GREVW = auto()
    SLOIW = auto()
    SROIW = auto()
    RORIW = auto()
    SBCLRIW = auto()
    SBSETIW = auto()
    SBINVIW = auto()
    GORCIW = auto()
    GREVIW = auto()
    FSLW = auto()
    FSRW = auto()
    FSRIW = auto()
    CLZW = auto()
    CTZW = auto()
    PCNTW = auto()
    CLMULW = auto()
    CLMULRW = auto()
    CLMULHW = auto()
    SHFLW = auto()
    UNSHFLW = auto()
    BDEPW = auto()
    BEXTW = auto()
    PACKW = auto()
    PACKUW = auto()
    BFPW = auto()
    MUL = auto()
    MULH = auto()
    MULHSU = auto()
    MULHU = auto()
    DIV = auto()
    DIVU = auto()
    REM = auto()
    REMU = auto()
    MULW = auto()
    DIVW = auto()
    DIVUW = auto()
    REMW = auto()
    REMUW = auto()
    FLW = auto()
    FSW = auto()
    FMADD_S = auto()
    FMSUB_S = auto()
    FNMSUB_S = auto()
    FNMADD_S = auto()
    FADD_S = auto()
    FSUB_S = auto()
    FMUL_S = auto()
    FDIV_S = auto()
    FSQRT_S = auto()
    FSGNJ_S = auto()
    FSGNJN_S = auto()
    FSGNJX_S = auto()
    FMIN_S = auto()
    FMAX_S = auto()
    FCVT_W_S = auto()
    FCVT_WU_S = auto()
    FMV_X_W = auto()
    FEQ_S = auto()
    FLT_S = auto()
    FLE_S = auto()
    FCLASS_S = auto()
    FCVT_S_W = auto()
    FCVT_S_WU = auto()
    FMV_W_X = auto()
    FCVT_L_S = auto()
    FCVT_LU_S = auto()
    FCVT_S_L = auto()
    FCVT_S_LU = auto()
    FLD = auto()
    FSD = auto()
    FMADD_D = auto()
    FMSUB_D = auto()
    FNMSUB_D = auto()
    FNMADD_D = auto()
    FADD_D = auto()
    FSUB_D = auto()
    FMUL_D = auto()
    FDIV_D = auto()
    FSQRT_D = auto()
    FSGNJ_D = auto()
    FSGNJN_D = auto()
    FSGNJX_D = auto()
    FMIN_D = auto()
    FMAX_D = auto()
    FCVT_S_D = auto()
    FCVT_D_S = auto()
    FEQ_D = auto()
    FLT_D = auto()
    FLE_D = auto()
    FCLASS_D = auto()
    FCVT_W_D = auto()
    FCVT_WU_D = auto()
    FCVT_D_W = auto()
    FCVT_D_WU = auto()
    FCVT_L_D = auto()
    FCVT_LU_D = auto()
    FMV_X_D = auto()
    FCVT_D_L = auto()
    FCVT_D_LU = auto()
    FMV_D_X = auto()
    LWU = auto()
    LD = auto()
    SD = auto()
    ADDIW = auto()
    SLLIW = auto()
    SRLIW = auto()
    SRAIW = auto()
    ADDW = auto()
    SUBW = auto()
    SLLW = auto()
    SRLW = auto()
    SRAW = auto()
    C_LW = auto()
    C_SW = auto()
    C_LWSP = auto()
    C_SWSP = auto()
    C_ADDI4SPN = auto()
    C_ADDI = auto()
    C_LI = auto()
    C_ADDI16SP = auto()
    C_LUI = auto()
    C_SRLI = auto()
    C_SRAI = auto()
    C_ANDI = auto()
    C_SUB = auto()
    C_XOR = auto()
    C_OR = auto()
    C_AND = auto()
    C_BEQZ = auto()
    C_BNEZ = auto()
    C_SLLI = auto()
    C_MV = auto()
    C_EBREAK = auto()
    C_ADD = auto()
    C_NOP = auto()
    C_J = auto()
    C_JAL = auto()
    C_JR = auto()
    C_JALR = auto()
    C_ADDIW = auto()
    C_SUBW = auto()
    C_ADDW = auto()
    C_LD = auto()
    C_SD = auto()
    C_LDSP = auto()
    C_SDSP = auto()
    C_SRLI64 = auto()
    C_SRAI64 = auto()
    C_SLLI64 = auto()
    C_LQ = auto()
    C_SQ = auto()
    C_LQSP = auto()
    C_SQSP = auto()
    C_FLW = auto()
    C_FSW = auto()
    C_FLWSP = auto()
    C_FSWSP = auto()
    C_FLD = auto()
    C_FSD = auto()
    C_FLDSP = auto()
    C_FSDSP = auto()
    LR_W = auto()
    SC_W = auto()
    AMOSWAP_W = auto()
    AMOADD_W = auto()
    AMOAND_W = auto()
    AMOOR_W = auto()
    AMOXOR_W = auto()
    AMOMIN_W = auto()
    AMOMAX_W = auto()
    AMOMINU_W = auto()
    AMOMAXU_W = auto()
    LR_D = auto()
    SC_D = auto()
    AMOSWAP_D = auto()
    AMOADD_D = auto()
    AMOAND_D = auto()
    AMOOR_D = auto()
    AMOXOR_D = auto()
    AMOMIN_D = auto()
    AMOMAX_D = auto()
    AMOMINU_D = auto()
    AMOMAXU_D = auto()
    VSETVL = auto()
    VSETVLI = auto()
    VADD = auto()
    VSUB = auto()
    VRSUB = auto()
    VWADDU = auto()
    VWSUBU = auto()
    VWADD = auto()
    VWSUB = auto()
    VADC = auto()
    VMADC = auto()
    VSBC = auto()
    VMSBC = auto()
    VAND = auto()
    VOR = auto()
    VXOR = auto()
    VSLL = auto()
    VSRL = auto()
    VSRA = auto()
    VNSRL = auto()
    VNSRA = auto()
    VMSEQ = auto()
    VMSNE = auto()
    VMSLTU = auto()
    VMSLT = auto()
    VMSLEU = auto()
    VMSLE = auto()
    VMSGTU = auto()
    VMSGT = auto()
    VMINU = auto()
    VMIN = auto()
    VMAXU = auto()
    VMAX = auto()
    VMUL = auto()
    VMULH = auto()
    VMULHU = auto()
    VMULHSU = auto()
    VDIVU = auto()
    VDIV = auto()
    VREMU = auto()
    VREM = auto()
    VWMUL = auto()
    VWMULU = auto()
    VWMULSU = auto()
    VMACC = auto()
    VNMSAC = auto()
    VMADD = auto()
    VNMSUB = auto()
    VWMACCU = auto()
    VWMACC = auto()
    VWMACCSU = auto()
    VWMACCUS = auto()
    VMERGE = auto()
    VMV = auto()
    VSADDU = auto()
    VSADD = auto()
    VSSUBU = auto()
    VSSUB = auto()
    VAADDU = auto()
    VAADD = auto()
    VASUBU = auto()
    VASUB = auto()
    VSSRL = auto()
    VSSRA = auto()
    VNCLIPU = auto()
    VNCLIP = auto()
    VFADD = auto()
    VFSUB = auto()
    VFRSUB = auto()
    VFMUL = auto()
    VFDIV = auto()
    VFRDIV = auto()
    VFWMUL = auto()
    VFMACC = auto()
    VFNMACC = auto()
    VFMSAC = auto()
    VFNMSAC = auto()
    VFMADD = auto()
    VFNMADD = auto()
    VFMSUB = auto()
    VFNMSUB = auto()
    VFWMACC = auto()
    VFWNMACC = auto()
    VFWMSAC = auto()
    VFWNMSAC = auto()
    VFSQRT_V = auto()
    VFMIN = auto()
    VFMAX = auto()
    VFSGNJ = auto()
    VFSGNJN = auto()
    VFSGNJX = auto()
    VMFEQ = auto()
    VMFNE = auto()
    VMFLT = auto()
    VMFLE = auto()
    VMFGT = auto()
    VMFGE = auto()
    VFCLASS_V = auto()
    VFMERGE = auto()
    VFMV = auto()
    VFCVT_XU_F_V = auto()
    VFCVT_X_F_V = auto()
    VFCVT_F_XU_V = auto()
    VFCVT_F_X_V = auto()
    VFWCVT_XU_F_V = auto()
    VFWCVT_X_F_V = auto()
    VFWCVT_F_XU_V = auto()
    VFWCVT_F_X_V = auto()
    VFWCVT_F_F_V = auto()
    VFNCVT_XU_F_W = auto()
    VFNCVT_X_F_W = auto()
    VFNCVT_F_XU_W = auto()
    VFNCVT_F_X_W = auto()
    VFNCVT_F_F_W = auto()
    VFNCVT_ROD_F_F_W = auto()
    VREDSUM_VS = auto()
    VREDMAXU_VS = auto()
    VREDMAX_VS = auto()
    VREDMINU_VS = auto()
    VREDMIN_VS = auto()
    VREDAND_VS = auto()
    VREDOR_VS = auto()
    VREDXOR_VS = auto()
    VWREDSUMU_VS = auto()
    VWREDSUM_VS = auto()
    VFREDOSUM_VS = auto()
    VFREDSUM_VS = auto()
    VFREDMAX_VS = auto()
    VFWREDOSUM_VS = auto()
    VFWREDSUM_VS = auto()
    VMAND_MM = auto()
    VMNAND_MM = auto()
    VMANDNOT_MM = auto()
    VMXOR_MM = auto()
    VMOR_MM = auto()
    VMNOR_MM = auto()
    VMORNOT_MM = auto()
    VMXNOR_MM = auto()
    VPOPC_M = auto()
    VFIRST_M = auto()
    VMSBF_M = auto()
    VMSIF_M = auto()
    VMSOF_M = auto()
    VIOTA_M = auto()
    VID_V = auto()
    VMV_X_S = auto()
    VMV_S_X = auto()
    VFMV_F_S = auto()
    VFMV_S_F = auto()
    VSLIDEUP = auto()
    VSLIDEDOWN = auto()
    VSLIDE1UP = auto()
    VSLIDE1DOWN = auto()
    VRGATHER = auto()
    VCOMPRESS = auto()
    VMV1R_V = auto()
    VMV2R_V = auto()
    VMV4R_V = auto()
    VMV8R_V = auto()
    DRET = auto()
    MRET = auto()
    URET = auto()
    SRET = auto()
    WFI = auto()
    SFENCE_VMA = auto()
    INVALID_INSTR = auto()


class riscv_reg_t(IntEnum):
    ZERO = 0
    RA = auto()
    SP = auto()
    GP = auto()
    TP = auto()
    T0 = auto()
    T1 = auto()
    T2 = auto()
    S0 = auto()
    S1 = auto()
    A0 = auto()
    A1 = auto()
    A2 = auto()
    A3 = auto()
    A4 = auto()
    A5 = auto()
    A6 = auto()
    A7 = auto()
    S2 = auto()
    S3 = auto()
    S4 = auto()
    S5 = auto()
    S6 = auto()
    S7 = auto()
    S8 = auto()
    S9 = auto()
    S10 = auto()
    S11 = auto()
    T3 = auto()
    T4 = auto()
    T5 = auto()
    T6 = auto()


class riscv_fpr_t(IntEnum):
    FT0 = 0
    FT1 = auto()
    FT2 = auto()
    FT3 = auto()
    FT4 = auto()
    FT5 = auto()
    FT6 = auto()
    FT7 = auto()
    FS0 = auto()
    FS1 = auto()
    FA0 = auto()
    FA1 = auto()
    FA2 = auto()
    FA3 = auto()
    FA4 = auto()
    FA5 = auto()
    FA6 = auto()
    FA7 = auto()
    FS2 = auto()
    FS3 = auto()
    FS4 = auto()
    FS5 = auto()
    FS6 = auto()
    FS7 = auto()
    FS8 = auto()
    FS9 = auto()
    FS10 = auto()
    FS11 = auto()
    FT8 = auto()
    FT9 = auto()
    FT10 = auto()
    FT11 = auto()


class riscv_vreg_t(IntEnum):
    V0 = 0
    V1 = auto()
    V2 = auto()
    V3 = auto()
    V4 = auto()
    V5 = auto()
    V6 = auto()
    V7 = auto()
    V8 = auto()
    V9 = auto()
    V10 = auto()
    V11 = auto()
    V12 = auto()
    V13 = auto()
    V14 = auto()
    V15 = auto()
    V16 = auto()
    V17 = auto()
    V18 = auto()
    V19 = auto()
    V20 = auto()
    V21 = auto()
    V22 = auto()
    V23 = auto()
    V24 = auto()
    V25 = auto()
    V26 = auto()
    V27 = auto()
    V28 = auto()
    V29 = auto()
    V30 = auto()
    V31 = auto()


class riscv_instr_format_t(IntEnum):
    J_FORMAT = 0
    U_FORMAT = auto()
    I_FORMAT = auto()
    B_FORMAT = auto()
    R_FORMAT = auto()
    S_FORMAT = auto()
    R4_FORMAT = auto()
    CI_FORMAT = auto()
    CB_FORMAT = auto()
    CJ_FORMAT = auto()
    CR_FORMAT = auto()
    CA_FORMAT = auto()
    CL_FORMAT = auto()
    CS_FORMAT = auto()
    CSS_FORMAT = auto()
    CIW_FORMAT = auto()
    VSET_FORMAT = auto()
    VA_FORMAT = auto()
    VS2_FORMAT = auto()
    VL_FORMAT = auto()
    VS_FORMAT = auto()


class va_variant_t(IntEnum):
    VV = 0
    VI = auto()
    VX = auto()
    VF = auto()
    WV = auto()
    WI = auto()
    WX = auto()
    VVM = auto()
    VIM = auto()
    VXM = auto()
    VFM = auto()
    VS = auto()
    VM = auto()


class riscv_instr_category_t(IntEnum):
    LOAD = 0
    STORE = auto()
    SHIFT = auto()
    ARITHMETIC = auto()
    LOGICAL = auto()
    COMPARE = auto()
    BRANCH = auto()
    JUMP = auto()
    SYNCH = auto()
    SYSTEM = auto()
    COUNTER = auto()
    CSR = auto()
    CHANGELEVEL = auto()
    TRAP = auto()
    INTERRUPT = auto()
    AMO = auto()


# typedef bit[11:0] riscv_csr_t;


class privileged_reg_t(IntEnum):
    USTATUS = 0x000
    UIE = 0x004
    UTVEC = 0x005
    USCRATCH = 0x040
    UEPC = 0x041
    UCAUSE = 0x042
    UTVAL = 0x043
    UIP = 0x044
    FFLAGS = 0x001
    FRM = 0x002
    FCSR = 0x003
    CYCLE = 0xC00
    TIME = 0xC01
    INSTRET = 0xC02
    HPMCOUNTER3 = 0xC03
    HPMCOUNTER4 = 0xC04
    HPMCOUNTER5 = 0xC05
    HPMCOUNTER6 = 0xC06
    HPMCOUNTER7 = 0xC07
    HPMCOUNTER8 = 0xC08
    HPMCOUNTER9 = 0xC09
    HPMCOUNTER10 = 0xC0A
    HPMCOUNTER11 = 0xC0B
    HPMCOUNTER12 = 0xC0C
    HPMCOUNTER13 = 0xC0D
    HPMCOUNTER14 = 0xC0E
    HPMCOUNTER15 = 0xC0F
    HPMCOUNTER16 = 0xC10
    HPMCOUNTER17 = 0xC11
    HPMCOUNTER18 = 0xC12
    HPMCOUNTER19 = 0xC13
    HPMCOUNTER20 = 0xC14
    HPMCOUNTER21 = 0xC15
    HPMCOUNTER22 = 0xC16
    HPMCOUNTER23 = 0xC17
    HPMCOUNTER24 = 0xC18
    HPMCOUNTER25 = 0xC19
    HPMCOUNTER26 = 0xC1A
    HPMCOUNTER27 = 0xC1B
    HPMCOUNTER28 = 0xC1C
    HPMCOUNTER29 = 0xC1D
    HPMCOUNTER30 = 0xC1E
    HPMCOUNTER31 = 0xC1F
    CYCLEH = 0xC80
    TIMEH = 0xC81
    INSTRETH = 0xC82
    HPMCOUNTER3H = 0xC83
    HPMCOUNTER4H = 0xC84
    HPMCOUNTER5H = 0xC85
    HPMCOUNTER6H = 0xC86
    HPMCOUNTER7H = 0xC87
    HPMCOUNTER8H = 0xC88
    HPMCOUNTER9H = 0xC89
    HPMCOUNTER10H = 0xC8A
    HPMCOUNTER11H = 0xC8B
    HPMCOUNTER12H = 0xC8C
    HPMCOUNTER13H = 0xC8D
    HPMCOUNTER14H = 0xC8E
    HPMCOUNTER15H = 0xC8F
    HPMCOUNTER16H = 0xC90
    HPMCOUNTER17H = 0xC91
    HPMCOUNTER18H = 0xC92
    HPMCOUNTER19H = 0xC93
    HPMCOUNTER20H = 0xC94
    HPMCOUNTER21H = 0xC95
    HPMCOUNTER22H = 0xC96
    HPMCOUNTER23H = 0xC97
    HPMCOUNTER24H = 0xC98
    HPMCOUNTER25H = 0xC99
    HPMCOUNTER26H = 0xC9A
    HPMCOUNTER27H = 0xC9B
    HPMCOUNTER28H = 0xC9C
    HPMCOUNTER29H = 0xC9D
    HPMCOUNTER30H = 0xC9E
    HPMCOUNTER31H = 0xC9F
    SSTATUS = 0x100
    SEDELEG = 0x102
    SIDELEG = 0x103
    SIE = 0x104
    STVEC = 0x105
    SCOUNTEREN = 0x106
    SSCRATCH = 0x140
    SEPC = 0x141
    SCAUSE = 0x142
    STVAL = 0x143
    SIP = 0x144
    SATP = 0x180
    MVENDORID = 0xF11
    MARCHID = 0xF12
    MIMPID = 0xF13
    MHARTID = 0xF14
    MSTATUS = 0x300
    MISA = 0x301
    MEDELEG = 0x302
    MIDELEG = 0x303
    MIE = 0x304
    MTVEC = 0x305
    MCOUNTEREN = 0x306
    MSCRATCH = 0x340
    MEPC = 0x341
    MCAUSE = 0x342
    MTVAL = 0x343
    MIP = 0x344
    PMPCFG0 = 0x3A0
    PMPCFG1 = 0x3A1
    PMPCFG2 = 0x3A2
    PMPCFG3 = 0x3A3
    PMPADDR0 = 0x3B0
    PMPADDR1 = 0x3B1
    PMPADDR2 = 0x3B2
    PMPADDR3 = 0x3B3
    PMPADDR4 = 0x3B4
    PMPADDR5 = 0x3B5
    PMPADDR6 = 0x3B6
    PMPADDR7 = 0x3B7
    PMPADDR8 = 0x3B8
    PMPADDR9 = 0x3B9
    PMPADDR10 = 0x3BA
    PMPADDR11 = 0x3BB
    PMPADDR12 = 0x3BC
    PMPADDR13 = 0x3BD
    PMPADDR14 = 0x3BE
    PMPADDR15 = 0x3BF
    MCYCLE = 0xB00
    MINSTRET = 0xB02
    MHPMCOUNTER3 = 0xB03
    MHPMCOUNTER4 = 0xB04
    MHPMCOUNTER5 = 0xB05
    MHPMCOUNTER6 = 0xB06
    MHPMCOUNTER7 = 0xB07
    MHPMCOUNTER8 = 0xB08
    MHPMCOUNTER9 = 0xB09
    MHPMCOUNTER10 = 0xB0A
    MHPMCOUNTER11 = 0xB0B
    MHPMCOUNTER12 = 0xB0C
    MHPMCOUNTER13 = 0xB0D
    MHPMCOUNTER14 = 0xB0E
    MHPMCOUNTER15 = 0xB0F
    MHPMCOUNTER16 = 0xB10
    MHPMCOUNTER17 = 0xB11
    MHPMCOUNTER18 = 0xB12
    MHPMCOUNTER19 = 0xB13
    MHPMCOUNTER20 = 0xB14
    MHPMCOUNTER21 = 0xB15
    MHPMCOUNTER22 = 0xB16
    MHPMCOUNTER23 = 0xB17
    MHPMCOUNTER24 = 0xB18
    MHPMCOUNTER25 = 0xB19
    MHPMCOUNTER26 = 0xB1A
    MHPMCOUNTER27 = 0xB1B
    MHPMCOUNTER28 = 0xB1C
    MHPMCOUNTER29 = 0xB1D
    MHPMCOUNTER30 = 0xB1E
    MHPMCOUNTER31 = 0xB1F
    MCYCLEH = 0xB80
    MINSTRETH = 0xB82
    MHPMCOUNTER3H = 0xB83
    MHPMCOUNTER4H = 0xB84
    MHPMCOUNTER5H = 0xB85
    MHPMCOUNTER6H = 0xB86
    MHPMCOUNTER7H = 0xB87
    MHPMCOUNTER8H = 0xB88
    MHPMCOUNTER9H = 0xB89
    MHPMCOUNTER10H = 0xB8A
    MHPMCOUNTER11H = 0xB8B
    MHPMCOUNTER12H = 0xB8C
    MHPMCOUNTER13H = 0xB8D
    MHPMCOUNTER14H = 0xB8E
    MHPMCOUNTER15H = 0xB8F
    MHPMCOUNTER17H = 0xB90
    MHPMCOUNTER18H = 0xB91
    MHPMCOUNTER19H = 0xB92
    MHPMCOUNTER20H = 0xB93
    MHPMCOUNTER21H = 0xB94
    MHPMCOUNTER22H = 0xB95
    MHPMCOUNTER23H = 0xB96
    MHPMCOUNTER24H = 0xB97
    MHPMCOUNTER25H = 0xB98
    MHPMCOUNTER26H = 0xB99
    MHPMCOUNTER27H = 0xB9A
    MHPMCOUNTER28H = 0xB9B
    MHPMCOUNTER29H = 0xB9C
    MHPMCOUNTER30H = 0xB9D
    MHPMCOUNTER31H = 0xB9E
    MCOUNTINHIBIT = 0x320F
    MHPMEVENT3 = 0x323
    MHPMEVENT4 = 0x324
    MHPMEVENT5 = 0x325
    MHPMEVENT6 = 0x326
    MHPMEVENT7 = 0x327
    MHPMEVENT8 = 0x328
    MHPMEVENT9 = 0x329
    MHPMEVENT10 = 0x32A
    MHPMEVENT11 = 0x32B
    MHPMEVENT12 = 0x32C
    MHPMEVENT13 = 0x32D
    MHPMEVENT14 = 0x32E
    MHPMEVENT15 = 0x32F
    MHPMEVENT16 = 0x330
    MHPMEVENT17 = 0x331
    MHPMEVENT18 = 0x332
    MHPMEVENT19 = 0x333
    MHPMEVENT20 = 0x334
    MHPMEVENT21 = 0x335
    MHPMEVENT22 = 0x336
    MHPMEVENT23 = 0x337
    MHPMEVENT24 = 0x338
    MHPMEVENT25 = 0x339
    MHPMEVENT26 = 0x33A
    MHPMEVENT27 = 0x33B
    MHPMEVENT28 = 0x33C
    MHPMEVENT29 = 0x33D
    MHPMEVENT30 = 0x33E
    MHPMEVENT31 = 0x33F
    TSELECT = 0x7A0
    TDATA1 = 0x7A1
    TDATA2 = 0x7A2
    TDATA3 = 0x7A3
    DCSR = 0x7B0
    DPC = 0x7B1
    DSCRATCH0 = 0x7B2
    DSCRATCH1 = 0x7B3
    VSTART = 0x008
    VXSTAT = 0x009
    VXRM = 0x00A
    VL = 0xC20
    VTYPE = 0xC21
    VLENB = 0xC22


class privileged_reg_fld_t(IntEnum):
    RSVD = 0
    MXL = auto()
    EXTENSION = auto()
    MODE = auto()
    ASID = auto()
    PPN = auto()


class privileged_level_t(IntEnum):
    M_LEVEL = 0b11
    S_LEVEL = 0b01
    U_LEVEL = 0b00


class reg_field_access_t(IntEnum):
    WPRI = 0
    WLRL = auto()
    WARL = auto()


class riscv_pseudo_instr_name_t(IntEnum):
    LI = 0
    LA = auto()


class data_pattern_t(IntEnum):
    RAND_DATA = 0
    ALL_ZERO = auto()
    INCR_VAL = auto()


class pte_permission_t(IntEnum):
    NEXT_LEVEL_PAGE = 0b000
    READ_ONLY_PAGE = 0b001
    READ_WRITE_PAGE = 0b011
    EXECUTE_ONLY_PAGE = 0b100
    READ_EXECUTE_PAGE = 0b101
    R_W_EXECUTE_PAGE = 0b111


class interrupt_cause_t(IntEnum):
    U_SOFTWARE_INTR = 0x0
    S_SOFTWARE_INTR = 0x1
    M_SOFTWARE_INTR = 0x3
    U_TIMER_INTR = 0x4
    S_TIMER_INTR = 0x5
    M_TIMER_INTR = 0x7
    U_EXTERNAL_INTR = 0x8
    S_EXTERNAL_INTR = 0x9
    M_EXTERNAL_INTR = 0xB


class exception_cause_t(IntEnum):
    INSTRUCTION_ADDRESS_MISALIGNED = 0x0
    INSTRUCTION_ACCESS_FAULT = 0x1
    ILLEGAL_INSTRUCTION = 0x2
    BREAKPOINT = 0x3
    LOAD_ADDRESS_MISALIGNED = 0x4
    LOAD_ACCESS_FAULT = 0x5
    STORE_AMO_ADDRESS_MISALIGNED = 0x6
    STORE_AMO_ACCESS_FAULT = 0x7
    ECALL_UMODE = 0x8
    ECALL_SMODE = 0x9
    ECALL_MMODE = 0xB
    INSTRUCTION_PAGE_FAULT = 0xC
    LOAD_PAGE_FAULT = 0xD
    STORE_AMO_PAGE_FAULT = 0xF


class misa_ext_t(IntEnum):
    MISA_EXT_A = 0
    MISA_EXT_B = auto()
    MISA_EXT_C = auto()
    MISA_EXT_D = auto()
    MISA_EXT_E = auto()
    MISA_EXT_F = auto()
    MISA_EXT_G = auto()
    MISA_EXT_H = auto()
    MISA_EXT_I = auto()
    MISA_EXT_J = auto()
    MISA_EXT_K = auto()
    MISA_EXT_L = auto()
    MISA_EXT_M = auto()
    MISA_EXT_N = auto()
    MISA_EXT_O = auto()
    MISA_EXT_P = auto()
    MISA_EXT_Q = auto()
    MISA_EXT_R = auto()
    MISA_EXT_S = auto()
    MISA_EXT_T = auto()
    MISA_EXT_U = auto()
    MISA_EXT_V = auto()
    MISA_EXT_W = auto()
    MISA_EXT_X = auto()
    MISA_EXT_Y = auto()
    MISA_EXT_Z = auto()


class hazard_e(IntEnum):
    NO_HAZARD = 0
    RAW_HAZARD = auto()
    WAR_HAZARD = auto()
    WAW_HAZARD = auto()


# TODO: ignore bins is not yet supported in pyvsc; extra enums will be removed
#  once support is added
# Ignore WAR/WAW_HAZARD for branch instructions
class branch_hazard_e(IntEnum):
    NO_HAZARD = 0
    RAW_HAZARD = auto()


# RV32I_MISC covergroup instructions
class rv32i_misc_instrs(IntEnum):
    FENCE = 0
    FENCE_I = auto()
    EBREAK = auto()
    ECALL = auto()
    MRET = auto()

# Ignore RAW_HAZARD for store lsu hazard


class store_lsu_hazard_e(IntEnum):
    NO_HAZARD = 0
    WAR_HAZARD = auto()
    WAW_HAZARD = auto()


# RA/T1 for rs1/rd_link in jalr instruction
class jalr_riscv_reg_t(IntEnum):
    RA = 0
    T1 = auto()


# Ignore ZERO as src1 of load instructions
class riscv_reg_ex_zero_t(IntEnum):
    RA = 0
    SP = auto()
    GP = auto()
    TP = auto()
    T0 = auto()
    T1 = auto()
    T2 = auto()
    S0 = auto()
    S1 = auto()
    A0 = auto()
    A1 = auto()
    A2 = auto()
    A3 = auto()
    A4 = auto()
    A5 = auto()
    A6 = auto()
    A7 = auto()
    S2 = auto()
    S3 = auto()
    S4 = auto()
    S5 = auto()
    S6 = auto()
    S7 = auto()
    S8 = auto()
    S9 = auto()
    S10 = auto()
    S11 = auto()
    T3 = auto()
    T4 = auto()
    T5 = auto()
    T6 = auto()


class pmp_addr_mode_t(Enum):
    OFF = 0b00
    TOR = 0b01
    NA4 = 0b10
    NAPOT = 0b11


class vtype_t(Enum):
    ill = 0
    reserved = auto()
    vediv = auto()
    vsew = auto()
    vlmul = auto()


class vxrm_t(Enum):
    RoundToNearestUp = 0
    RoundToNearestEven = auto()
    RoundDown = auto()
    RoundToOdd = auto()


class b_ext_group_t(Enum):
    ZBB = 0
    ZBS = auto()
    ZBP = auto()
    ZBE = auto()
    ZBF = auto()
    ZBC = auto()
    ZBR = auto()
    ZBM = auto()
    ZBT = auto()
    ZB_TMP = auto()


class all_gpr(Enum):
    ZERO = 0
    RA = auto()
    SP = auto()
    GP = auto()
    TP = auto()
    T0 = auto()
    T1 = auto()
    T2 = auto()
    S0 = auto()
    S1 = auto()
    A0 = auto()
    A1 = auto()
    A2 = auto()
    A3 = auto()
    A4 = auto()
    A5 = auto()
    A6 = auto()
    A7 = auto()
    S2 = auto()
    S3 = auto()
    S4 = auto()
    S5 = auto()
    S6 = auto()
    S7 = auto()
    S8 = auto()
    S9 = auto()
    S10 = auto()
    S11 = auto()
    T3 = auto()
    T4 = auto()
    T5 = auto()
    T6 = auto()


class compressed_gpr(Enum):
    S0 = 0
    S1 = auto()
    A0 = auto()
    A1 = auto()
    A2 = auto()
    A3 = auto()
    A4 = auto()
    A5 = auto()


class all_categories(Enum):
    LOAD = 0
    STORE = auto()
    SHIFT = auto()
    ARITHMETIC = auto()
    LOGICAL = auto()
    COMPARE = auto()
    BRANCH = auto()
    JUMP = auto()
    SYNCH = auto()
    SYSTEM = auto()
    COUNTER = auto()
    CSR = auto()
    CHANGELEVEL = auto()
    TRAP = auto()
    INTERRUPT = auto()
    AMO = auto()


def get_val(in_string, hexa=0):
    if len(in_string) > 2:
        if "0x" in in_string:
            out_val = int(in_string, base=16)
            return out_val
    if hexa:
        out_val = int(in_string, base=16)
    else:
        out_val = int(in_string)
    logging.info("imm: {} -> {}".format(in_string, out_val))
    return out_val


def get_attr_list(instr_name):
    switcher = {
        # LOAD instructions
        riscv_instr_name_t.LB: [riscv_instr_format_t.I_FORMAT,
                                riscv_instr_category_t.LOAD,
                                riscv_instr_group_t.RV32I],
        riscv_instr_name_t.LH: [riscv_instr_format_t.I_FORMAT,
                                riscv_instr_category_t.LOAD,
                                riscv_instr_group_t.RV32I],
        riscv_instr_name_t.LW: [riscv_instr_format_t.I_FORMAT,
                                riscv_instr_category_t.LOAD,
                                riscv_instr_group_t.RV32I],
        riscv_instr_name_t.LBU: [riscv_instr_format_t.I_FORMAT,
                                 riscv_instr_category_t.LOAD,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.LHU: [riscv_instr_format_t.I_FORMAT,
                                 riscv_instr_category_t.LOAD,
                                 riscv_instr_group_t.RV32I],
        # STORE instructions
        riscv_instr_name_t.SB: [riscv_instr_format_t.S_FORMAT,
                                riscv_instr_category_t.STORE,
                                riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SH: [riscv_instr_format_t.S_FORMAT,
                                riscv_instr_category_t.STORE,
                                riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SW: [riscv_instr_format_t.S_FORMAT,
                                riscv_instr_category_t.STORE,
                                riscv_instr_group_t.RV32I],
        # SHIFT intructions
        riscv_instr_name_t.SLL: [riscv_instr_format_t.R_FORMAT,
                                 riscv_instr_category_t.SHIFT,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SLLI: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.SHIFT,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SRL: [riscv_instr_format_t.R_FORMAT,
                                 riscv_instr_category_t.SHIFT,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SRLI: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.SHIFT,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SRA: [riscv_instr_format_t.R_FORMAT,
                                 riscv_instr_category_t.SHIFT,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SRAI: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.SHIFT,
                                  riscv_instr_group_t.RV32I],
        # ARITHMETIC intructions
        riscv_instr_name_t.ADD: [riscv_instr_format_t.R_FORMAT,
                                 riscv_instr_category_t.ARITHMETIC,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.ADDI: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.ARITHMETIC,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.NOP: [riscv_instr_format_t.I_FORMAT,
                                 riscv_instr_category_t.ARITHMETIC,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SUB: [riscv_instr_format_t.R_FORMAT,
                                 riscv_instr_category_t.ARITHMETIC,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.LUI: [riscv_instr_format_t.U_FORMAT,
                                 riscv_instr_category_t.ARITHMETIC,
                                 riscv_instr_group_t.RV32I, imm_t.UIMM],
        riscv_instr_name_t.AUIPC: [riscv_instr_format_t.U_FORMAT,
                                   riscv_instr_category_t.ARITHMETIC,
                                   riscv_instr_group_t.RV32I, imm_t.UIMM],
        # LOGICAL instructions
        riscv_instr_name_t.XOR: [riscv_instr_format_t.R_FORMAT,
                                 riscv_instr_category_t.LOGICAL,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.XORI: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.LOGICAL,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.OR: [riscv_instr_format_t.R_FORMAT,
                                riscv_instr_category_t.LOGICAL,
                                riscv_instr_group_t.RV32I],
        riscv_instr_name_t.ORI: [riscv_instr_format_t.I_FORMAT,
                                 riscv_instr_category_t.LOGICAL,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.AND: [riscv_instr_format_t.R_FORMAT,
                                 riscv_instr_category_t.LOGICAL,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.ANDI: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.LOGICAL,
                                  riscv_instr_group_t.RV32I],
        # COMPARE instructions
        riscv_instr_name_t.SLT: [riscv_instr_format_t.R_FORMAT,
                                 riscv_instr_category_t.COMPARE,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SLTI: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.COMPARE,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SLTU: [riscv_instr_format_t.R_FORMAT,
                                  riscv_instr_category_t.COMPARE,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SLTIU: [riscv_instr_format_t.I_FORMAT,
                                   riscv_instr_category_t.COMPARE,
                                   riscv_instr_group_t.RV32I],
        # BRANCH instructions
        riscv_instr_name_t.BEQ: [riscv_instr_format_t.B_FORMAT,
                                 riscv_instr_category_t.BRANCH,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.BNE: [riscv_instr_format_t.B_FORMAT,
                                 riscv_instr_category_t.BRANCH,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.BLT: [riscv_instr_format_t.B_FORMAT,
                                 riscv_instr_category_t.BRANCH,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.BGE: [riscv_instr_format_t.B_FORMAT,
                                 riscv_instr_category_t.BRANCH,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.BLTU: [riscv_instr_format_t.B_FORMAT,
                                  riscv_instr_category_t.BRANCH,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.BGEU: [riscv_instr_format_t.B_FORMAT,
                                  riscv_instr_category_t.BRANCH,
                                  riscv_instr_group_t.RV32I],
        # JUMP instructions
        riscv_instr_name_t.JAL: [riscv_instr_format_t.J_FORMAT,
                                 riscv_instr_category_t.JUMP,
                                 riscv_instr_group_t.RV32I],
        riscv_instr_name_t.JALR: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.JUMP,
                                  riscv_instr_group_t.RV32I],
        # SYNCH instructions
        riscv_instr_name_t.FENCE: [riscv_instr_format_t.I_FORMAT,
                                   riscv_instr_category_t.SYNCH,
                                   riscv_instr_group_t.RV32I],
        riscv_instr_name_t.FENCE_I: [riscv_instr_format_t.I_FORMAT,
                                     riscv_instr_category_t.SYNCH,
                                     riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SFENCE_VMA: [riscv_instr_format_t.R_FORMAT,
                                        riscv_instr_category_t.SYNCH,
                                        riscv_instr_group_t.RV32I],
        # SYSTEM instructions
        riscv_instr_name_t.ECALL: [riscv_instr_format_t.I_FORMAT,
                                   riscv_instr_category_t.SYSTEM,
                                   riscv_instr_group_t.RV32I],
        riscv_instr_name_t.EBREAK: [riscv_instr_format_t.I_FORMAT,
                                    riscv_instr_category_t.SYSTEM,
                                    riscv_instr_group_t.RV32I],
        riscv_instr_name_t.URET: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.SYSTEM,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.SRET: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.SYSTEM,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.MRET: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.SYSTEM,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.DRET: [riscv_instr_format_t.I_FORMAT,
                                  riscv_instr_category_t.SYSTEM,
                                  riscv_instr_group_t.RV32I],
        riscv_instr_name_t.WFI: [riscv_instr_format_t.I_FORMAT,
                                 riscv_instr_category_t.INTERRUPT,
                                 riscv_instr_group_t.RV32I],
        # CSR instructions
        riscv_instr_name_t.CSRRW: [riscv_instr_format_t.R_FORMAT,
                                   riscv_instr_category_t.CSR,
                                   riscv_instr_group_t.RV32I, imm_t.UIMM],
        riscv_instr_name_t.CSRRS: [riscv_instr_format_t.R_FORMAT,
                                   riscv_instr_category_t.CSR,
                                   riscv_instr_group_t.RV32I, imm_t.UIMM],
        riscv_instr_name_t.CSRRC: [riscv_instr_format_t.R_FORMAT,
                                   riscv_instr_category_t.CSR,
                                   riscv_instr_group_t.RV32I, imm_t.UIMM],
        riscv_instr_name_t.CSRRWI: [riscv_instr_format_t.I_FORMAT,
                                    riscv_instr_category_t.CSR,
                                    riscv_instr_group_t.RV32I, imm_t.UIMM],
        riscv_instr_name_t.CSRRSI: [riscv_instr_format_t.I_FORMAT,
                                    riscv_instr_category_t.CSR,
                                    riscv_instr_group_t.RV32I, imm_t.UIMM],
        riscv_instr_name_t.CSRRCI: [riscv_instr_format_t.I_FORMAT,
                                    riscv_instr_category_t.CSR,
                                    riscv_instr_group_t.RV32I, imm_t.UIMM],
    }
    # if instruction is not present in the dictionary,second argument well
    # be assigned as default value of passed argument
    attr_list = switcher.get(instr_name, "Cannot find instruction")
    return attr_list


def add_functions_as_methods(function):
    def decorator(Class):
        setattr(Class, function.__name__, function)
        return Class

    return decorator


class riscv_instr_pkg:
    global rcs
    from pygen_src.riscv_instr_gen_config import cfg
    rcs = import_module("pygen_src.target." + cfg.argv.target + ".riscv_core_setting")

    MPRV_BIT_MASK = BitArray(uint=0x1 << 0x17, length=rcs.XLEN)
    SUM_BIT_MASK = BitArray(uint=0x1 << 0x18, length=rcs.XLEN)
    MPP_BIT_MASK = BitArray(uint=0x3 << 0x11, length=rcs.XLEN)
    MAX_USED_VADDR_BITS = 30
    IMM25_WIDTH = 25
    IMM12_WIDTH = 12
    INSTR_WIDTH = 32
    DATA_WIDTH = 32
    MAX_INSTR_STR_LEN = 11
    LABEL_STR_LEN = 18
    MAX_CALLSTACK_DEPTH = 20
    MAX_SUB_PROGRAM_CNT = 20
    MAX_CALL_PER_FUNC = 5
    indent = LABEL_STR_LEN * " "

    def hart_prefix(self, hart=0):
        if (rcs.NUM_HARTS <= 1):
            return ""
        else:
            return f"h{hart}_"

    def get_label(self, label, hart=0):
        return (self.hart_prefix(hart) + label)

    def format_string(self, string, length=10):
        formatted_str = length * " "
        if (int(length) < len(string)):
            return string
        formatted_str = string + formatted_str[0: (int(length) - len(string))]
        return formatted_str

    def format_data(self, data, byte_per_group=4):
        string = "0x"
        for i in range(len(data)):
            if ((i % byte_per_group == 0) and (i != len(data) - 1) and (
                    i != 0)):
                string = string + ", 0x"
            string = string + "{:02x}".format(data[i])
        return string

    def push_gpr_to_kernel_stack(self, status, scratch, mprv, sp, tp, instr):
        store_instr = ''
        if(rcs.XLEN == 32):
            store_instr = "sw"
        else:
            store_instr = "sd"
        if (scratch.name in rcs.implemented_csr):
            # Use kernal stack for handling exceptions. Save the user mode stack
            # pointer to the scratch register
            instr.append(pkg_ins.format_string(
                "csrrw x{}, {}, x{}".format(sp, hex(scratch.value), sp)))
            # Move TP to SP
            instr.append(pkg_ins.format_string("add x{}, x{}, zero".format(sp, tp)))
        # If MPRV is set and MPP is S/U mode, it means the address translation and
        # memory protection for load/store instruction is the same as the mode indicated
        # by MPP. In this case, we need to use the virtual address to access the kernel stack.
        if((status.name == "MSTATUS") and (rcs.SATP_MODE != "BARE")):
            # We temporarily use tp to check mstatus to avoid changing other GPR. The value
            # of sp has been saved to xScratch and can be restored later.
            if(mprv):
                instr.append(pkg_ins.format_string(
                    "csrr x{}, 0x{} // MSTATUS".format(tp, status.value)))
                instr.append(pkg_ins.format_string(
                    "srli x{}, x{}, 11".format(tp, tp)))  # Move MPP to bit 0
                instr.append(pkg_ins.format_string(
                    "andi x{}, x{}, 0x3".format(tp, tp)))  # keep the MPP bits
                # Check if MPP equals to M-mode('b11)
                instr.append(pkg_ins.format_string("xori x{}, x{}, 0x3".format(tp, tp)))
                # Use physical address for kernel SP
                instr.append(pkg_ins.format_string("bnez x{}, 1f".format(tp)))
                # Use virtual address for stack pointer
                instr.append(pkg_ins.format_string(
                    "slli x{}, x{}, {}".format(sp, sp,
                                               rcs.XLEN - riscv_instr_pkg.MAX_USED_VADDR_BITS)))
                instr.append(pkg_ins.format_string(
                    "srli x{}, x{}, {}".format(sp, sp,
                                               rcs.XLEN - riscv_instr_pkg.MAX_USED_VADDR_BITS)))
        # Reserve space from kernel stack to save all 32 GPR except for x0
        instr.append(pkg_ins.format_string(
            "1: addi x{}, x{}, -{}".format(sp, sp, int(31 * (rcs.XLEN / 8)))))
        # Push all GPRs to kernel stack
        for i in range(1, 32):
            instr.append(pkg_ins.format_string("{} x{}, {}(x{})".format(
                store_instr, i, int(i * (rcs.XLEN / 8)), sp)))

    def pop_gpr_from_kernel_stack(self, status, scratch, mprv, sp, tp, instr):
        load_instr = ''
        if(rcs.XLEN == 32):
            load_instr = "lw"
        else:
            load_instr = "ld"
        # Pop user mode GPRs from kernel stack
        for i in range(1, 32):
            instr.append(pkg_ins.format_string("{} x{}, {}(x{})".format(
                load_instr, i, int(i * (rcs.XLEN / 8)), sp)))
        # Restore kernel stack pointer
        instr.append(pkg_ins.format_string(
            "addi x{}, x{}, {}".format(sp, sp, int(31 * (rcs.XLEN / 8)))))
        if (scratch in rcs.implemented_csr):
            # Move SP to TP
            instr.append(pkg_ins.format_string("add x{}, x{}, zero".format(tp, sp)))
            # Restore user mode stack pointer
            instr.append(pkg_ins.format_string(
                "csrrw x{}, 0x{}, x{}".format(sp, scratch.value, sp)))


pkg_ins = riscv_instr_pkg()
