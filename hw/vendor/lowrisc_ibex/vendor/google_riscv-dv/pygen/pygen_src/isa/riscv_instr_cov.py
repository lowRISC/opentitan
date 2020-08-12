import sys
import vsc
import logging
from enum import Enum, auto
from pygen_src.riscv_instr_pkg import riscv_reg_t

class operand_sign_e(Enum):
    POSITIVE = 0
    NEGATIVE = auto()

class div_result_e(Enum):
    DIV_NORMAL = 0
    DIV_BY_ZERO = auto()
    DIV_OVERFLOW = auto()

class compare_result_e(Enum):
    EQUAL = 0
    LARGER = auto()
    SMALLER = auto()

class logical_similarity_e(Enum):
    IDENTICAL = 0
    OPPOSITE = auto()
    SIMILAR = auto()
    DIFFERENT = auto()

class special_val_e(Enum):
    NORMAL_VAL = 0
    MIN_VAL = auto()
    MAX_VAL = auto()
    ZERO_VAL = auto()


def get_gpr(reg_name):
    reg_name = reg_name.upper()
    if not reg_name in riscv_reg_t:
        logging.fatal("Cannot convert {} to GPR".format(reg_name))
    return riscv_reg_t[reg_name]

def get_gpr_state(reg_name):
    if reg_name in ["zero", "x0"]:
        return 0
    elif reg_name in gpr_state:
        return gpr_state[reg_name]
    else:
        logging.warning("Cannot find GPR state: {}".format(reg_name))
