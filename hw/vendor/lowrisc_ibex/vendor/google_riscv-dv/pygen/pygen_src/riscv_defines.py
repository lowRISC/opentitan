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

from pygen_src.riscv_instr_pkg import imm_t
from pygen_src.isa.riscv_instr import riscv_instr
from pygen_src.isa.riscv_compressed_instr import riscv_compressed_instr
from pygen_src.isa.riscv_floating_point_instr import riscv_floating_point_instr
from pygen_src.isa.riscv_b_instr import riscv_b_instr
from pygen_src.isa.riscv_amo_instr import riscv_amo_instr


# Regular integer instruction
def DEFINE_INSTR(instr_n, instr_format, instr_category,
                 instr_group, imm_tp = imm_t.IMM, g = globals()):
    class_name = "riscv_{}_instr".format(instr_n.name)

    def __init__(self):
        riscv_instr.__init__(self)
        self.instr_name = instr_n
        self.format = instr_format
        self.category = instr_category
        self.group = instr_group
        self.imm_type = imm_tp

        self.set_imm_len()
        self.set_rand_mode()
    NewClass = type(class_name, (riscv_instr,), {
        "__init__": __init__,
        "valid": riscv_instr.register(instr_n, instr_group)
    })
    g[class_name] = NewClass


# Compressed instruction
def DEFINE_C_INSTR(instr_n, instr_format, instr_category,
                   instr_group, imm_tp = imm_t.IMM, g = globals()):
    class_name = "riscv_{}_instr".format(instr_n.name)

    def __init__(self):
        riscv_compressed_instr.__init__(self)
        self.instr_name = instr_n
        self.format = instr_format
        self.category = instr_category
        self.group = instr_group
        self.imm_type = imm_tp
        self.set_imm_len()
        self.set_rand_mode()
    NewClass = type(class_name, (riscv_compressed_instr,), {
        "__init__": __init__,
        "valid": riscv_compressed_instr.register(instr_n, instr_group)
    })
    g[class_name] = NewClass


# Floating point instruction
def DEFINE_FP_INSTR(instr_n, instr_format, instr_category,
                    instr_group, imm_tp = imm_t.IMM, g = globals()):
    class_name = "riscv_{}_instr".format(instr_n.name)

    def __init__(self):
        riscv_floating_point_instr.__init__(self)
        self.instr_name = instr_n
        self.format = instr_format
        self.category = instr_category
        self.group = instr_group
        self.imm_type = imm_tp
        self.set_imm_len()
        self.set_rand_mode()
    NewClass = type(class_name, (riscv_floating_point_instr,), {
        "__init__": __init__,
        "valid": riscv_floating_point_instr.register(instr_n, instr_group)
    })
    g[class_name] = NewClass


# Floating point compressed instruction
def DEFINE_FC_INSTR(instr_n, instr_format, instr_category,
                    instr_group, imm_tp = imm_t.IMM, g = globals()):
    class_name = "riscv_{}_instr".format(instr_n.name)

    def __init__(self):
        riscv_compressed_instr.__init__(self)
        self.instr_name = instr_n
        self.format = instr_format
        self.category = instr_category
        self.group = instr_group
        self.imm_type = imm_tp
        self.set_imm_len()
        self.set_rand_mode()
    NewClass = type(class_name, (riscv_compressed_instr,), {
        "__init__": __init__,
        "valid": riscv_compressed_instr.register(instr_n, instr_group)
    })
    g[class_name] = NewClass


# B-extension instruction
def DEFINE_B_INSTR(instr_n, instr_format, instr_category,
                   instr_group, imm_tp = imm_t.IMM, g = globals()):
    class_name = "riscv_{}_instr".format(instr_n.name)

    def __init__(self):
        riscv_b_instr.__init__(self)
        self.instr_name = instr_n
        self.format = instr_format
        self.category = instr_category
        self.group = instr_group
        self.imm_type = imm_tp
        self.set_imm_len()
        self.set_rand_mode()
    NewClass = type(class_name, (riscv_b_instr,), {
        "__init__": __init__,
        "valid": riscv_b_instr.register(instr_n, instr_group)
    })
    g[class_name] = NewClass


# A-extension instruction
def DEFINE_AMO_INSTR(instr_n, instr_format, instr_category,
                     instr_group, imm_tp = imm_t.IMM, g = globals()):
    class_name = "riscv_{}_instr".format(instr_n.name)

    def __init__(self):
        riscv_amo_instr.__init__(self)
        self.instr_name = instr_n
        self.format = instr_format
        self.category = instr_category
        self.group = instr_group
        self.imm_type = imm_tp
        self.set_imm_len()
        self.set_rand_mode()
    NewClass = type(class_name, (riscv_amo_instr,), {
        "__init__": __init__,
        "valid": riscv_amo_instr.register(instr_n, instr_group)
    })
    g[class_name] = NewClass


'''
TODO
@vsc.constraint
def add_pseudo_instr(self, instr_n, instr_format, instr_category, instr_group):
        with vsc.if_then(self.pseudo_instr_name == instr_n):
            self.format == instr_format.name
            self.category == instr_category.name
            self.group == instr_group.name
'''
