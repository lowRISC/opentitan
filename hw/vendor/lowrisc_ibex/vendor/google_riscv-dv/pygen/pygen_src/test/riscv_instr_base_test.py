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

import sys
sys.path.append("../../")
from pygen_src.riscv_instr_gen_config import cfg  # NOQA
from pygen_src.isa.rv32i_instr import *  # NOQA
from pygen_src.isa.riscv_instr import riscv_instr_ins  # NOQA
from pygen_src.riscv_asm_program_gen import riscv_asm_program_gen  # NOQA


class riscv_instr_base_test:
    def __init__(self):
        pass

    for _ in range(cfg.num_of_tests):
        cfg.randomize()
        asm = riscv_asm_program_gen()
        riscv_instr_ins.create_instr_list(cfg)
        test_name = "riscv_arithmetic_basic_test_{}.S".format(_)
        asm.get_directed_instr_stream()
        asm.gen_program()
        asm.gen_test_file(test_name)
