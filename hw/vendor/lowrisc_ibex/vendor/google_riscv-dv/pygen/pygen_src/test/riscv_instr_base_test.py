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
See the License for the specific language governing permissions and
limitations under the License.
Regression script for RISC-V random instruction generator

"""

import sys
sys.path.append("../../")
from pygen_src.isa.rv32i_instr import * # NOQA
from pygen_src.isa.riscv_instr import cfg, riscv_instr_ins # NOQA


class riscv_instr_base_test:
    def __init__(self):
        pass

    for _ in range(cfg.num_of_test):
        riscv_instr_ins.create_instr_list(cfg)
