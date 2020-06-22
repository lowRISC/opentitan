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


class riscv_instr_gen_config:
    def __init__(self):
        self.enable_floating_point = 1
        self.disable_compressed_instr = 1
        self.num_of_test = 3
        self.no_fence = 1
        self.enable_sfence = 0
        self.reserved_regs = []
        self.enable_illegal_csr_instruction = 0
        self.enable_access_invalid_csr_level = 0
        self.invalid_priv_mode_csrs = []
        self.init_privileged_mode = "MACHINE_MODE"
        self.no_ebreak = 1
        self.no_dret = 1
        self.no_csr_instr = 1
        self.no_wfi = 1
