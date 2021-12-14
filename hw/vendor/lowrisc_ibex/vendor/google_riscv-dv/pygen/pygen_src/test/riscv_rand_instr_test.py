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
import time
import logging
sys.path.append("pygen/")
from pygen_src.test.riscv_instr_base_test import riscv_instr_base_test
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_utils import gen_config_table


class riscv_rand_instr_test(riscv_instr_base_test):
    def __init__(self):
        super().__init__()

    def randomize_cfg(self):
        cfg.instr_cnt = 10000
        cfg.num_of_sub_program = 5
        cfg.randomize()
        logging.info("riscv_instr_gen_config is randomized")
        gen_config_table()

    def apply_directed_instr(self):
        # Mix below directed instruction streams with the random instructions
        self.asm.add_directed_instr_stream("riscv_load_store_rand_instr_stream", 4)
        # self.asm.add_directed_instr_stream("riscv_loop_instr", 3)
        self.asm.add_directed_instr_stream("riscv_jal_instr", 4)
        # self.asm.add_directed_instr_stream("riscv_hazard_instr_stream", 4)
        self.asm.add_directed_instr_stream("riscv_load_store_hazard_instr_stream", 4)
        # self.asm.add_directed_instr_stream("riscv_multi_page_load_store_instr_stream", 4)
        # self.asm.add_directed_instr_stream("riscv_mem_region_stress_test", 4)


start_time = time.time()
riscv_rand_test_ins = riscv_rand_instr_test()
riscv_rand_test_ins.run()
end_time = time.time()
logging.info("Total execution time: {}s".format(round(end_time - start_time)))
