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
import logging
import time
import random
import traceback
import multiprocessing
sys.path.append("pygen/")
from pygen_src.riscv_instr_pkg import *
from pygen_src.riscv_instr_gen_config import cfg  # NOQA
for isa in rcs.supported_isa:
    import_module("pygen_src.isa." + isa.name.lower() + "_instr")
from pygen_src.isa.riscv_instr import riscv_instr  # NOQA
from pygen_src.riscv_asm_program_gen import riscv_asm_program_gen  # NOQA
from pygen_src.riscv_utils import gen_config_table


# Base test
class riscv_instr_base_test:
    def __init__(self):
        self.start_idx = cfg.argv.start_idx
        self.asm_file_name = cfg.argv.asm_file_name
        self.asm = ""

    def run(self):
        with multiprocessing.Pool(processes = cfg.num_of_tests) as pool:
            ret = pool.map(self.run_phase, list(range(cfg.num_of_tests)))
        if 1 in ret:
            raise Exception("Test-generation jobs failed")

    def run_phase(self, num):
        try:
            self._run_phase(num)
            return 0
        except Exception as e:
            traceback.print_exc()
            return 1

    def _run_phase(self, num):
        if num == 0:
            '''Get the user specified seed value otherwise
               generate a random seed value from SeedGen method of run.py'''
            rand_seed = cfg.argv.seed.split("--")[0]
        else:
            # Generate random seed value everytime for multiple test iterations
            rand_seed = random.getrandbits(31)
        # Assign the global seed value for a particular iteration
        random.seed(rand_seed)
        self.randomize_cfg()
        self.asm = riscv_asm_program_gen()
        riscv_instr.create_instr_list(cfg)
        if cfg.asm_test_suffix != "":
            self.asm_file_name = "{}.{}".format(self.asm_file_name,
                                                cfg.asm_test_suffix)
        self.asm.get_directed_instr_stream()
        test_name = "{}_{}.S".format(self.asm_file_name,
                                     num + self.start_idx)
        self.apply_directed_instr()
        logging.info("All directed instruction is applied")
        self.asm.gen_program()
        self.asm.gen_test_file(test_name)
        logging.info("TEST GENERATED USING SEED VALUE = {}".format(rand_seed))
        logging.info("TEST GENERATION DONE")

    def randomize_cfg(self):
        cfg.randomize()
        logging.info("riscv_instr_gen_config is randomized")
        gen_config_table()

    def apply_directed_instr(self):
        pass


start_time = time.time()
riscv_base_test_ins = riscv_instr_base_test()
if cfg.argv.gen_test == "riscv_instr_base_test":
    riscv_base_test_ins.run()
    end_time = time.time()
    logging.info("Total execution time: {}s".format(round(end_time - start_time)))
