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
import vsc
import random
from collections import defaultdict
from pygen_src.riscv_instr_pkg import pkg_ins, data_pattern_t
from pygen_src.riscv_instr_gen_config import cfg


@vsc.randobj
class riscv_data_page_gen:
    def __init__(self):
        self.data_page_str = []
        self.mem_region_setting = defaultdict(list)

    @staticmethod
    def gen_data(idx, pattern, num_of_bytes, data):
        temp_data = 0
        data = [0] * num_of_bytes
        for i in range(len(data)):
            if pattern == data_pattern_t.RAND_DATA:
                temp_data = random.randrange(0, (2**8) - 1)
                data[i] = temp_data
            elif pattern == data_pattern_t.INCR_VAL:
                data[i] = (idx + i) % 256
        return data

    def gen_data_page(self, hart_id, pattern, is_kernel=0, amo=0):
        tmp_str = ""
        temp_data = []
        page_size = 0
        self.data_page_str.clear()
        if is_kernel:
            self.mem_region_setting = cfg.s_mem_region
        elif amo:
            self.mem_region_setting = cfg.amo_region
        else:
            self.mem_region_setting = cfg.mem_region
        for i in range(len(self.mem_region_setting)):
            logging.info("mem_region_setting {}".format(self.mem_region_setting[i]))
        for i in range(len(self.mem_region_setting)):
            logging.info("Generate data section: {} size:0x{} xwr:0x{}".format(
                         self.mem_region_setting[i].name,
                         self.mem_region_setting[i].size_in_bytes,
                         self.mem_region_setting[i].xwr))
            if amo:
                if cfg.use_push_data_section:
                    self.data_page_str.append(".pushsection .{},\"aw\",@progbits;"
                                              .format(self.mem_region_setting[i].name))
                else:
                    self.data_page_str.append(".section .{},\"aw\",@progbits;"
                                              .format(self.mem_region_setting[i].name))
                self.data_page_str.append("{}:".format(self.mem_region_setting[i].name))
            else:
                if cfg.use_push_data_section:
                    self.data_page_str.append(".pushsection .{},\"aw\",@progbits;"
                                              .format(pkg_ins.hart_prefix(hart_id) +
                                                      self.mem_region_setting[i].name))
                else:
                    self.data_page_str.append(".section .{},\"aw\",@progbits;"
                                              .format(pkg_ins.hart_prefix(hart_id) +
                                                      self.mem_region_setting[i].name))
                self.data_page_str.append("{}:".format(pkg_ins.hart_prefix(hart_id) +
                                                       self.mem_region_setting[i].name))
            page_size = self.mem_region_setting[i].size_in_bytes
            for i in range(0, page_size, 32):
                if page_size - 1 >= 32:
                    temp_data = self.gen_data(idx=i, pattern=pattern,
                                              num_of_bytes=32, data=temp_data)
                else:
                    temp_data = self.gen_data(idx=i, pattern=pattern,
                                              num_of_bytes=page_size - 1, data=temp_data)
                tmp_str = pkg_ins.format_string(".word {}".format(pkg_ins.format_data(temp_data)),
                                                pkg_ins.LABEL_STR_LEN)
                self.data_page_str.append(tmp_str)
                if cfg.use_push_data_section:
                    self.data_page_str.append(".popsection")
