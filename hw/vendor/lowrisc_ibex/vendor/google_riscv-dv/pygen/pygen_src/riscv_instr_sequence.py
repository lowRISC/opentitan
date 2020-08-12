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
from pygen_src.riscv_instr_stream import riscv_rand_instr_stream
from pygen_src.riscv_instr_pkg import pkg_ins


class riscv_instr_sequence:

    def __init__(self):
        self.instr_cnt = 0
        self.instr_stream = riscv_rand_instr_stream()
        self.is_main_program = 0
        self.is_debug_program = 0
        self.label_name = ""
        self.instr_string_list = []  # Save the instruction list
        self.program_stack_len = 0  # Stack space allocated for this program
        self.directed_instr = []    # List of all directed instruction stream
        self.illegal_instr_pct = 0  # Percentage of illegal instructions
        self.hint_instr_pct = 0     # Percentage of hint instructions

    def gen_instr(self, is_main_program, no_branch = 1):
        self.is_main_program = is_main_program
        self.instr_stream.initialize_instr_list(self.instr_cnt)
        logging.info("Start generating %d instruction" % len(self.instr_stream.instr_list))
        self.instr_stream.gen_instr(no_branch = no_branch, no_load_store = 1,
                                    is_debug_program = self.is_debug_program)

        if not is_main_program:
            self.gen_stack_enter_instr()
            self.gen_stack_exit_instr()

    # TODO
    def gen_stack_enter_instr(self):
        pass

    # TODO
    def gen_stack_exit_instr(self):
        pass

    # TODO
    def post_process_instr(self):
        pass

    # TODO
    def insert_jump_instr(self):
        pass

    def generate_instr_stream(self, no_label = 0):
        prefix = ''
        string = ''
        self.instr_string_list.clear()

        for i in range(len(self.instr_stream.instr_list)):
            if i == 0:
                if no_label:
                    prefix = pkg_ins.format_string(string = ' ', length = pkg_ins.LABEL_STR_LEN)
                else:
                    prefix = pkg_ins.format_string(string = '{}:'.format(
                        self.label_name), length = pkg_ins.LABEL_STR_LEN)

                self.instr_stream.instr_list[i].has_label = 1
            else:
                if(self.instr_stream.instr_list[i].has_label):
                    prefix = pkg_ins.format_string(string = '{}'.format(
                        self.instr_stream.instr_list[i].label), length = pkg_ins.LABEL_STR_LEN)
                else:
                    prefix = pkg_ins.format_string(string = " ", length = pkg_ins.LABEL_STR_LEN)
            string = prefix + self.instr_stream.instr_list[i].convert2asm()
            self.instr_string_list.append(string)

    # TODO
    def generate_return_routine(self):
        pass

    # TODO
    def insert_illegal_hint_instr(self):
        pass
