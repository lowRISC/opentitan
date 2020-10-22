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
import random
from collections import defaultdict
from pygen_src.riscv_instr_stream import riscv_rand_instr_stream
from pygen_src.riscv_instr_gen_config import cfg
from pygen_src.riscv_instr_pkg import pkg_ins, riscv_instr_category_t


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
        self.branch_idx = [None] * 30

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

    '''
    ----------------------------------------------------------------------------------------------
    Instruction post-process

    Post-process is required for branch instructions:

    Need to assign a valid branch target. This is done by picking a random instruction label in
    this sequence and assigning to the branch instruction. All the non-atomic instructions
    will have a unique numeric label as the local branch target identifier.
    The atomic instruction streams don't have labels except for the first instruction. This is
    to avoid branching into an atomic instruction stream which breaks its atomicy. The
    definition of an atomic instruction stream here is a sequence of instructions which must be
    executed in-order.
    In this sequence, only forward branch is handled. The backward branch target is implemented
    in a dedicated loop instruction sequence. Randomly choosing a backward branch target could
    lead to dead loops in the absence of proper loop exiting conditions.
    ----------------------------------------------------------------------------------------------
    '''

    def post_process_instr(self):
        label_idx = 0
        branch_cnt = 0
        j = 0
        branch_target = defaultdict(lambda: None)

        for instr in self.directed_instr:
            self.instr_stream.insert_instr_stream(instr.instr_list)
        '''
        Assign an index for all instructions, these indexes wont change
        even a new instruction is injected in the post process.
        '''
        for i in range(len(self.instr_stream.instr_list)):
            self.instr_stream.instr_list[i].idx = label_idx
            if(self.instr_stream.instr_list[i].has_label and
                    not(self.instr_stream.instr_list[i].atomic)):
                if((self.illegal_instr_pct > 0) and
                   (self.instr_stream.instr_list[i].insert_illegal_instr == 0)):
                    '''
                    The illegal instruction generator always increase PC by 4 when resume execution,
                    need to make sure PC + 4 is at the correct instruction boundary.
                    '''
                    if(self.instr_stream.instr_list[i].is_compressed):
                        if(i < (len(self.instr_stream.instr_list) - 1)):
                            if(self.instr_stream.instr_list[i + 1].is_compressed):
                                self.instr_stream.instr_list[i].is_illegal_instr = random.randrange(
                                    0, min(100, self.illegal_instr_pct))
                    else:
                        self.instr_stream.instr_list[i].is_illegal_instr = random.randrange(
                            0, min(100, self.illegal_instr_pct))
                if(self.hint_instr_pct > 0 and
                        (self.instr_stream.instr_list[i].is_illegal_instr == 0)):
                    if(self.instr_stream.instr_list[i].is_compressed):
                        self.instr_stream.instr_list[i].is_hint_instr = random.randrange(
                            0, min(100, self.hint_instr_pct))

                self.instr_stream.instr_list[i].label = "{}".format(label_idx)
                self.instr_stream.instr_list[i].is_local_numeric_label = 1
                label_idx += 1

        # Generate branch target
        for i in range(len(self.branch_idx)):
            self.branch_idx[i] = random.randint(1, cfg.max_branch_step)

        while(j < len(self.instr_stream.instr_list)):
            if((self.instr_stream.instr_list[j].category == riscv_instr_category_t.BRANCH) and
                    (not self.instr_stream.instr_list[j].branch_assigned) and
                    (not self.instr_stream.instr_list[j].is_illegal_instr)):
                '''
                Post process the branch instructions to give a valid local label
                Here we only allow forward branch to avoid unexpected infinite loop
                The loop structure will be inserted with a separate routine using
                reserved loop registers
                '''
                branch_target_label = 0
                branch_byte_offset = 0
                branch_target_label = self.instr_stream.instr_list[j].idx + \
                    self.branch_idx[branch_cnt]
                if(branch_target_label >= label_idx):
                    branch_target_label = label_idx - 1
                branch_cnt += 1
                if(branch_cnt == len(self.branch_idx)):
                    branch_cnt = 0
                    random.shuffle(self.branch_idx)
                logging.info("Processing branch instruction[%0d]:%0s # %0d -> %0d", j,
                             self.instr_stream.instr_list[j].convert2asm(),
                             self.instr_stream.instr_list[j].idx, branch_target_label)
                self.instr_stream.instr_list[j].imm_str = "{}f".format(branch_target_label)
                self.instr_stream.instr_list[j].branch_assigned = 1
                branch_target[branch_target_label] = 1

            # Remove the local label which is not used as branch target
            if(self.instr_stream.instr_list[j].has_label and
                    self.instr_stream.instr_list[j].is_local_numeric_label):
                idx = int(self.instr_stream.instr_list[j].label)
                if(not branch_target[idx]):
                    self.instr_stream.instr_list[j].has_label = 0
            j += 1
        logging.info("Finished post-processing instructions")

    def insert_jump_instr(self):
        pass  # TODO

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
                    prefix = pkg_ins.format_string(string = '{}:'.format(
                        self.instr_stream.instr_list[i].label), length = pkg_ins.LABEL_STR_LEN)
                else:
                    prefix = pkg_ins.format_string(string = " ", length = pkg_ins.LABEL_STR_LEN)
            string = prefix + self.instr_stream.instr_list[i].convert2asm()
            self.instr_string_list.append(string)
            prefix = pkg_ins.format_string(str(i), pkg_ins.LABEL_STR_LEN)

    # TODO
    def generate_return_routine(self):
        pass

    # TODO
    def insert_illegal_hint_instr(self):
        pass
