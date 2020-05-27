"""Copyright 2020 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
"""

import subprocess
import random
from bitstring import BitArray, BitStream
import utils
import riscv_instr_sequence
import riscv_instr_stream
import riscv_load_store_instr_lib
import riscv_data_page_gen
import riscv_callstack_gen


# RISC-V assembly program generator: main class to generate a RISC-V program
class riscv_asm_program_gen:

  def __init__(self):
    self.instr_stream = []
    self.main_program = riscv_instr_sequence.riscv_instr_sequence(
        "main_program")
    self.sub_program = []  # elements are from type riscv_instr_sequence
    self.data_page_gen = riscv_data_page_gen.riscv_data_page_gen()
    # Directed instruction ratio, occurrence per 1000 instructions
    self.directed_instr_stream_ratio = dict()

  def gen_program(self, cnt):
    sub_program_name = []  # elements are strings
    self.instr_stream.clear()
    self.gen_program_header()
    self.init_gpr()
    # Init section
    self.gen_init_section()
    # Generate sub program
    # TO DO: cfg
    # if cfg.num_of_sub_program
    num_of_sub_program = 1
    if num_of_sub_program > 0:
      self.sub_program = [None] * num_of_sub_program
      idx = 0
      for i in range(len(self.sub_program)):
        self.sub_program[i] = riscv_instr_sequence.riscv_instr_sequence(
            "sub_{}".format(idx + 1))
        idx += 1
        # TO DO: cfg
        # sub_program.instr_cnt = cfg.sub_program_instr_cnt[i]
        self.sub_program[i].instr_cnt = random.randint(1, 100)
        self.generate_directed_instr_stream(
            self.sub_program[i].directed_instr,
            self.sub_program[i].name,
            self.sub_program[i].instr_cnt,
            min_insert_cnt=0)
        self.sub_program[i].label_name = self.sub_program[i].name
        # TO DO: cfg
        # sub_program.cfg = cfg
        self.sub_program[i].gen_instr(0)
        sub_program_name.append(self.sub_program[i].label_name)
    # Generate main program
    self.main_program.instr_cnt = cnt
    self.main_program.label_name = "_main"
    # Generate directed instruction stream
    self.generate_directed_instr_stream(
        self.main_program.directed_instr,
        "main",
        self.main_program.instr_cnt,
        min_insert_cnt=1)
    self.main_program.gen_instr(1)
    # Setup jump instruction among main program and sub programs
    if num_of_sub_program > 0:
      callstack_gen = riscv_callstack_gen.riscv_callstack_gen("callstack_gen")
      callstack_gen.init(num_of_sub_program + 1)
      # before randomization, we need to call problem_definition to apply the constraints
      callstack_gen.problem_definition()
      if callstack_gen.randomize():
        idx = 0
        # Insert the jump instruction based on the call stack
        for i in range(len(callstack_gen.program_h)):
          for j in range(len(callstack_gen.program_h[i].sub_program_id)):
            idx += 1
            pid = callstack_gen.program_h[i].sub_program_id[j] - 1
            if i == 0:
              self.main_program.insert_jump_instr(sub_program_name[pid], idx)
            else:
              self.sub_program[i - 1].insert_jump_instr(sub_program_name[pid],
                                                        idx)

    # Needed for branch instructions:
    self.main_program.post_process_instr()
    self.main_program.generate_instr_stream()
    self.instr_stream.append(self.main_program.instr_string_list)
    # Test done section
    self.gen_test_done()
    # Shuffle the sub programs and insert to the instruction stream
    random.shuffle(self.sub_program)
    for item in self.sub_program:
      item.post_process_instr()
      item.generate_instr_stream()
      self.instr_stream.append(item.instr_string_list)
    self.gen_program_end()
    self.gen_data_page_begin()
    # TO DO: cfg
    # if not cfg.no_data_page
    # Data section
    self.gen_data_page()
    self.gen_kernel_sections()

    # TODO: added temporarily here, just to print the self.instr_stream to
    # see what we have so far
    self.print_instr_stream()

  def gen_program_header(self):
    self.instr_stream.append(".macro init")
    self.instr_stream.append(".endm")
    self.instr_stream.append(".section .text.init")
    self.instr_stream.append(".globl _start")
    self.instr_stream.append("_start:")

  def init_gpr(self):
    for i in range(0, 32):
      rnd_val = random.randrange(1, 6)
      if rnd_val == 1:
        reg_val = BitArray(hex="0x0")
      elif rnd_val == 2:
        reg_val = BitArray(hex="0x80000000")
      elif rnd_val == 3:
        temp = random.randrange(0x1, 0xf)
        reg_val = BitArray(hex(temp))
      elif rnd_val == 4:
        temp = random.randrange(0x10, 0xefffffff)
        # reg_val = BitArray(uint=temp, length=32)
        reg_val = BitArray(hex(temp))
      elif rnd_val == 5:
        temp = random.randrange(0xf0000000, 0xffffffff)
        reg_val = BitArray(hex(temp))
      str = "{}li x{}, 0x{}".format(utils.indent, i, reg_val.hex)
      self.instr_stream.append(str)

  def gen_init_section(self):
    pass

  def gen_test_done(self):
    str = "test_done:"
    self.instr_stream.append(str)
    self.instr_stream.append("{}li gp, 1".format(utils.indent))
    # TODO: commented out for now as ecall puts the simulation into an infinite loop as of now (sinc we still don't support it)
    # self.instr_stream.append("{}ecall".format(utils.indent))

  def gen_program_end(self):
    # TODO: this instruction puts Spike in an infinite loop. For now, I just
    # replace it with "writing 1 into tohost" to tell Spike to exit.
    self.gen_section("write_tohost", ["sw gp, tohost, t5"])
    # self.gen_section("write_tohost", ["li t0, 1", "la t1, tohost", "sw t0, 0(t1)"])
    self.gen_section("_exit", ["j write_tohost"])

  def gen_data_page_begin(self):
    self.instr_stream.append(".data")
    self.instr_stream.append('.pushsection .tohost,"aw",@progbits;')
    self.instr_stream.append(".align 6; .global tohost; tohost: .dword 0;")
    self.instr_stream.append(".align 6; .global fromhost; fromhost: .dword 0;")
    self.instr_stream.append(".popsection;")
    self.instr_stream.append(".align 4;")

  def gen_section(self, label, instr_list):
    if label != "":
      str = "{}:{}".format(label, utils.indent)
      self.instr_stream.append(str)
    for instr in instr_list:
      str = "{}{}".format(utils.indent, instr)
      self.instr_stream.append(str)
    self.instr_stream.append("")

  def gen_data_page(self, is_kernel=0):
    # TO DO: cfg
    # self.data_page_gen.cfg = cfg
    # self.data_page_gen.gen_data_page(cfg.data_page_pattern, is_kernel)
    self.data_page_gen.gen_data_page(
        random.choice(utils.data_pattern_t), is_kernel)
    self.instr_stream.append(self.data_page_gen.data_page_str)

  def gen_kernel_sections(self):
    self.gen_all_trap_handler()

  def gen_all_trap_handler(self):
    pass
    # TODO: commenting out for now
    # self.gen_ecall_handler()

  # ECALL trap handler
  # It does some clean up like dump GPRs before communicating with host to terminate the test.
  # User can extend this function if some custom clean up routine is needed.
  def gen_ecall_handler(self):
    str = "ecall_handler:{}".format(utils.indent)
    self.instr_stream.append(str)
    # TODO: TO DO need to add these two functions later when we support sw/sd
    # dump_perf_stats();
    # gen_register_dump();
    str = "{}j write_tohost".format(utils.indent)
    self.instr_stream.append(str)

  def print_instr_stream(self):
    subprocess.run(["mkdir", "-p", "out"])
    f = open("./out/test.S", "w+")
    for s in self.instr_stream:
      if isinstance(s, list):
        for ss in s:
          f.write("{}\n".format(ss))
      else:
        f.write("{}\n".format(s))
    f.close()

  # ---------------------------------------------------------------------------------------
  #  Inject directed instruction stream
  # ---------------------------------------------------------------------------------------
  def add_directed_instr_stream(self, name, ratio):
    self.directed_instr_stream_ratio[name] = ratio

  # Generate directed instruction stream based on the ratio setting
  # I had to move instr_stream to the beginning of arguments as non-default args can't follow default args in python
  def generate_directed_instr_stream(self,
                                     instr_stream,
                                     label,
                                     original_instr_cnt,
                                     min_insert_cnt=0,
                                     access_u_mode_mem=1):
    new_instr_stream = riscv_instr_stream.riscv_rand_instr_stream()
    instr_insert_cnt, idx = 0, 0
    # TO DO: cfg
    # if cfg.no_directed_instr:
    #     return
    for item in self.directed_instr_stream_ratio:
      instr_insert_cnt = int(original_instr_cnt *
                             self.directed_instr_stream_ratio[item] / 1000)
      if instr_insert_cnt <= min_insert_cnt:
        instr_insert_cnt = min_insert_cnt
      for i in range(instr_insert_cnt):
        name = "{}_{}".format(item, i)
        # name will be used in the info_printing
        if item == "riscv_load_store_rand_instr_stream":
          ls_rand_instr_stream_object = riscv_load_store_instr_lib.riscv_load_store_rand_instr_stream(
              name)
          new_instr_stream = ls_rand_instr_stream_object
          # TO DO: cfg
          # new_instr_stream.cfg = cfg
          new_instr_stream.label = "{}_instr_{}".format(label, idx)
          new_instr_stream.access_u_mode_mem = access_u_mode_mem
          # First applying the constraints, then randomizing new_instr_stream
          new_instr_stream.problem_definition()
          new_instr_stream.randomize()

          instr_stream.append(new_instr_stream)
        else:
          pass
        idx += 1
    random.shuffle(instr_stream)


instance = riscv_asm_program_gen()
instance.add_directed_instr_stream("riscv_load_store_rand_instr_stream", 10)
instance.gen_program(100)
print("Test generated: ./out/test.S")
