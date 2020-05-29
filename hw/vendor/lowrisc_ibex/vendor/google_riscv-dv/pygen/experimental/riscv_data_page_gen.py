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

import utils
import random
from bitstring import BitArray, BitStream


# -----------------------------------------------------------------------------------------
#  RISC-V assmebly program data section generator
#  There can be user mode and supervisor(kernel) mode data pages
# -----------------------------------------------------------------------------------------
class riscv_data_page_gen:

  def __init__(self):
    self.data_page_str = []
    # TO DO: cfg
    # cfg...

  # The data section can be initialized with different data pattern:
  # Random value, incremental value, all zeros
  def gen_data(self, idx, pattern, num_of_bytes):
    data = [None] * num_of_bytes
    for i in range(len(data)):
      if pattern == "RAND_DATA":
        temp_data = random.randint(0, 255)
        # data[i] = temp_data
        data[i] = BitArray(uint=temp_data, length=8)
      elif pattern == "INCR_VAL":
        # data[i] = (idx+i) % 256
        data[i] = BitArray(uint=(idx + i) % 256, length=8)
    return data

  # Generate the assembly code for the data section
  def gen_data_page(self, pattern, is_kernel=0):
    self.data_page_str.clear()
    # TO DO: need to embed num_of_kernel_data_pages, num_of_data_pages, etc. in the riscv_core_setting
    page_cnt = 1 if is_kernel else 2
    page_size = 4096
    for section_idx in range(page_cnt):
      if is_kernel:
        self.data_page_str.append("kernel_data_page_{}:".format(section_idx))
      else:
        self.data_page_str.append("data_page_{}:".format(section_idx))
      # TO DO: need to embed data_page_alignment in the core_setting
      self.data_page_str.append(".align 12")
      for i in range(0, page_size, 32):
        tmp_data = self.gen_data(i, pattern, 32)
        tmp_str = ".word {:{}}".format(
            utils.format_data(tmp_data), utils.length)
        self.data_page_str.append(tmp_str)
