/*
 * Copyright 2018 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------------------
// RISC-V assmebly program data section generator
// There can be user mode and supervisor(kernel) mode data pages
//-----------------------------------------------------------------------------------------

class riscv_data_page_gen extends uvm_object;

  riscv_instr_gen_config  cfg;
  string                  data_page_str[$];

  `uvm_object_utils(riscv_data_page_gen)

  function new (string name = "");
    super.new(name);
  endfunction

  // The data section can be initialized with different data pattern:
  // - Random value, incremental value, all zeros
  virtual function void gen_data(input  int idx,
                                 input  data_pattern_t pattern,
                                 input  int unsigned num_of_bytes,
                                 output bit [7:0] data[]);
    bit [7:0] temp_data;
    data = new[num_of_bytes];
    foreach(data[i]) begin
      if(pattern == RAND_DATA) begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(temp_data)
        data[i] = temp_data;
      end else if (pattern == INCR_VAL) begin
        data[i] = (idx + i) % 256;
      end
    end
  endfunction

  // Generate the assembly code for the data section
  function void gen_data_page(data_pattern_t pattern, bit is_kernel = 1'b0);
    string tmp_str;
    bit [7:0] tmp_data[];
    int page_cnt;
    int page_size;
    data_page_str = {};
    page_cnt = is_kernel ? riscv_instr_pkg::num_of_kernel_data_pages :
                           riscv_instr_pkg::num_of_data_pages;
    page_size = is_kernel ? riscv_instr_pkg::kernel_data_page_size :
                            riscv_instr_pkg::data_page_size;
    for(int section_idx = 0; section_idx < page_cnt; section_idx++) begin
      if(is_kernel) begin
        data_page_str.push_back($sformatf("kernel_data_page_%0d:", section_idx));
      end else begin
        data_page_str.push_back($sformatf("data_page_%0d:", section_idx));
      end
      data_page_str.push_back($sformatf(".align %0d", riscv_instr_pkg::data_page_alignment));
      for(int i = 0; i < page_size; i+= 32) begin
        gen_data(.idx(i), .pattern(pattern), .num_of_bytes(32), .data(tmp_data));
        tmp_str = format_string($sformatf(".word %0s", format_data(tmp_data)), LABEL_STR_LEN);
        data_page_str.push_back(tmp_str);
      end
    end
  endfunction

endclass
