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
  mem_region_t            mem_region_setting[$];

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

  // Generate data pages for all memory regions
  function void gen_data_page(int hart_id,
                              data_pattern_t pattern,
                              bit is_kernel = 1'b0,
                              bit amo = 0);
    string tmp_str;
    bit [7:0] tmp_data[];
    int page_cnt;
    int page_size;
    data_page_str = {};
    if (is_kernel) begin
      mem_region_setting = cfg.s_mem_region;
    end else if (amo) begin
      mem_region_setting = cfg.amo_region;
    end else begin
      mem_region_setting = cfg.mem_region;
    end
    foreach (mem_region_setting[i]) begin
      `uvm_info(`gfn, $sformatf("Generate data section: %0s size:0x%0x  xwr:0x%0x]",
                                mem_region_setting[i].name,
                                mem_region_setting[i].size_in_bytes,
                                mem_region_setting[i].xwr), UVM_LOW)
      if (amo) begin
        if (cfg.use_push_data_section) begin
          data_page_str.push_back($sformatf(".pushsection .%0s,\"aw\",@progbits;",
                                            mem_region_setting[i].name));
        end else begin
          data_page_str.push_back($sformatf(".section .%0s,\"aw\",@progbits;",
                                            mem_region_setting[i].name));
        end
        data_page_str.push_back($sformatf("%0s:", mem_region_setting[i].name));
      end else begin
        if (cfg.use_push_data_section) begin
          data_page_str.push_back($sformatf(".pushsection .%0s,\"aw\",@progbits;",
                                            {hart_prefix(hart_id), mem_region_setting[i].name}));
        end else begin
          data_page_str.push_back($sformatf(".section .%0s,\"aw\",@progbits;",
                                            {hart_prefix(hart_id), mem_region_setting[i].name}));
        end
        data_page_str.push_back($sformatf("%0s:",
                                          {hart_prefix(hart_id), mem_region_setting[i].name}));
      end
      page_size = mem_region_setting[i].size_in_bytes;
      for(int i = 0; i < page_size; i+= 32) begin
        if (page_size-i >= 32) begin
          gen_data(.idx(i), .pattern(pattern), .num_of_bytes(32), .data(tmp_data));
        end else begin
          gen_data(.idx(i), .pattern(pattern), .num_of_bytes(page_size-i), .data(tmp_data));
        end
        tmp_str = format_string($sformatf(".word %0s", format_data(tmp_data)), LABEL_STR_LEN);
        data_page_str.push_back(tmp_str);
      end
      if (cfg.use_push_data_section) begin
        data_page_str.push_back(".popsection;");
      end
    end
  endfunction

endclass
