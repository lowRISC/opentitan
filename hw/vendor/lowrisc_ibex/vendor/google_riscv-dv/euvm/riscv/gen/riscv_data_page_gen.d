/*
 * Copyright 2018 Google LLC
 * Copyright 2022 Coverify Systems Technology
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

module riscv.gen.riscv_data_page_gen;

import riscv.gen.riscv_instr_pkg: mem_region_t, data_pattern_t, hart_prefix, format_string,
  format_data, LABEL_STR_LEN;
import riscv.gen.riscv_instr_gen_config: riscv_instr_gen_config;

import std.format: format;

import esdl.data.bvec: ubvec, toubvec;
import esdl.base.rand: urandom;

import uvm;

class riscv_data_page_gen: uvm_object
{
  import std.conv: to;

  riscv_instr_gen_config        cfg;
  string[]                      data_page_str;
  mem_region_t[]                mem_region_setting;

  mixin uvm_object_utils;

  this(string name = "cls_avail_regs") {
    super(name);
  }

  // The data section can be initialized with different data pattern:
  // - Random value, incremental value, all zeros
  void gen_data(in  int idx,
		in  data_pattern_t pattern,
		in  uint  num_of_bytes,
		out ubyte[] data) {
    ubyte temp_data;
    data.length = num_of_bytes;
    foreach (i, ref dd; data) {
      if (pattern == data_pattern_t.RAND_DATA) {
        temp_data = toubvec!8(urandom!ubyte());
	dd = temp_data;
      }
      else if (pattern == data_pattern_t.INCR_VAL) {
        dd = cast(ubyte) ((idx + (cast(int) i)) % 256);
      }
    }
  }

  // Generate data pages for all memory regions
  void gen_data_page(int hart_id,
		     data_pattern_t pattern,
		     bool is_kernel = false,
		     bool amo = false) {
    string tmp_str;
    ubyte[] tmp_data;
    int page_cnt;
    int page_size;
    data_page_str.length = 0;
    if (is_kernel) {
      mem_region_setting = cfg.s_mem_region;
    }
    else if (amo) {
      mem_region_setting = cfg.amo_region;
    }
    else {
      mem_region_setting = cfg.mem_region;
    }
    foreach (setting; mem_region_setting) {
      uvm_info(get_full_name, format("Generate data section: %0s size:0x%0x  xwr:0x%0x]",
				     setting.name, setting.size_in_bytes, setting.xwr), UVM_LOW);
      if (amo) {
        if (cfg.use_push_data_section) {
          data_page_str ~= format(".pushsection .%0s,\"aw\",@progbits;",
				  setting.name);
	}
	else {
          data_page_str ~= format(".section .%0s,\"aw\",@progbits;",
				  setting.name);
        }
        data_page_str ~= format("%0s:", setting.name);
      }
      else {
        if (cfg.use_push_data_section) {
          data_page_str ~= format(".pushsection .%0s,\"aw\",@progbits;",
				  (hart_prefix(hart_id) ~ setting.name));
        }
	else {
          data_page_str ~= format(".section .%0s,\"aw\",@progbits;",
				  (hart_prefix(hart_id) ~ setting.name));
        }
        data_page_str ~= format("%0s:",
				(hart_prefix(hart_id) ~ setting.name));
      }
      page_size = setting.size_in_bytes;
      for (int i = 0; i < page_size; i+= 32) {
        if (page_size-i >= 32) {
          gen_data(i, pattern, 32, tmp_data);
        }
	else {
          gen_data(i, pattern, page_size-i, tmp_data);
        }
        tmp_str = format_string(format(".word %0s", format_data(tmp_data)), LABEL_STR_LEN);
        data_page_str ~= tmp_str;
      }
      if (cfg.use_push_data_section) {
        data_page_str ~= ".popsection;";
      }
    }
  }

}
