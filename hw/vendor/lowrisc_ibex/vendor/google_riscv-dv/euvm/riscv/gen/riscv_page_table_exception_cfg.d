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
module riscv.gen.riscv_page_table_exception_cfg;

import esdl.rand: constraint, rand;
import uvm;


class riscv_page_table_exception_cfg : uvm_object
{
  mixin uvm_object_utils ;

  this(string name = "") {
    super(name);
  }

  bool enable_exception;

  // Knobs for each type of exception
  @rand bool allow_page_access_control_exception;
  @rand bool allow_superpage_misaligned_exception;
  @rand bool allow_leaf_link_page_exception;
  @rand bool allow_invalid_page_exception;
  @rand bool allow_privileged_mode_exception;
  @rand bool allow_zero_access_bit_exception;
  @rand bool allow_zero_dirty_bit_exception;

  // Exception ratio control
  uint page_access_fault_ratio     = 10;
  uint misaligned_superpage_ratio  = 10;
  uint leaf_link_page_ratio        = 10;
  uint invalid_page_ratio          = 10;
  uint privl_mode_fault_ratio      = 10;
  uint zero_access_fault_ratio     = 5;
  uint zero_dirty_fault_ratio      = 5;

  constraint! q{
    if (enable_exception == true) {
      allow_page_access_control_exception dist
	[ true := page_access_fault_ratio,
	  false := 100 - page_access_fault_ratio ];
      allow_superpage_misaligned_exception dist
	[ true := misaligned_superpage_ratio,
	  false := 100 - misaligned_superpage_ratio ];
      allow_leaf_link_page_exception dist
	[ true := leaf_link_page_ratio,
	  false := 100 - leaf_link_page_ratio ];
      allow_invalid_page_exception dist
	[ true := invalid_page_ratio,
	  false := 100 - invalid_page_ratio ];
      allow_privileged_mode_exception dist
	[ true := privl_mode_fault_ratio,
	  false := 100 - privl_mode_fault_ratio ];
      allow_zero_access_bit_exception  dist
	[ true := zero_access_fault_ratio,
	  false := 100 - zero_access_fault_ratio ];
      allow_zero_dirty_bit_exception dist
	[ true := zero_dirty_fault_ratio,
	  false := 100 - zero_dirty_fault_ratio ];
    }
    else {
      allow_page_access_control_exception  == false;
      allow_superpage_misaligned_exception == false;
      allow_leaf_link_page_exception       == false;
      allow_invalid_page_exception         == false;
      allow_privileged_mode_exception      == false;
      allow_zero_access_bit_exception      == false;
      allow_zero_dirty_bit_exception       == false;
    }
  } exception_ratio_c;

}
