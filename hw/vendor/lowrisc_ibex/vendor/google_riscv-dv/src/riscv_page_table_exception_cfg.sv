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

class riscv_page_table_exception_cfg extends uvm_object;

  bit enable_exception;

  // Knobs for each type of exception
  rand bit allow_page_access_control_exception;
  rand bit allow_superpage_misaligned_exception;
  rand bit allow_leaf_link_page_exception;
  rand bit allow_invalid_page_exception;
  rand bit allow_privileged_mode_exception;
  rand bit allow_zero_access_bit_exception;
  rand bit allow_zero_dirty_bit_exception;

  // Exception ratio control
  int unsigned page_access_fault_ratio     = 10;
  int unsigned misaligned_superpage_ratio  = 10;
  int unsigned leaf_link_page_ratio        = 10;
  int unsigned invalid_page_ratio          = 10;
  int unsigned privl_mode_fault_ratio      = 10;
  int unsigned zero_access_fault_ratio     = 5;
  int unsigned zero_dirty_fault_ratio      = 5;

  constraint exception_ratio_c {
    if(enable_exception) {
      allow_page_access_control_exception  dist { 1 := page_access_fault_ratio,
                                                  0 := 100 - page_access_fault_ratio };
      allow_superpage_misaligned_exception dist { 1 := misaligned_superpage_ratio,
                                                  0 := 100 - misaligned_superpage_ratio };
      allow_leaf_link_page_exception       dist { 1 := leaf_link_page_ratio,
                                                  0 := 100 - leaf_link_page_ratio };
      allow_invalid_page_exception         dist { 1 := invalid_page_ratio,
                                                  0 := 100 - invalid_page_ratio };
      allow_privileged_mode_exception      dist { 1 := privl_mode_fault_ratio,
                                                  0 := 100 - privl_mode_fault_ratio };
      allow_zero_access_bit_exception      dist { 1 := zero_access_fault_ratio,
                                                  0 := 100 - zero_access_fault_ratio };
      allow_zero_dirty_bit_exception       dist { 1 := zero_dirty_fault_ratio,
                                                  0 := 100 - zero_dirty_fault_ratio };
    } else {
      allow_page_access_control_exception  == 0;
      allow_superpage_misaligned_exception == 0;
      allow_leaf_link_page_exception       == 0;
      allow_invalid_page_exception         == 0;
      allow_privileged_mode_exception      == 0;
      allow_zero_access_bit_exception      == 0;
      allow_zero_dirty_bit_exception       == 0;
    }
  }

  `uvm_object_utils(riscv_page_table_exception_cfg)
  `uvm_object_new

endclass
