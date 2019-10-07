/*
 * Copyright 2019 Google LLC
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

package riscv_signature_pkg;

  // Will be the lowest 8 bits of the data word
  typedef enum bit[7:0] {
    // Information sent to the core relating its current status.
    // Bits [12:8] of the data word will be the core_status_t value
    // corresponding to the current core status.
    CORE_STATUS,
    // Information sent to the core conveying the uvm simulation result.
    // Bit [8] of the data word will be the test_result_t value.
    TEST_RESULT,
    // Sent to the core to indicate a dump of GPRs to testbench.
    // Will be followed by 32 writes of registers x0-x32.
    WRITE_GPR,
    // Sent to the core to indicate a write of a CSR's data.
    // Bits [19:8] of the data word will be the CSR address.
    // Will be followed by a second write of the actual data from the CSR.
    WRITE_CSR
  } signature_type_t;

  typedef enum bit[4:0] {
    INITIALIZED,
    IN_DEBUG_MODE,
    IN_MACHINE_MODE,
    IN_HYPERVISOR_MODE,
    IN_SUPERVISOR_MODE,
    IN_USER_MODE,
    HANDLING_IRQ,
    FINISHED_IRQ,
    HANDLING_EXCEPTION,
    INSTR_FAULT_EXCEPTION,
    ILLEGAL_INSTR_EXCEPTION,
    LOAD_FAULT_EXCEPTION,
    STORE_FAULT_EXCEPTION,
    EBREAK_EXCEPTION
  } core_status_t;

  typedef enum bit {
    TEST_PASS,
    TEST_FAIL
  } test_result_t;

endpackage
