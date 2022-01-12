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

from enum import IntEnum, auto


# Will be the lowest 8 bits of the data word
class signature_type_t(IntEnum):
    '''
    Information sent to the core relating its current status.
    Bits [12:8] of the data word will be the core_status_t value
    corresponding to the current core status.
    '''
    CORE_STATUS = 0
    '''
    Information sent to the core conveying the uvm simulation result.
    Bit [8] of the data word will be the test_result_t value.
    '''
    TEST_RESULT = auto()
    '''
    Sent to the core to indicate a dump of GPRs to testbench.
    Will be followed by 32 writes of registers x0-x32.
    '''
    WRITE_GPR = auto()
    '''
    Sent to the core to indicate a write of a CSR's data.
    Bits [19:8] of the data word will be the CSR address.
    Will be followed by a second write of the actual data from the CSR.
    '''
    WRITE_CSR = auto()


class core_status_t(IntEnum):
    INITIALIZED = 0
    IN_DEBUG_MODE = auto()
    IN_MACHINE_MODE = auto()
    IN_HYPERVISOR_MODE = auto()
    IN_SUPERVISOR_MODE = auto()
    IN_USER_MODE = auto()
    HANDLING_IRQ = auto()
    FINISHED_IRQ = auto()
    HANDLING_EXCEPTION = auto()
    INSTR_FAULT_EXCEPTION = auto()
    ILLEGAL_INSTR_EXCEPTION = auto()
    LOAD_FAULT_EXCEPTION = auto()
    STORE_FAULT_EXCEPTION = auto()
    EBREAK_EXCEPTION = auto()


class test_result_t(IntEnum):
    TEST_PASS = 0
    TEST_FAIL = auto()
