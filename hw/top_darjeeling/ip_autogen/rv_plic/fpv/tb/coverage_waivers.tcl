# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The statement is a deadcode as le_i is always level triggered.
check_cov -waiver -add -start_line 34 -end_line 34 -type {branch} -instance {dut.u_gateway} -comment {le_i is tied to a parameter which is 0}

# All the interrupts are level triggered thus le_i is always 0. The reason to add this assertion is
# to support the waiver for the statement above. The statement is a ternary assignment and the
# conditional part of it is le_i which is always false.
assert -name InterruptsAreLevelTriggered {!$rose(dut.u_gateway.le_i)}
