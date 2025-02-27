# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The statement is a deadcode as le_i is always level triggered.
check_cov -waiver -add -start_line 34 -end_line 34 -type {branch} -instance {dut.u_gateway} -comment {le_i is tied to a parameter which is 0}
