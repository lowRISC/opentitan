// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Coverage exclusion file for uart
CHECKSUM: "1115183444 4229339"
INSTANCE: tb.dut.uart_core
// this is unreachable condition
Condition 16 "7100374" "(break_err && (break_st == BRK_CHK)) 1 -1" (2 "10")
CHECKSUM: "1115183444 3548154843"
INSTANCE: tb.dut.uart_core
// these are scanmode ralated branches
Branch 1 "2534752149" "scanmode_i" (0) "scanmode_i 1"
Branch 5 "2534752149" "scanmode_i" (0) "scanmode_i 1"
Branch 1 "2534752149" "scanmode_i" (1) "scanmode_i 0"
Branch 5 "2534752149" "scanmode_i" (1) "scanmode_i 0"
// default branch, it's unreachable
Branch 9 "221332935" "(!rst_ni)" (5) "(!rst_ni) 0,default,-,-"
