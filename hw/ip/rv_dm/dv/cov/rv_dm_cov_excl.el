// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// In dm_mem.sv, a location that can be read is at WhereToAddr. This is supposed to contain a JAL
// instruction that points at the first instruction of the current abstract command. This location
// is either the start of the program buffer or the start of the abstract command. Deciding which is
// done with the current command's cmdtype. But it turns out that this is always dm::AccessRegister,
// because this is the only supported command. Waive coverage of a situation where the command is
// not that value.
INSTANCE: tb.dut.u_dm_top.i_dm_mem
ANNOTATION: "Cannot have running command other than AccessRegister"
Condition 5 "3588663374" "((cmd_i.cmdtype == AccessRegister) && ((!ac_ar.transfer)) && ac_ar.postexec) 1 -1" (1 "011")
Condition 6 "3885215629" "(cmd_i.cmdtype == AccessRegister) 1 -1" (1 "0")
