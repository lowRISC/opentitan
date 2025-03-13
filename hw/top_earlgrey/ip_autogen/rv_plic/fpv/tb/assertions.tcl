# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# To support that the precondition related to assertion Onehot0Check_A can never happen i.e.
# !$onehot0(oh_i), an assertion to make sure that oh_i is always onehot or zero.
assert -name InpAlwaysOnehot0_A {$onehot0(dut.u_reg.u_prim_reg_we_check.u_prim_onehot_check.oh_i)}

# To support the precondition related to the assertion EnableCheck_A i.e. !en_i && |oh_i can never
# become true as both of the signals has a dependency on the same wire. If that wire is false then
# they both can't happen. The below assertions makes sure that whenever oh_i is onehot then there
# must be en_i.
assert -name InpOnehotImpliesEn_A \
  {{$onehot(dut.u_reg.u_prim_reg_we_check.u_prim_onehot_check.oh_i)} -> \
  {dut.u_reg.u_prim_reg_we_check.u_prim_onehot_check.en_i}}
