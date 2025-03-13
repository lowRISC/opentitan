# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This assertion states that if the input enable (en_i) is not high and onehot input (oh_i) is
# non-zero then we get an output error (err_o). The precondition for EnableCheck_A is false i.e.
# !en_i && |oh_i cannot become true.
# oh_i is connected to reg_we_check under the instantiation of u_prim_reg_we_check inside u_reg
# module. Each bit of reg_we_check is assigned through range of different software controlled
# registers except 6 bits ranging from reg_we_check[186:191] are wired to 0. Those software
# controlled registers are driven by a addr_hit[x] bit and if that bit is true then reg_addr coming
# from u_reg_if is the address of that register. Then they also required reg_we=1 and !reg_error.
# So, if we get a respective addr_hit[x], reg_we and !reg_error then we get reg_we_check as true,
# which means |oh_i is true.
# en_i is wired to reg_we && !addr_miss expression under the instantiation of u_prim_reg_we_check.
# If en_i is false, it means that either reg_we is false or addr_miss is true or both. In anycase,
# we can't get oh_i through the explanation argued above. !addr_miss means that either we don't
# have a reg_we or the address in reg_addr is not equal to any of the registers (equivalent to
# !addr_hit).
cover -disable -regexp ".*\.u_prim_reg_we_check.u_prim_onehot_check\..*\.EnableCheck_A:precondition1"

# To support the precondition related to the assertion EnableCheck_A i.e. !en_i && |oh_i can never
# become true as both of the signals has a dependency on the same wire. If that wire is false then
# they both can't happen. The below assertions makes sure that whenever oh_i is onehot then there
# must be en_i.
assert -name InpOnehotImpliesEn_A \
  {{$onehot(dut.u_reg.u_prim_reg_we_check.u_prim_onehot_check.oh_i)} -> \
  {dut.u_reg.u_prim_reg_we_check.u_prim_onehot_check.en_i}}

# This assertion means that if onehot input(oh_i) is not onehot or zero then err_o in
# u_prim_onehot_check should get asserted. The precondition for Onehot0Check_A is !$onehot0(oh_i).
# But oh_i is always one-hot or zero for the same reason argued above. Due to the fact that oh_i is
# wired to reg_we_check in u_reg and each bit of reg_we_check is driven by a range of software
# controlled registers. Those registers are a single bit value and which is true if their
# respective addr_hit[x] is true along with reg_we and !reg_error. But addr_hit is also a onehot0
# vector as each bit of addr_hit represents a specific address hit of a register. The address is
# coming from reg_addr as an output from u_reg_if and that can only have an address of a single
# software controlled register. That address is checked against the address of every register and
# whichever matches, the corresponding addr_hit bit gets updated to 1.
# To conclude this, oh_i means that we have a mapped register address with a reg write enable
# without a register error. Since a register could be a mapped one or not, the precondition can
# never happen.
cover -disable -regexp ".*\.u_prim_reg_we_check.u_prim_onehot_check.Onehot0Check_A:precondition1"

# To support that the precondition related to assertion Onehot0Check_A can never happen i.e.
# !$onehot0(oh_i), an assertion to make sure that oh_i is always onehot or zero.
assert -name InpAlwaysOnehot0_A {$onehot0(dut.u_reg.u_prim_reg_we_check.u_prim_onehot_check.oh_i)}

# Jasper analyzed this precondition as unreachable. It requires err_o in u_prim_onehot_check
# instantiated under u_reg.u_prim_reg_we_check as true to enable the assertion. First, err_o is
# driven in u_prim_onehot_check. If either of enable_err, addr_err or oh0_err is true then err_o is
# true. addr_err is always false as the parameter AddrCheck is tied to zero. Then, oh0 depends upon
# err_tree[0] which is assigned through a binary tree structure. Any node in an err_tree at any
# level is true if either of the two children associated to that node or both of the children of an
# or_tree node is true. When the tree reached at the bottom, then or_tree left nodes equivalent to
# OneHotWidth (leftmost node) assigned through oh_i and rest (rightmost nodes) are tied to 0. By
# the same reason argued above, we know that oh_i is always onehot or zero so we can't get multiple
# ones in an or_tree and therefore in an err_tree. So, oh_0 is always false.
# Lastly, enable_err needs root node of the or_tree as true and en_i (assigned in u_reg) as false.
# Again the agument above for the precondiiton of EnableCheck states that we can't get oh_i without
# en_i and if we don't have oh_i then we can't get any node in an or_tree as true.
cover -disable <embedded>::rv_plic_tb.dut.FpvSecCmRegWeOnehotCheck_A:precondition1

# The intention to add this assertion is to make sure that err_o never happens as we waived off the
# precondition above.
assert -name RvPlicRegNoOneHot&EnError \
  {dut.u_reg.u_prim_reg_we_check.u_prim_onehot_check.err_o == 0}
