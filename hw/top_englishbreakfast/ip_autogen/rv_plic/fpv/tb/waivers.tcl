# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

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
