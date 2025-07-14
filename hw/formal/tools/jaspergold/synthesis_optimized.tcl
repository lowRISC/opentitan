# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set all_cids [check_cov -list -cid]
set non_optimized_cids [check_cov -list -exclude synthesis_optimized -cid]

foreach cid $all_cids {
  if {[lsearch -exact $non_optimized_cids $cid] == -1} {
    check_cov -waiver -add -cover_item_id $cid -comment "Optimized in synthesis"
  }
}
