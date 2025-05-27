// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is bound into the edn_core module and enables/disables assertions embedded in
// its code.

// These hierarchical paths are all up-references and go up one step (to leave the bound-in
// interface), then select a block that is a child of the edn_core module.

`define PATH1 u_prim_count_max_reqs_cntr
`define PATH2 u_edn_main_sm
`define PATH3 gen_ep_blk[0].u_edn_ack_sm_ep

interface edn_assert_if();

  task automatic assert_off ();
    $assertoff(0, `PATH1.CntErrReported_A);
    $assertoff(0, `PATH2.u_state_regs_A);
    $assertoff(0, `PATH3.u_state_regs_A);
  endtask

  task automatic assert_on ();
    $asserton(0, `PATH1.CntErrReported_A);
    $asserton(0, `PATH2.u_state_regs_A);
    $asserton(0, `PATH3.u_state_regs_A);
  endtask

endinterface

`undef PATH3
`undef PATH2
`undef PATH1
