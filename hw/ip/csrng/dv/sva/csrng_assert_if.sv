// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that is bound into the csrng module and enables/disables assertions embedded in its
// code.

// These hierarchical paths were meant to all be up-references, going up one step (to leave the
// bound-in interface), then select a block that is a child of the csrng module.
// However, due to the missing support for up-references in $assertoff() (and probably other
// assertion-control functions), they have to be absolute references for now.
`define DUT_PATH tb.dut
`define PATH1 \
    u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage
`define PATH2 \
    u_csrng_core.u_csrng_block_encrypt.u_aes_cipher_core.u_aes_cipher_control
`define PATH2_1 \
    gen_fsm[0].gen_fsm_p.u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm
`define PATH2_2 \
    gen_fsm[1].gen_fsm_p.u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm
`define PATH2_3 \
    gen_fsm[2].gen_fsm_n.u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm
`define PATH3 \
    u_csrng_core.u_csrng_ctr_drbg
`define PATH4 \
    u_csrng_core.u_csrng_main_sm

interface csrng_assert_if
(
  input csrng_cmd_i
);

  task automatic assert_off ();
    $assertoff(0, `DUT_PATH.`PATH1.u_state_regs_A);
    $assertoff(0, `DUT_PATH.`PATH2.`PATH2_1.AesCipherControlStateValid);
    $assertoff(0, `DUT_PATH.`PATH2.`PATH2_2.AesCipherControlStateValid);
    $assertoff(0, `DUT_PATH.`PATH2.`PATH2_3.AesCipherControlStateValid);
    $assertoff(0, `DUT_PATH.`PATH2.`PATH2_1.u_state_regs_A);
    $assertoff(0, `DUT_PATH.`PATH2.`PATH2_2.u_state_regs_A);
    $assertoff(0, `DUT_PATH.`PATH2.`PATH2_3.u_state_regs_A);
    $assertoff(0, `DUT_PATH.`PATH3.u_state_regs_A);
    $assertoff(0, `DUT_PATH.`PATH4.u_state_regs_A);
  endtask // assert_off

  task automatic assert_on ();
    $asserton(0, `DUT_PATH.`PATH1.u_state_regs_A);
    $asserton(0, `DUT_PATH.`PATH2.`PATH2_1.AesCipherControlStateValid);
    $asserton(0, `DUT_PATH.`PATH2.`PATH2_2.AesCipherControlStateValid);
    $asserton(0, `DUT_PATH.`PATH2.`PATH2_3.AesCipherControlStateValid);
    $asserton(0, `DUT_PATH.`PATH2.`PATH2_1.u_state_regs_A);
    $asserton(0, `DUT_PATH.`PATH2.`PATH2_2.u_state_regs_A);
    $asserton(0, `DUT_PATH.`PATH2.`PATH2_3.u_state_regs_A);
    $asserton(0, `DUT_PATH.`PATH3.u_state_regs_A);
    $asserton(0, `DUT_PATH.`PATH4.u_state_regs_A);
  endtask // assert_on

  task automatic assert_off_alert ();

  endtask // assert_off_alert

  task automatic assert_on_alert ();
  endtask // assert_on_alert
endinterface

`undef PATH4
`undef PATH3
`undef PATH2_3
`undef PATH2_2
`undef PATH2_1
`undef PATH2
`undef PATH1
