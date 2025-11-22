// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface deals with the force paths in CSRNG interrupt and error tests

interface csrng_path_if
(
  input csrng_cmd_i
);

  import uvm_pkg::*;

  string core_path = "tb.dut.u_csrng_core";

  function automatic string fifo_err_path(int app, string fifo_name, string which_path);
    case (fifo_name) inside
      "sfifo_cmd", "sfifo_genbits": return {core_path, $sformatf(".gen_cmd_stage[%0d]", app),
                                            ".u_csrng_cmd_stage.", fifo_name, "_", which_path};
      default: `uvm_fatal("csrng_path_if", $sformatf("%s: Invalid fifo name!", fifo_name))
    endcase // case (fifo_name.substr(6, fifo_name.len()-1))
  endfunction // fifo_err_path

  function automatic string sm_err_path(string which_sm, int app);
    case (which_sm)
      "cmd_stage_sm": return {core_path, $sformatf(".gen_cmd_stage[%0d]", app),
                                  ".u_csrng_cmd_stage.state_q"};
      "main_sm": return {core_path, ".u_csrng_main_sm.state_q"};
      "ctr_drbg_sm": return {core_path, ".u_csrng_ctr_drbg.state_q"};
      default: `uvm_fatal("csrng_path_if", "Invalid sm name!")
    endcase // case (which_sm)
  endfunction // sm_err_path

  function automatic string aes_cipher_fsm_err_path(int which_sp2v, string which_path);
    return {core_path, ".u_csrng_block_encrypt.u_aes_cipher_core.u_aes_cipher_control",
            $sformatf(".gen_fsm[%0d].gen_fsm_%s", which_sp2v, which_path),
            ".u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm",
            ".aes_cipher_ctrl_cs"};
  endfunction // aes_cipher_fsm_err_path

  function automatic string aes_cipher_rnd_ctr_err_path(int which_sp2v, string which_path);
    return {core_path, ".u_csrng_block_encrypt.u_aes_cipher_core.u_aes_cipher_control",
            $sformatf(".gen_fsm[%0d].gen_fsm_%s", which_sp2v, which_path),
            ".u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm",
            ".rnd_ctr_q"};
  endfunction // aes_cipher_rnd_ctr_err_path

  function automatic string aes_cipher_ctrl_err_path(int which_sp2v, string which_path);
    return {core_path, ".u_csrng_block_encrypt.u_aes_cipher_core.u_aes_cipher_control",
            $sformatf(".gen_fsm[%0d].gen_fsm_%s", which_sp2v, which_path),
            ".u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm",
            ".add_rk_sel_o"};
  endfunction // aes_cipher_ctrl_err_path

  function automatic string cmd_gen_cnt_err_path(int app);
    return {core_path, $sformatf(".gen_cmd_stage[%0d]", app),
            ".u_csrng_cmd_stage.u_prim_count_cmd_gen_cntr.cnt_q[1]"};
  endfunction // cmd_gen_cnt_err_path

  function automatic string ctr_drbg_ctr_err_path();
    return {core_path, ".u_csrng_ctr_drbg.u_prim_count_ctr_drbg.cnt_q[1]"};
  endfunction // ctr_drbg_ctr_err_path

  function automatic string csrng_core_path(string path_ext);
    return {core_path, ".", path_ext};
  endfunction // core_path
endinterface // csrng_path_if
