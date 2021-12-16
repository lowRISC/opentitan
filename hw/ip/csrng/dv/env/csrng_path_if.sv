// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This interface deals with the force paths in CSRNG interrupt and error tests

interface csrng_path_if
(
  input csrng_cmd_i
);

  import uvm_pkg::*;

  string core_path = "tb.dut.u_csrng_core";

  function automatic string cs_hw_inst_exc_path(string which_path, int which_hw_inst_exc);
    return {core_path, $sformatf(".cmd_stage_%s[%0d]", which_path, which_hw_inst_exc)};
  endfunction // cs_hw_inst_exc_path

  function automatic string fifo_err_path(int NHwApps, string fifo_name, string which_path);
    case (fifo_name) inside
      "sfifo_cmd", "sfifo_genbits": return {core_path, $sformatf(".gen_cmd_stage[%0d]", NHwApps),
                                            ".u_csrng_cmd_stage.", fifo_name, "_", which_path};
      "sfifo_cmdreq", "sfifo_rcstage", "sfifo_keyvrc": return {core_path, ".u_csrng_ctr_drbg_cmd.",
                                                               fifo_name, "_", which_path};
      "sfifo_updreq", "sfifo_bencreq", "sfifo_bencack", "sfifo_pdata", "sfifo_final": return
        {core_path, ".u_csrng_ctr_drbg_upd.", fifo_name, "_", which_path};
      "sfifo_gbencack", "sfifo_grcstage", "sfifo_ggenreq", "sfifo_gadstage", "sfifo_ggenbits":
        return {core_path,".u_csrng_ctr_drbg_gen.sfifo_", fifo_name.substr(7, fifo_name.len()-1),
                "_", which_path};
      "sfifo_blkenc": return {core_path, ".u_csrng_block_encrypt.", fifo_name, "_", which_path};
      default: `uvm_fatal("csrng_path_if", "Invalid fifo name!")
    endcase // case (fifo_name.substr(6, fifo_name.len()-1))
  endfunction // fifo_err_path

  function automatic string sm_err_path(string which_sm, int NHwApps);
    case (which_sm)
      "cmd_stage_sm": return {core_path, $sformatf(".gen_cmd_stage[%0d]", NHwApps),
                                  ".u_csrng_cmd_stage.state_q"};
      "main_sm": return {core_path, ".u_csrng_main_sm.state_q"};
      "drbg_gen_sm": return {core_path, ".u_csrng_ctr_drbg_gen.state_q"};
      "drbg_updbe_sm": return {core_path, ".u_csrng_ctr_drbg_upd.blk_enc_state_q"};
      "drbg_updob_sm": return {core_path, ".u_csrng_ctr_drbg_upd.outblk_state_q"};
      default: `uvm_fatal("csrng_path_if", "Invalid sm name!")
    endcase // case (which_sm)
  endfunction // sm_err_path

  function automatic string aes_cipher_sm_err_path(int which_sp2v, string which_path);
    return {core_path, ".u_csrng_block_encrypt.u_aes_cipher_core.u_aes_cipher_control",
            $sformatf(".gen_fsm[%0d].gen_fsm_%s", which_sp2v, which_path),
            ".u_aes_cipher_control_fsm_i.u_aes_cipher_control_fsm",
            ".aes_cipher_ctrl_cs"};
  endfunction // aes_cipher_sm_err_path

  function automatic string cmd_gen_cnt_err_path(int NHwApps);
    return {core_path, $sformatf(".gen_cmd_stage[%0d]", NHwApps),
            ".u_csrng_cmd_stage.u_prim_count_cmd_gen_cntr.gen_cross_cnt_hardening.msb"};
  endfunction // cmd_gen_cnt_err_path
endinterface // csrng_path_if
