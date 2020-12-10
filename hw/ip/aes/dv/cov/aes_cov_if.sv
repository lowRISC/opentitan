// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for AES

interface aes_cov_if
  (
   input logic clk_i // not sure I will use this yet
   );

  import uvm_pkg::*;
  import aes_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"

  bit          en_full_cov = 1'b1;
  bit          en_intg_cov = 1'b1;

  ///////////////////////////////////
  // Control register cover points //
  ///////////////////////////////////

  covergroup aes_ctrl_cg  with function sample(bit                                 aes_op,
                                               bit [aes_pkg::AES_MODE_WIDTH-1:0]   aes_mode,
                                               bit [aes_pkg::AES_KEYLEN_WIDTH-1:0] aes_keylen,
                                               bit                                 aes_man_op,
                                               bit                                 aes_force_0mask
                                               );
    option.per_instance = 1;
    option.name         = "aes_ctrl_cg";

    cp_operation: coverpoint aes_op
      {
       bins enc         = {AES_ENC};
       bins dec         = {AES_DEC};
       }

     cp_mode: coverpoint aes_mode
      {
       bins ecb     = { AES_ECB};
       bins cbc     = { AES_CBC };
       bins cfb     = { AES_CFB };
       bins ofb     = { AES_OFB };
       bins ctr     = { AES_CTR };
       bins none    = { AES_NONE };
       bins illegal = { [0:$] } with ($countones(item) != 1);
      }

    cp_key_len: coverpoint aes_keylen
      {
       bins aes_128 = {AES_128};
       bins aes_192 = {AES_192};
       bins aes_256 = {AES_256};
       bins illegal = { [0:$] } with ($countones(item) != 1);
      }

    cp_manual_operation: coverpoint aes_man_op
      {
       bins auto_mode   = { 1'b0 };
       bins manual_mode = { 1'b1 };
      }

    cp_force_0_masks: coverpoint aes_force_0mask;

    // Cross coverage points
    // All key_lens are tested in all modes
    cr_mode_key_len: cross cp_mode, cp_key_len;
    // all modes are tested in both auto an manual operation
    cr_mode_man_op:  cross cp_mode, cp_manual_operation;
    // All modes used in both incryption and decryption
    cr_mode_op:      cross cp_mode, cp_operation;
  endgroup // aes_ctrl_cg


  ///////////////////////////////////
  // Status register cover points  //
  ///////////////////////////////////

  covergroup aes_status_cg with function sample(status_t aes_status);
    option.per_instance = 1;
    option.name         = "aes_status_cg";
  endgroup // aes_status_cg


  ///////////////////////////////////
  // Trigger register cover points //
  ///////////////////////////////////

  covergroup aes_trigger_cg with function sample(bit aes_start,
                                                 bit aes_key_iv_datain_clear,
                                                 bit aes_dataout_clear,
                                                 bit aes_prng_reseed
                                                 );
    option.per_instance = 1;
    option.name         = "aes_trigger_cg";

    cp_start:                coverpoint aes_start;
    cp_key_iv_datain_clear:  coverpoint aes_key_iv_datain_clear;
    cp_dataout_clear:        coverpoint aes_dataout_clear;
    cp_prng_reseed:          coverpoint aes_prng_reseed;

    cr_clear: cross cp_key_iv_datain_clear, cp_dataout_clear;

  endgroup // aes_trigger_cg

  ///////////////////////////////////
  // Alert register cover points   //
  ///////////////////////////////////

  covergroup aes_alert_cg with function sample(alert_test_t alert_test);
    option.per_instance = 1;
    option.name         = "aes_test_alert_cg";
  endgroup // aes_alert_cg


  ///////////////////////////////////
  // Instantiation Macros          //
  ///////////////////////////////////

 `DV_FCOV_INSTANTIATE_CG(aes_ctrl_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_status_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_trigger_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_alert_cg, en_full_cov)


  ///////////////////////////////////
  // Sample functions              //
  // needed for xcelium            //
  ///////////////////////////////////

  function automatic void cg_ctrl_sample(bit                                 aes_op,
                                         bit [aes_pkg::AES_MODE_WIDTH-1:0]   aes_mode,
                                         bit [aes_pkg::AES_KEYLEN_WIDTH-1:0] aes_keylen,
                                         bit                                 aes_man_op,
                                         bit                                 aes_force_0mask
                                         );
    aes_ctrl_cg_inst.sample(aes_op, aes_mode, aes_keylen, aes_man_op, aes_force_0mask);
  endfunction

  function automatic void cg_status_sample(bit [31:0] val);
    aes_status_cg_inst.sample(val);
  endfunction

  function automatic void cg_trigger_sample(bit aes_start,
                                            bit aes_key_iv_datain_clear,
                                            bit aes_dataout_clear,
                                            bit aes_prng_reseed
                                           );
    aes_trigger_cg_inst.sample(aes_start, aes_key_iv_datain_clear, aes_dataout_clear, aes_prng_reseed);
  endfunction

  function automatic void cg_alert_test_sample(bit [31:0] val);
    aes_alert_cg_inst.sample(val);
  endfunction

endinterface
