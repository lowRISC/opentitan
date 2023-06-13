// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for AES

interface aes_cov_if
  (
   input bit   clk_i,
   input bit   idle_i
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


  covergroup aes_aux_regwen_cg  with function sample(bit regwen);
    option.per_instance = 1;
    option.name = "aes_aux_ctrl_cg";

    cp_regwen: coverpoint regwen;
  endgroup // aes_aux_regen_cg


  covergroup aes_ctrl_cg  with function sample(
             bit                                         aes_op,
             bit [aes_pkg::AES_MODE_WIDTH-1:0]           aes_mode,
             bit [aes_pkg::AES_KEYLEN_WIDTH-1:0]         aes_keylen,
             bit                                         aes_man_op,
             bit                                         aes_sideload,
             bit [aes_pkg::AES_PRNGRESEEDRATE_WIDTH-1:0] aes_prng_reseed_rate
             );
    option.per_instance = 1;
    option.name         = "aes_ctrl_cg";

    cp_operation: coverpoint aes_op
      {
       bins enc     = {AES_ENC};
       bins dec     = {AES_DEC};
       bins illegal = { [0:$] } with ($countones(item) != 1);
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

    cp_sideload: coverpoint aes_sideload;

    cp_prng_reseed: coverpoint aes_prng_reseed_rate
      {
       bins per_1   = {PER_1};
       bins per_64  = {PER_64};
       bins per_8k  = {PER_8K};
       bins illegal = {[0:$]} with ($countones(item) != 1);
      }


    // Cross coverage points
    // All key_lens are tested in all modes with sideload
    cr_mode_key_len: cross cp_mode, cp_key_len, cp_sideload;

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

    cp_idle:         coverpoint aes_status.idle;
    cp_stall:        coverpoint aes_status.stall;
    cp_out_lost:     coverpoint aes_status.output_lost;
    cp_out_valid:    coverpoint aes_status.output_valid;
    cp_in_Ready:     coverpoint aes_status.input_ready;
    cp_alert_recov:  coverpoint aes_status.alert_recov_ctrl_update_err;
    cp_alert_fatal:  coverpoint aes_status.alert_fatal_fault;

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

    cp_fatal_fault: coverpoint alert_test.fatal_fault;
    cp_recov_fault: coverpoint alert_test.recov_ctrl_update_err;
  endgroup // aes_alert_cg

  ///////////////////////////////////
  // transition cover groups       //
  ///////////////////////////////////


  // interleaving writes to each registers is allowed
  // This covergroup has a bin for each i => j combination. For example, 0 => 0 means "write to
  // data_in_0 twice in a row". 3 => 0 means "write to data_in_3 and then data_in_0"
  // it also checks that we attemp to access the register while DUT is !idle
  // the test well verify correct behavior (read and write data is accepted under certain
  // conditions
  covergroup aes_wr_data_interleave_cg with function sample(int data_in, bit idle);
    option.per_instance = 1;
    option.name         = "aes_wr_data_interleave_cg";

    cp_wr_data: coverpoint data_in
      {
        bins reg_interleave[] = (0,1,2,3 => 0,1,2,3);
      }

    // Data can still be accepted when !Idle
    // check that we verify this
    cp_wr_not_idle: coverpoint data_in iff(!idle)
      {
        bins data_not_idle = {[0:3]};
      }
  endgroup


  // interleaving writes to each registers is allowed
  // This covergroup has a bin for each i => j combination. For example, 0 => 0 means "reading
  // data_out_0 twice in a row". 3 => 0 means "reading data_out_3 and then data_out_0"
  // it also checks that we attemp to access the register while DUT is !idle
  // the test well verify correct behavior (read and write data is accepted under certain
  // conditions
  covergroup aes_rd_data_interleave_cg with function sample(int data_out, bit idle);
    option.per_instance = 1;
    option.name         = "aes_rd_data_interleave_cg";

    cp_rd_data: coverpoint data_out
      {
        bins reg_interleave[] = (0,1,2,3 => 0,1,2,3);
      }

    // check that we see reads when not idle
    cp_wr_not_idle: coverpoint data_out iff(!idle)
      {
        bins data_not_idle = {[0:3]};
      }
  endgroup

  // interleaving writes to each registers is allowed
  // This covergroup has a bin for each i => j combination. For example, 0 => 0 means "write to
  // iv_0 twice in a row". 3 => 0 means "write to iv_3 and then iv_0"
  // it also checks that we attemp to access the register while DUT is !idle
  // the test well verify correct behavior (read and write data is accepted under certain
  // conditions
  covergroup aes_iv_interleave_cg with function sample(int iv, bit idle);
    option.per_instance = 1;
    option.name         = "aes_iv_interleave_cg";

    cp_iv: coverpoint iv
      {
        bins reg_interleave[] = (0,1,2,3 => 0,1,2,3);
      }

    // Writes to IV should be ignored when !IDLE
    // check that we actually try to do this
    cp_wr_not_idle: coverpoint iv iff(!idle)
      {
        bins iv_not_idle = {[0:3]};
      }
  endgroup

  // interleaving writes to each registers is allowed
  // This covergroup has a bin for each i => j combination. For example, 0 => 0 means "write to
  // key_0 twice in a row". 3 => 0 means "write to key_3 and then key_0"
  // it also checks that we attemp to access the register while DUT is !idle
  // the test well verify correct behavior (read and write data is accepted under certain
  // conditions
  covergroup aes_key_interleave_cg with function sample(int key, bit idle);
    option.per_instance = 1;
    option.name         = "aes_key_interleave_cg";

    cp_key: coverpoint key
      {
      // we don't care if all transitions have been coverd
      // just that we interleave
        bins from_0toX  = ( 0 => [1:15]);
        bins from_1toX  = ( 1 => 0)     ,(1  => [2:15] );
        bins from_2toX  = ( 2 => [0:1]) ,(2  => [3:15] );
        bins from_3toX  = ( 3 => [0:2]) ,(3  => [4:15] );
        bins from_4toX  = ( 4 => [0:3]) ,(4  => [5:15] );
        bins from_5toX  = ( 5 => [0:4]) ,(5  => [6:15] );
        bins from_6toX  = ( 6 => [0:5]) ,(6  => [7:15] );
        bins from_7toX  = ( 7 => [0:6]) ,(7  => [8:15] );
        bins from_8toX  = ( 8 => [0:7]) ,(8  => [9:15] );
        bins from_9toX  = ( 9 => [0:8]) ,(9  => [10:15]);
        bins from_10toX = (10 => [0:9]) ,(10 => [11:15]);
        bins from_11toX = (11 => [0:10]),(11 => [12:15]);
        bins from_12toX = (12 => [0:11]),(12 => [13:15]);
        bins from_13toX = (13 => [0:12]),(14 => [14:15]);
        bins from_14toX = (14 => [0:13]),(14 => 15);
        bins from_15toX = (15 => [0:14]);
      }

    // Writes to IV should be ignored when !IDLE
    // check that we actually try to do this
    cp_wr_not_idle: coverpoint key iff(!idle)
      {
        bins key_not_idle = {[0:3]};
      }
  endgroup // aes_key_interleave_cg

  // interleaving writes to each registers is allowed
  // This covergroup has a bin for each i => j combination. For example, 0 => 0 means "write to
  // data_in twice in a row". 2 => 0 means "write to iv and then data_in"
  covergroup aes_reg_interleave_cg with function sample(bit [1:0] value);
    option.per_instance = 1;
    option.name         = "aes_reg_interleave_cg";

    // data in = 0
    // key     = 1
    // iv      = 2
    cp_reg: coverpoint value
      {
        bins DataToX = (0 => 1,2);
        bins KeyToX  = (1 => 0,2);
        bins IvToX   = (2 => 0,1);
      }
  endgroup // aes_reg_interleave_cg


  ///////////////////////////////////
  // Instantiation Macros          //
  ///////////////////////////////////
 `DV_FCOV_INSTANTIATE_CG(aes_aux_regwen_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_ctrl_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_status_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_trigger_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_alert_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_wr_data_interleave_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_rd_data_interleave_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_iv_interleave_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_key_interleave_cg, en_full_cov)
 `DV_FCOV_INSTANTIATE_CG(aes_reg_interleave_cg, en_full_cov)


  ///////////////////////////////////
  // Sample functions              //
  // needed for xcelium            //
  ///////////////////////////////////

  function automatic void cg_aux_regwen_sample(bit val);
    aes_aux_regwen_cg_inst.sample(val);
  endfunction

  function automatic void cg_ctrl_sample(
           bit                                         aes_op,
           bit [aes_pkg::AES_MODE_WIDTH-1:0]           aes_mode,
           bit [aes_pkg::AES_KEYLEN_WIDTH-1:0]         aes_keylen,
           bit                                         aes_man_op,
           bit                                         aes_sideload,
           bit [aes_pkg::AES_PRNGRESEEDRATE_WIDTH-1:0] aes_prng_reseed_rate
           );
    aes_ctrl_cg_inst.sample(aes_op, aes_mode, aes_keylen, aes_man_op,
                            aes_sideload, aes_prng_reseed_rate );
  endfunction

  function automatic void cg_status_sample(bit [31:0] val);
    aes_status_cg_inst.sample(val);
  endfunction

  function automatic void cg_trigger_sample(bit aes_start,
                                            bit aes_key_iv_datain_clear,
                                            bit aes_dataout_clear,
                                            bit aes_prng_reseed
                                            );
    aes_trigger_cg_inst.sample(aes_start,
                               aes_key_iv_datain_clear,
                               aes_dataout_clear,
                               aes_prng_reseed);
  endfunction

  function automatic void cg_alert_test_sample(bit [31:0] val);
    aes_alert_cg_inst.sample(val);
  endfunction

  function automatic void cg_wr_data_sample(int data_in);
    aes_wr_data_interleave_cg_inst.sample(data_in, idle_i);
    aes_reg_interleave_cg_inst.sample(0);
  endfunction

  function automatic void cg_rd_data_sample(int data_out);
    aes_rd_data_interleave_cg_inst.sample(data_out, idle_i);
  endfunction

  function automatic void cg_iv_sample(int iv);
    aes_iv_interleave_cg_inst.sample(iv, idle_i);
    aes_reg_interleave_cg_inst.sample(2);
  endfunction

  function automatic void cg_key_sample(int key);
    aes_key_interleave_cg_inst.sample(key, idle_i);
    aes_reg_interleave_cg_inst.sample(1);
  endfunction
endinterface
