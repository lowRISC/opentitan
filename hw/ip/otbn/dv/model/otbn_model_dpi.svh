// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Imports for the functions defined in otbn_model.h. There are documentation comments explaining
// what the functions do there. This needs to be included into otbn_core_model (because we need
// svGetScope() to point at the model instance).

`ifndef SYNTHESIS
import "DPI-C" context function chandle otbn_model_init(string mem_scope,
                                                        string design_scope,
                                                        bit    enable_secure_wipe);

import "DPI-C" function void otbn_model_destroy(chandle model);

import "DPI-C" function void edn_model_flush(chandle model);

import "DPI-C" function void edn_model_rnd_step(chandle model,
                                                logic [31:0] edn_rnd_data);

import "DPI-C" function void edn_model_urnd_step(chandle model,
                                                 logic [31:0] edn_urnd_data);

import "DPI-C" function
  void edn_model_urnd_cdc_done(chandle model);

import "DPI-C" function
  int otbn_model_set_keymgr_value(chandle model, logic [383:0] key0,
                                  logic [383:0] key1, bit valid);

import "DPI-C" function
  void edn_model_rnd_cdc_done(chandle model);

import "DPI-C" function
  void otp_key_cdc_done(chandle model);

import "DPI-C" context function
  int unsigned otbn_model_step(chandle          model,
                               int unsigned     model_state,
                               bit       [7:0]  cmd,
                               inout bit [7:0]  status,
                               inout bit [31:0] insn_cnt,
                               inout bit        rnd_req,
                               inout bit [31:0] err_bits,
                               inout bit [31:0] stop_pc);

import "DPI-C" context function int otbn_model_check(chandle model, inout bit mismatch);

import "DPI-C" function int otbn_model_invalidate_imem(chandle model);

import "DPI-C" function int otbn_model_step_crc(chandle          model,
                                                bit [47:0]       item,
                                                inout bit [31:0] state);

import "DPI-C" context function int otbn_model_invalidate_dmem(chandle model);

import "DPI-C" function void otbn_model_reset(chandle model);

import "DPI-C" function void otbn_take_loop_warps(chandle model, chandle memutil);

import "DPI-C" function int otbn_model_send_lc_escalation(chandle model);
`endif // SYNTHESIS
