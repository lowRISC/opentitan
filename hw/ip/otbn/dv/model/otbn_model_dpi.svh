// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Imports for the functions defined in otbn_model.h. There are documentation comments explaining
// what the functions do there. This needs to be included into otbn_core_model (because we need
// svGetScope() to point at the model instance).

`ifndef SYNTHESIS
import "DPI-C" context function chandle otbn_model_init(string mem_scope,
                                                        string design_scope);

import "DPI-C" function void otbn_model_destroy(chandle model);

import "DPI-C" function void otbn_take_loop_warps(chandle model, chandle memutil);

import "DPI-C" function int otbn_has_loop_warps(chandle memutil);

import "DPI-C" function int otbn_model_edn_flush(chandle model);

import "DPI-C" function int otbn_model_edn_rnd_step(chandle model,
                                                    logic [31:0] edn_rnd_data,
                                                    bit fips_err);

import "DPI-C" function int otbn_model_edn_urnd_step(chandle model,
                                                     logic [31:0] edn_urnd_data);

import "DPI-C" function int otbn_model_rnd_cdc_done(chandle model);

import "DPI-C" function int otbn_model_urnd_cdc_done(chandle model);

import "DPI-C" function int otbn_model_otp_key_cdc_done(chandle model);

import "DPI-C" function
  int otbn_model_set_keymgr_value(chandle model, logic [383:0] key0,
                                  logic [383:0] key1, bit valid);

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

import "DPI-C" function int otbn_model_invalidate_dmem(chandle model);

import "DPI-C" function int otbn_model_set_software_errs_fatal(chandle model, bit new_val);

import "DPI-C" function int otbn_set_no_sec_wipe_chk(chandle model);

import "DPI-C" function int otbn_model_step_crc(chandle          model,
                                                bit [47:0]       item,
                                                inout bit [31:0] state);

import "DPI-C" context function int otbn_model_reset(chandle          model,
                                                     inout bit [7:0]  status,
                                                     inout bit [31:0] insn_cnt,
                                                     inout bit        rnd_req,
                                                     inout bit [31:0] err_bits,
                                                     inout bit [31:0] stop_pc);

import "DPI-C" function int otbn_model_send_err_escalation(chandle    model,
                                                           bit [31:0] err_val,
                                                           bit        lock_immediately);

import "DPI-C" function int otbn_model_set_rma_req(chandle   model,
                                                   bit [3:0] rma_req);

import "DPI-C" function int otbn_model_initial_secure_wipe(chandle model);

import "DPI-C" function int otbn_disable_stack_check(chandle model);

`endif // SYNTHESIS
