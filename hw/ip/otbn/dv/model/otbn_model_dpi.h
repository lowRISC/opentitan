// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_DPI_H_
#define OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_DPI_H_

// The DPI exports for OtbnModel. See also otbn_model_dpi.svh, where
// they are declared for the SystemVerilog side.
//
// These are defined in a separate file from otbn_model.h because otherwise
// something like otbn_top_sim.cc will see both these defines and the
// auto-generated ones that Verilator produces in e.g. Votbn_top_sim__Dpi.h. The
// latter use void* for all the chandle arguments and some versions of GCC treat
// the resulting signatures as incompatible.

extern "C" {

// Create an OtbnModel object. Will always succeed.
OtbnModel *otbn_model_init(const char *mem_scope, const char *design_scope);

// Delete an OtbnModel
void otbn_model_destroy(OtbnModel *model);

// Take loop warps from an OtbnMemUtil
void otbn_take_loop_warps(OtbnModel *model, OtbnMemUtil *memutil);

// Returns non-zero if an OtbnMemUtil contains loop warps
int otbn_has_loop_warps(OtbnMemUtil *memutil);

// Flush URND and RND EDN data from model because of edn_rst_n signal. Returns
// 0 on success; -1 on error.
int otbn_model_edn_flush(OtbnModel *model);

// Call edn_rnd_step function of OtbnModel. Returns 0 on success; -1 on error.
int otbn_model_edn_rnd_step(OtbnModel *model,
                            svLogicVecVal *edn_rnd_data /* logic [31:0] */,
                            unsigned char fips_err);

// Call edn_urnd_step function of OtbnModel. Returns 0 on success; -1 on error.
int otbn_model_edn_urnd_step(OtbnModel *model,
                             svLogicVecVal *edn_urnd_data /* logic [31:0] */);

// Signal RTL is finished processing RND data to Model. Returns 0 on success;
// -1 on error.
int otbn_model_rnd_cdc_done(OtbnModel *model);

// Signal RTL is finished processing EDN data for URND to Model. Returns 0 on
// success; -1 on error.
int otbn_model_urnd_cdc_done(OtbnModel *model);

// Signal RTL is finished processing OTP key to the Model. Returns 0 on
// success; -1 on error.
int otbn_model_otp_key_cdc_done(OtbnModel *model);

// Pass keymgr data to model. Returns 0 on success; -1 on error.
int otbn_model_set_keymgr_value(OtbnModel *model, svLogicVecVal *key0,
                                svLogicVecVal *key1, unsigned char valid);

// The main entry point to the OTBN model, exported from here and used in
// otbn_core_model.sv.
//
// This communicates state with otbn_core_model.sv through the model_state
// parameter, which has the following bits:
//
//    Bit 0:      running       True if the model is currently running
//    Bit 1:      check_due     True if the model finished running last cycle
//    Bit 2:      failed_step   Something failed when trying to start/step ISS
//
// The otbn_model_step function should only be called when either the model is
// running (bit 0 of model_state), has a check due (bit 1 of model_state), or
// when start is asserted. At other times, it will return immediately (but
// wastes a DPI call).
//
// If the model is running and start is false, otbn_model_step steps the ISS by
// a single cycle. If something goes wrong, it will set failed_step to true and
// running to false. Otherwise, it writes the new value of otbn.INSN_CNT to
// *insn_cnt.
//
// If nothing goes wrong and the ISS finishes its run, we set running to false,
// write out err_bits and stop_pc and set check_due to ensure otbn_model_check
// runs on the next negedge of the clock.
//
unsigned otbn_model_step(OtbnModel *model, unsigned model_state,
                         svBitVecVal *cmd /* bit [7:0] */,
                         svBitVecVal *status /* bit [7:0] */,
                         svBitVecVal *insn_cnt /* bit [31:0] */,
                         svBitVecVal *rnd_req /* bit [0:0] */,
                         svBitVecVal *err_bits /* bit [31:0] */,
                         svBitVecVal *stop_pc /* bit [31:0] */);

// This gets run if the otbn_model_step function sets the check_due bit in its
// model_state bitfield (see above). If the model's design_scope is non-empty,
// it should be the scope of an RTL implementation. In that case, we compare
// register and memory contents with that implementation, printing to stderr
// and setting the failed_cmp bit if there are any mismatches. If the model's
// design_scope is the empty string, we grab the contents of DMEM from the ISS
// and inject them into the simulation memory.
//
// Returns 1 on success; 0 on failure.
int otbn_model_check(OtbnModel *model, svBitVecVal *mismatch /* bit [0:0] */);

// Tell the model to mark all of IMEM as invalid so that any fetch causes an
// integrity error. Returns 0 on success or -1 on failure.
int otbn_model_invalidate_imem(OtbnModel *model);

// Tell the model to mark all of DMEM as invalid so that any load causes an
// integrity error. Returns 0 on success or -1 on failure.
int otbn_model_invalidate_dmem(OtbnModel *model);

// Tell the model to set software_errs_fatal bit in ctrl register. Once this bit
// is set, any software error will be ellevated to fatal error from recoverable
// error.
int otbn_model_set_software_errs_fatal(OtbnModel *model, unsigned char new_val);

// Tell the model to not execute checks to see if secure wiping has written
// random data to all registers before wiping them with zeroes.
int otbn_set_no_sec_wipe_chk(OtbnModel *model);

// Disable stack integrity checks
int otbn_disable_stack_check(OtbnModel *model);

// Step the CRC calculation for item
//
// state is an inout parameter and should be updated in-place. This is
// a "pure" function: there isn't actually any model state that gets
// updated by calling it. Returns 0 on success or -1 on failure.
int otbn_model_step_crc(OtbnModel *model, svBitVecVal *item /* bit [47:0] */,
                        svBitVecVal *state /* inout bit [31:0] */);

// Flush any information in the model. Returns 0 on success; -1 on error.
int otbn_model_reset(OtbnModel *model, svBitVecVal *status /* bit [7:0] */,
                     svBitVecVal *insn_cnt /* bit [31:0] */,
                     svBitVecVal *rnd_req /* bit [0:0] */,
                     svBitVecVal *err_bits /* bit [31:0] */,
                     svBitVecVal *stop_pc /* bit [31:0] */);

// React to an error escalation. Returns 0 on success or -1 on failure.
int otbn_model_send_err_escalation(OtbnModel *model,
                                   svBitVecVal *err_val /* bit [31:0] */,
                                   svBit lock_immediately);

// Send an RMA request value to the model
int otbn_model_set_rma_req(OtbnModel *model,
                           svBitVecVal *rma_req /* bit [3:0] */);

// Trigger initial secure wipe.
int otbn_model_initial_secure_wipe(OtbnModel *model);
}

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_DPI_H_
