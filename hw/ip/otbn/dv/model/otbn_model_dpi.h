// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_DPI_H_
#define OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_DPI_H_

// The DPI exports for OtbnModel. See also otbn_model_pkg.sv, where they are
// declared for the SystemVerilog side.
//
// These are defined in a separate file from otbn_model.h because otherwise
// something like otbn_top_sim.cc will see both these defines and the
// auto-generated ones that Verilator produces in e.g. Votbn_top_sim__Dpi.h. The
// latter use void* for all the chandle arguments and some versions of GCC treat
// the resulting signatures as incompatible.

extern "C" {

// Create an OtbnModel object. Will always succeed.
OtbnModel *otbn_model_init(const char *mem_scope, const char *design_scope,
                           unsigned imem_words, unsigned dmem_words);

// Delete an OtbnModel
void otbn_model_destroy(OtbnModel *model);

// Call edn_step function of OtbnModel
void edn_model_step(OtbnModel *model,
                    svLogicVecVal *edn_rnd_data /* logic [31:0] */);

// Signal RTL is finished processing RND data to Model
void edn_model_rnd_cdc_done(OtbnModel *model);

// The main entry point to the OTBN model, exported from here and used in
// otbn_core_model.sv.
//
// This communicates state with otbn_core_model.sv through the model_state
// parameter, which has the following bits:
//
//    Bit 0:      running       True if the model is currently running
//    Bit 1:      check_due     True if the model finished running last cycle
//    Bit 2:      failed_step   Something failed when trying to start/step ISS
//    Bit 3:      failed_cmp    Consistency check at end of run failed
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
// write out err_bits and stop_pc and do the post-run task. If the model's
// design_scope is non-empty, it should be the scope of an RTL implementation.
// In that case, we compare register and memory contents with that
// implementation, printing to stderr and setting the failed_cmp bit if there
// are any mismatches. If the model's design_scope is the empty string, we grab
// the contents of DMEM from the ISS and inject them into the simulation
// memory.
//
// If start is true, we start the model and then step once (as
// above).
unsigned otbn_model_step(OtbnModel *model, svLogic start, unsigned model_state,
                         svLogic edn_urnd_data_valid,
                         svBitVecVal *status /* bit [7:0] */,
                         svBitVecVal *insn_cnt /* bit [31:0] */,
                         svBitVecVal *err_bits /* bit [31:0] */,
                         svBitVecVal *stop_pc /* bit [31:0] */);

// Tell the model to mark all of IMEM as invalid so that any fetch causes an
// integrity error. Returns 0 on success or -1 on failure.
int otbn_model_invalidate_imem(OtbnModel *model);

// Flush any information in the model
void otbn_model_reset(OtbnModel *model);

// Take loop warps from an OtbnMemUtil
void otbn_take_loop_warps(OtbnModel *model, OtbnMemUtil *memutil);
}

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_DPI_H_
