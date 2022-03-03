// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_H_
#define OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_H_

#include <cstdint>
#include <stdexcept>
#include <string>
#include <svdpi.h>
#include <vector>

#include "otbn_memutil.h"

struct ISSWrapper;

class OtbnModel {
 public:
  OtbnModel(const std::string &mem_scope, const std::string &design_scope,
            bool enable_secure_wipe);
  ~OtbnModel();

  // Replace any current loop warps with those from memutil. Returns 0
  // on success or -1 on failure. In the latter case, a message will
  // already have been written to stderr.
  int take_loop_warps(const OtbnMemUtil &memutil);

  // True if this model is running in a simulation that has an RTL
  // implementation too (which needs checking).
  bool has_rtl() const { return !design_scope_.empty(); }

  // Start a new run with the model, writing IMEM/DMEM and jumping to address
  // zero. Returns 0 on success; -1 on failure.
  int start();

  // Starts an IMEM Secure wipe operation
  int imem_wipe();

  // Starts an DMEM Secure wipe operation
  int dmem_wipe();

  // Flush EDN data from model because of edn_rst_n
  void edn_flush();

  // EDN Step sends ISS the RND data when ACK signal is high.
  void edn_rnd_step(svLogicVecVal *edn_rnd_data /* logic [31:0] */);

  // Set or unset the two keys from keymgr. Returns 0 on success or -1
  // on error.
  int set_keymgr_value(svLogicVecVal *key0 /* logic [383:0] */,
                       svLogicVecVal *key1 /* logic [383:0] */,
                       unsigned char valid);

  // EDN Step sends ISS the URND related EDN data when ACK signal is high.
  void edn_urnd_step(svLogicVecVal *edn_urnd_data /* logic [31:0] */);

  // Signals that RTL is finished processing OTP key
  void otp_key_cdc_done();

  // Signals that RTL is finished processing RND data from EDN
  void edn_rnd_cdc_done();

  // Signals that RTL is finished processing data from EDN for URND
  void edn_urnd_cdc_done();

  // Step once in the model. Returns 1 if the model has finished, 0 if not and
  // -1 on failure. If gen_trace is true, pass trace entries to the trace
  // checker. If the model has finished, writes otbn.ERR_BITS to *err_bits.
  int step(svBitVecVal *status /* bit [7:0] */,
           svBitVecVal *insn_cnt /* bit [31:0] */,
           svBitVecVal *rnd_req /* bit [0:0] */,
           svBitVecVal *err_bits /* bit [31:0] */,
           svBitVecVal *stop_pc /* bit [31:0] */);

  // Check model against RTL (if there is any) when a run has finished. Prints
  // messages to stderr on failure or mismatch. Returns 1 for a match, 0 for a
  // mismatch, -1 for some other failure.
  int check() const;

  // Grab contents of dmem from the model and load it back into the RTL
  // simulation. This is used when there's no RTL model of the design. Returns
  // 0 on success; -1 on failure.
  int load_dmem();

  // Mark all of IMEM as invalid so that any fetch causes an integrity
  // error. Returns 0 on success; -1 on failure.
  int invalidate_imem();

  // Mark all of DMEM as invalid so that any load causes an integrity
  // error. Returns 0 on success; -1 on failure.
  int invalidate_dmem();

  // Step CRC by consuming 48 bits of data.
  //
  // This doesn't actually update any internal state: we're just using the
  // otbn_model framework as a convenient connection between SystemVerilog and
  // Python. Returns 0 on success; -1 on failure.
  int step_crc(const svBitVecVal *item /* bit [47:0] */,
               svBitVecVal *state /* bit [31:0] */);

  // Flush any information in the model
  void reset();

  // React to a lifecycle controller escalation signal. Returns 0 on
  // success; -1 on failure.
  int send_lc_escalation();

  // Returns true if we have an ISS wrapper and it has the START_WIPE flag
  // asserted
  bool is_at_start_of_wipe() const;

 private:
  // Constructs an ISS wrapper if necessary. If something goes wrong, this
  // function prints a message and then returns null. If ensure is true, it
  // will never return null without printing a message, so error handling at
  // the callsite can silently return a failure code.
  ISSWrapper *ensure_wrapper();

  // Read the contents of the ISS's memory
  Ecc32MemArea::EccWords get_sim_memory(bool is_imem) const;

  // Set the contents of the ISS's memory
  void set_sim_memory(bool is_imem, const Ecc32MemArea::EccWords &words);

  // Grab contents of dmem from the model and compare them with the RTL. Prints
  // messages to stderr on failure or mismatch. Returns true on success; false
  // on mismatch. Throws a std::runtime_error on failure.
  bool check_dmem(ISSWrapper &iss) const;

  // Compare contents of ISS registers with those from the design. Prints
  // messages to stderr on failure or mismatch. Returns true on success; false
  // on mismatch. Throws a std::runtime_error on failure.
  bool check_regs(ISSWrapper &iss) const;

  // Compare contents of ISS call stack with those from the design. Prints
  // messages to stderr on failure or mismatch. Returns true on success; false
  // on mismatch. Throws a std::runtime_error on failure.
  bool check_call_stack(ISSWrapper &iss) const;

  // We want to create the model in an initial block in the SystemVerilog
  // simulation, but might not actually want to spawn the ISS. To handle that
  // in a non-racy way, the most convenient thing is to spawn the ISS the first
  // time it's actually needed. Use ensure_wrapper() to create as needed.
  std::unique_ptr<ISSWrapper> iss_;

  OtbnMemUtil mem_util_;
  std::string design_scope_;
  bool enable_secure_wipe_;
};

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_H_
