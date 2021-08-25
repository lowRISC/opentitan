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

class ISSWrapper;

class OtbnModel {
 public:
  OtbnModel(const std::string &mem_scope, const std::string &design_scope,
            unsigned imem_size_words, unsigned dmem_size_words);
  ~OtbnModel();

  // Replace any current loop warps with those from memutil. Returns 0
  // on success or -1 on failure. In the latter case, a message will
  // already have been written to stderr.
  int take_loop_warps(const OtbnMemUtil &memutil);

  // True if this model is running in a simulation that has an RTL
  // implementation too (which needs checking).
  bool has_rtl() const { return !design_scope_.empty(); }

  // Start a new run with the model, writing IMEM/DMEM and jumping to the given
  // start address. Returns 0 on success; -1 on failure.
  int start(unsigned start_addr);

  // Step once in the model. Returns 1 if the model has finished, 0 if not and
  // -1 on failure. If gen_trace is true, pass trace entries to the trace
  // checker. If the model has finished, writes otbn.ERR_BITS to *err_bits.
  int step(svLogic edn_rnd_data_valid,
           svLogicVecVal *edn_rnd_data, /* logic [255:0] */
           svLogic edn_urnd_data_valid, svBitVecVal *insn_cnt /* bit [31:0] */,
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

  // Flush any information in the model
  void reset();

 private:
  // Constructs an ISS wrapper if necessary. If something goes wrong, this
  // function prints a message and then returns null. If ensure is true, it
  // will never return null without printing a message, so error handling at
  // the callsite can silently return a failure code.
  ISSWrapper *ensure_wrapper();

  // Read the contents of the ISS's memory
  std::vector<uint8_t> get_sim_memory(bool is_imem) const;

  // Set the contents of the ISS's memory
  void set_sim_memory(bool is_imem, const std::vector<uint8_t> &data);

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
  // time it's actually needed. Use ensure_iss() to create as needed.
  std::unique_ptr<ISSWrapper> iss_;
  OtbnMemUtil mem_util_;
  std::string design_scope_;
  unsigned imem_size_words_, dmem_size_words_;
};

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_OTBN_MODEL_H_
