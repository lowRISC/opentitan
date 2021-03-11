// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <algorithm>
#include <cassert>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <svdpi.h>

#include "iss_wrapper.h"
#include "otbn_trace_checker.h"
#include "sv_scoped.h"

namespace {
// An extremely thin wrapper around ISSWrapper. The point is that we want to
// create the model in an initial block in the SystemVerilog simulation, but
// might not actually want to spawn the ISS. To handle that in a non-racy
// way, the most convenient thing is to spawn the ISS on the first call to
// otbn_model_step.
struct OtbnModel {
 public:
  bool ensure() {
    if (!iss) {
      try {
        iss.reset(new ISSWrapper());
      } catch (const std::runtime_error &err) {
        std::cerr << "Error when constructing ISS wrapper: " << err.what()
                  << "\n";
        return false;
      }
    }
    assert(iss);
    return true;
  }

  std::unique_ptr<ISSWrapper> iss;
};
}  // namespace

extern "C" {
// DPI imports, implemented in SystemVerilog
int simutil_get_mem(int index, svBitVecVal *val);
int simutil_set_mem(int index, const svBitVecVal *val);

// These functions are only implemented if DesignScope != "", i.e. if we're
// running a block-level simulation. Code needs to check at runtime if
// otbn_rf_peek() and otbn_stack_element_peek() are available before calling
// them.
int otbn_rf_peek(int index, svBitVecVal *val) __attribute__((weak));
int otbn_stack_element_peek(int index, svBitVecVal *val) __attribute__((weak));
}

#define RUNNING_BIT (1U << 0)
#define CHECK_DUE_BIT (1U << 1)
#define FAILED_STEP_BIT (1U << 2)
#define FAILED_CMP_BIT (1U << 3)

// The main entry point to the OTBN model, exported from here and used in
// otbn_core_model.sv.
//
// This communicates state with otbn_core_model.sv through the status
// parameter, which has the following bits:
//
//    Bit 0:      running       True if the model is currently running
//    Bit 1:      check_due     True if the model finished running last cycle
//    Bit 2:      failed_step   Something failed when trying to start/step ISS
//    Bit 3:      failed_cmp    Consistency check at end of run failed
//
// The otbn_model_step function should only be called when either the model is
// running (bit 0 of status), has a check due (bit 1 of status), or when
// start_i is asserted. At other times, it will return immediately (but wastes
// a DPI call).
//
// If the model is running and start_i is false, otbn_model_step steps the ISS
// by a single cycle. If something goes wrong, it will set failed_step to true
// and running to false.
//
// If nothing goes wrong, but the ISS finishes its run, we set running to
// false, write out err_code and do the post-run task. If design_scope is
// non-empty, it should be the scope of an RTL implementation. In that case, we
// compare register and memory contents with that implementation, printing to
// stderr and setting the failed_cmp bit if there are any mismatches. If
// design_scope is the empty string, we grab the contents of DMEM from the ISS
// and inject them into the memory at dmem_scope.
//
// If start_i is true, we start the model at start_addr and then step once (as
// described above).
extern "C" unsigned otbn_model_step(OtbnModel *model, const char *imem_scope,
                                    unsigned imem_words, const char *dmem_scope,
                                    unsigned dmem_words,
                                    const char *design_scope, svLogic start_i,
                                    unsigned start_addr, unsigned status,
                                    svBitVecVal *err_code /* bit [31:0] */);

// Use simutil_get_mem to read data one word at a time from the given scope and
// collect the results up in a vector of uint8_t values.
static std::vector<uint8_t> get_sim_memory(const char *scope, size_t num_words,
                                           size_t word_size) {
  SVScoped scoped(scope);

  // simutil_get_mem passes data as a packed array of svBitVecVal words. It
  // only works for memories of size at most 312 bits, so we can just allocate
  // 312/8 = 39 bytes as 39/sizeof(svBitVecVal) words on the stack.
  assert(word_size <= 312 / 8);
  svBitVecVal buf[312 / 8 / sizeof(svBitVecVal)];

  std::vector<uint8_t> ret;

  for (size_t w = 0; w < num_words; w++) {
    if (!simutil_get_mem(w, buf)) {
      std::ostringstream oss;
      oss << "Cannot get memory at word " << w << " from scope " << scope
          << ".\n";
      throw std::runtime_error(oss.str());
    }

    // Append the first word_size bytes of data to ret.
    std::copy_n(reinterpret_cast<const char *>(buf), word_size,
                std::back_inserter(ret));
  }

  return ret;
}

// Use simutil_get_mem to write data one word at a time to the given scope.
static void set_sim_memory(const std::vector<uint8_t> &data, const char *scope,
                           size_t num_words, size_t word_size) {
  SVScoped scoped(scope);

  assert(num_words * word_size == data.size());

  // See get_sim_memory for why this array is sized like this.
  assert(word_size <= 312 / 8);
  svBitVecVal buf[312 / 8 / sizeof(svBitVecVal)];

  for (size_t w = 0; w < num_words; w++) {
    const uint8_t *p = &data[w * word_size];
    memcpy(buf, p, word_size);

    if (!simutil_set_mem(w, buf)) {
      std::ostringstream oss;
      oss << "Cannot set memory at word " << w << " for scope " << scope
          << ".\n";
      throw std::runtime_error(oss.str());
    }
  }
}

// Read (the start of) the contents of a file at path as a vector of bytes.
// Expects num_bytes bytes of data.
static std::vector<uint8_t> read_vector_from_file(const std::string &path,
                                                  size_t num_bytes) {
  std::filebuf fb;
  if (!fb.open(path.c_str(), std::ios::in | std::ios::binary)) {
    std::ostringstream oss;
    oss << "Cannot open the file '" << path << "'.";
    throw std::runtime_error(oss.str());
  }

  std::vector<uint8_t> buf(num_bytes);
  std::streamsize chars_in =
      fb.sgetn(reinterpret_cast<char *>(&buf[0]), num_bytes);

  if (chars_in != num_bytes) {
    std::ostringstream oss;
    oss << "Cannot read " << num_bytes << " bytes of memory data from " << path
        << " (actually got " << chars_in << ").";
    throw std::runtime_error(oss.str());
  }

  return buf;
}

// Write a vector of bytes to a new file at path
static void write_vector_to_file(const std::string &path,
                                 const std::vector<uint8_t> &data) {
  std::filebuf fb;
  if (!fb.open(path.c_str(), std::ios::out | std::ios::binary)) {
    std::ostringstream oss;
    oss << "Cannot open the file '" << path << "'.";
    throw std::runtime_error(oss.str());
  }

  // Write out the data
  std::streamsize chars_out =
      fb.sputn(reinterpret_cast<const char *>(&data[0]), data.size());

  if (chars_out != data.size()) {
    std::ostringstream oss;
    oss << "Cannot write " << data.size() << " bytes of memory data to " << path
        << "' (actually wrote " << chars_out << ").";
    throw std::runtime_error(oss.str());
  }
}

// Dump the memory at the given scope to a file at path.
static void dump_memory_to_file(const std::string &path, const char *scope,
                                size_t num_words, size_t word_size) {
  write_vector_to_file(path, get_sim_memory(scope, num_words, word_size));
}

// Read data from the given file and then write it into the memory at the given
// scope.
static void load_memory_from_file(const std::string &path, const char *scope,
                                  size_t num_words, size_t word_size) {
  size_t num_bytes = num_words * word_size;
  set_sim_memory(read_vector_from_file(path, num_bytes), scope, num_words,
                 word_size);
}

extern "C" OtbnModel *otbn_model_init() { return new OtbnModel; }

extern "C" void otbn_model_destroy(OtbnModel *model) { delete model; }

// Start a new run with the model, writing IMEM/DMEM and jumping to the given
// start address. Returns 0 on success; -1 on failure.
static int start_model(OtbnModel *model, const char *imem_scope,
                       unsigned imem_words, const char *dmem_scope,
                       unsigned dmem_words, unsigned start_addr) {
  assert(model);
  assert(imem_words >= 0);
  assert(dmem_words >= 0);
  assert(start_addr < (imem_words * 4));

  if (!model->ensure())
    return -1;
  assert(model->iss);
  ISSWrapper &iss = *model->iss;

  std::string ifname(iss.make_tmp_path("imem"));
  std::string dfname(iss.make_tmp_path("dmem"));

  try {
    dump_memory_to_file(dfname, dmem_scope, dmem_words, 32);
    dump_memory_to_file(ifname, imem_scope, imem_words, 4);
  } catch (const std::exception &err) {
    std::cerr << "Error when dumping memory contents: " << err.what() << "\n";
    return -1;
  }

  try {
    iss.load_d(dfname);
    iss.load_i(ifname);
    iss.start(start_addr);
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when starting ISS: " << err.what() << "\n";
    return -1;
  }

  return 0;
}

// Step once in the model. Returns 1 if the model has finished, 0 if not and -1
// on failure. If gen_trace is true, pass trace entries to the trace checker.
// If the model has finished, writes otbn.ERR_CODE to *err_code.
static int step_model(OtbnModel *model, bool gen_trace, uint32_t *err_code) {
  assert(model);
  assert(err_code);

  if (!model->ensure())
    return -1;
  assert(model->iss);
  ISSWrapper &iss = *model->iss;

  try {
    std::pair<bool, uint32_t> ret = iss.step(gen_trace);
    if (ret.first) {
      *err_code = ret.second;
      return 1;
    } else {
      return 0;
    }
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when stepping ISS: " << err.what() << "\n";
    return -1;
  }
}

// Grab contents of dmem from the model and load it back into the RTL. Returns
// 0 on success; -1 on failure.
static int load_dmem(OtbnModel *model, const char *dmem_scope,
                     unsigned dmem_words) {
  assert(model);
  if (!model->iss) {
    std::cerr << "Cannot load dmem from OTBN model: ISS has not started.\n";
    return -1;
  }
  ISSWrapper &iss = *model->iss;

  std::string dfname(iss.make_tmp_path("dmem_out"));
  try {
    iss.dump_d(dfname);
    load_memory_from_file(dfname, dmem_scope, dmem_words, 32);
  } catch (const std::exception &err) {
    std::cerr << "Error when loading dmem from ISS: " << err.what() << "\n";
    return -1;
  }
  return 0;
}

// Grab contents of dmem from the model and compare it with the RTL.
// Prints messages to stderr on failure or mismatch. Returns true on
// success; false on mismatch. Throws a std::runtime_error on failure.
static bool check_dmem(ISSWrapper &iss, const char *dmem_scope,
                       unsigned dmem_words) {
  size_t dmem_bytes = dmem_words * 32;
  std::string dfname(iss.make_tmp_path("dmem_out"));

  iss.dump_d(dfname);
  std::vector<uint8_t> iss_data = read_vector_from_file(dfname, dmem_bytes);
  assert(iss_data.size() == dmem_bytes);

  std::vector<uint8_t> rtl_data = get_sim_memory(dmem_scope, dmem_words, 32);
  assert(rtl_data.size() == dmem_bytes);

  // If the arrays match, we're done.
  if (0 == memcmp(&iss_data[0], &rtl_data[0], dmem_bytes))
    return true;

  // If not, print out the first 10 mismatches
  std::ios old_state(nullptr);
  old_state.copyfmt(std::cerr);
  std::cerr << "ERROR: Mismatches in dmem data:\n"
            << std::hex << std::setfill('0');
  int bad_count = 0;
  for (size_t i = 0; i < dmem_bytes; ++i) {
    if (iss_data[i] != rtl_data[i]) {
      std::cerr << " @offset 0x" << std::setw(3) << i << ": rtl has 0x"
                << std::setw(2) << (int)rtl_data[i] << "; iss has 0x"
                << std::setw(2) << (int)iss_data[i] << "\n";
      ++bad_count;

      if (bad_count == 10) {
        std::cerr << " (skipping further errors...)\n";
        break;
      }
    }
  }
  std::cerr.copyfmt(old_state);
  return false;
}

template <typename T>
static std::array<T, 32> get_rtl_regs(const std::string &reg_scope) {
  std::array<T, 32> ret;
  static_assert(sizeof(T) <= 256 / 8, "Can only copy 256 bits");

  SVScoped scoped(reg_scope);

  // otbn_rf_peek passes data as a packed array of svBitVecVal words (for a
  // "bit [255:0]" argument). Allocate 256 bits (= 32 bytes) as
  // 32/sizeof(svBitVecVal) words on the stack.
  svBitVecVal buf[256 / 8 / sizeof(svBitVecVal)];

  // The implementation of otbn_rf_peek() is only available if DesignScope != ""
  // (the function is implemented in SystemVerilog, and imported through DPI).
  // We should not reach the code here if that's the case.
  assert(otbn_rf_peek);

  for (int i = 0; i < 32; ++i) {
    if (!otbn_rf_peek(i, buf)) {
      std::ostringstream oss;
      oss << "Failed to peek into RTL to get value of register " << i
          << " at scope `" << reg_scope << "'.";
      throw std::runtime_error(oss.str());
    }
    memcpy(&ret[i], buf, sizeof(T));
  }

  return ret;
}

template <typename T>
static std::vector<T> get_stack(const std::string &stack_scope) {
  std::vector<T> ret;
  static_assert(sizeof(T) <= 256 / 8, "Can only copy 256 bits");

  SVScoped scoped(stack_scope);

  // otbn_stack_element_peek passes data as a packed array of svBitVecVal words
  // (for a "bit [255:0]" argument). Allocate 256 bits (= 32 bytes) as
  // 32/sizeof(svBitVecVal) words on the stack.
  svBitVecVal buf[256 / 8 / sizeof(svBitVecVal)];

  // The implementation of otbn_stack_element_peek() is only available if
  // DesignScope != "" (the function is implemented in SystemVerilog, and
  // imported through DPI).  We should not reach the code here if that's the
  // case.
  assert(otbn_stack_element_peek);

  int i = 0;

  while (1) {
    int peek_result = otbn_stack_element_peek(i, buf);

    if (peek_result == 2) {
      std::ostringstream oss;
      oss << "Failed to peek into RTL to get value of stack element " << i
          << " at scope `" << stack_scope << "'.";
      throw std::runtime_error(oss.str());
    } else if (peek_result == 1) {
      // No more elements on stack
      break;
    }

    T stack_element;
    memcpy(&stack_element, buf, sizeof(T));
    ret.push_back(stack_element);

    ++i;
  }

  return ret;
}

// Compare contents of ISS registers with those from the design. Prints
// messages to stderr on failure or mismatch. Returns true on success; false on
// mismatch. Throws a std::runtime_error on failure.
static bool check_regs(ISSWrapper &iss, const std::string &design_scope) {
  std::string base_scope =
      design_scope +
      ".u_otbn_rf_base.gen_rf_base_ff.u_otbn_rf_base_inner.u_snooper";
  std::string wide_scope =
      design_scope + ".gen_rf_bignum_ff.u_otbn_rf_bignum.u_snooper";

  auto rtl_gprs = get_rtl_regs<uint32_t>(base_scope);
  auto rtl_wdrs = get_rtl_regs<ISSWrapper::u256_t>(wide_scope);

  std::array<uint32_t, 32> iss_gprs;
  std::array<ISSWrapper::u256_t, 32> iss_wdrs;
  iss.get_regs(&iss_gprs, &iss_wdrs);

  bool good = true;

  for (int i = 0; i < 32; ++i) {
    // Register index 1 is call stack, which is checked seperately
    if (i == 1)
      continue;

    if (rtl_gprs[i] != iss_gprs[i]) {
      std::ios old_state(nullptr);
      old_state.copyfmt(std::cerr);
      std::cerr << std::setfill('0') << "RTL computed x" << i << " as 0x"
                << std::hex << rtl_gprs[i] << ", but ISS got 0x" << iss_gprs[i]
                << ".\n";
      std::cerr.copyfmt(old_state);
      good = false;
    }
  }
  for (int i = 0; i < 32; ++i) {
    if (0 != memcmp(rtl_wdrs[i].words, iss_wdrs[i].words,
                    sizeof(rtl_wdrs[i].words))) {
      std::ios old_state(nullptr);
      old_state.copyfmt(std::cerr);
      std::cerr << "RTL computed w" << i << " as 0x" << std::hex
                << std::setfill('0');
      for (int j = 0; j < 8; ++j) {
        if (j)
          std::cerr << "_";
        std::cerr << std::setw(8) << rtl_wdrs[i].words[7 - j];
      }
      std::cerr << ", but ISS got 0x";
      for (int j = 0; j < 8; ++j) {
        if (j)
          std::cerr << "_";
        std::cerr << std::setw(8) << iss_wdrs[i].words[7 - j];
      }
      std::cerr << ".\n";
      std::cerr.copyfmt(old_state);
      good = false;
    }
  }

  return good;
}

// Compare contents of ISS call stack with those from the design. Prints
// messages to stderr on failure or mismatch. Returns true on success; false on
// mismatch.  Throws a std::runtime_error on failure.
static bool check_call_stack(ISSWrapper &iss, const std::string &design_scope) {
  std::string call_stack_snooper_scope =
      design_scope + ".u_otbn_rf_base.u_call_stack_snooper";

  auto rtl_call_stack = get_stack<uint32_t>(call_stack_snooper_scope);

  auto iss_call_stack = iss.get_call_stack();

  bool good = true;

  if (iss_call_stack.size() != rtl_call_stack.size()) {
    std::cerr << "Call stack size mismatch, RTL call stack has "
              << rtl_call_stack.size() << " elements and ISS call stack has "
              << iss_call_stack.size() << " elements\n";

    good = false;
  }

  // Iterate through both call stacks where both have elements
  std::size_t call_stack_size =
      std::min(rtl_call_stack.size(), iss_call_stack.size());
  for (std::size_t i = 0; i < call_stack_size; ++i) {
    if (iss_call_stack[i] != rtl_call_stack[i]) {
      std::ios old_state(nullptr);
      old_state.copyfmt(std::cerr);
      std::cerr << std::setfill('0') << "RTL call stack element " << i
                << " is 0x" << std::hex << rtl_call_stack[i]
                << ", but ISS has 0x" << iss_call_stack[i] << ".\n";
      std::cerr.copyfmt(old_state);
      good = false;
    }
  }

  return good;
}

// Check model against RTL when a run has finished. Prints messages to stderr
// on failure or mismatch. Returns 1 for a match, 0 for a mismatch, -1 for some
// other failure.
int check_model(OtbnModel *model, const char *dmem_scope, unsigned dmem_words,
                const char *design_scope) {
  assert(model);
  assert(dmem_words >= 0);
  assert(design_scope);

  if (!model->iss) {
    std::cerr << "Cannot check OTBN model: ISS has not started.\n";
    return -1;
  }
  ISSWrapper &iss = *model->iss;

  bool good = true;

  good &= OtbnTraceChecker::get().Finish();

  try {
    good &= check_dmem(iss, dmem_scope, dmem_words);
  } catch (const std::exception &err) {
    std::cerr << "Failed to check DMEM: " << err.what() << "\n";
    return -1;
  }

  try {
    good &= check_regs(iss, design_scope);
  } catch (const std::exception &err) {
    std::cerr << "Failed to check registers: " << err.what() << "\n";
    return -1;
  }

  try {
    good &= check_call_stack(iss, design_scope);
  } catch (const std::exception &err) {
    std::cerr << "Failed to check call stack: " << err.what() << "\n";
    return -1;
  }

  return good ? 1 : 0;
}

// Pack a uint32_t-based error code (as generated by step_model) into a
// SystemVerilog bit vector that represents a "bit [31:0]" (as in the SV
// prototype of otbn_model_step)
static void set_err_code(svBitVecVal *dst, uint32_t src) {
  for (int i = 0; i < 32; ++i) {
    svBit bit = (src >> i) & 1;
    svPutBitselBit(dst, i, bit);
  }
}

extern "C" unsigned otbn_model_step(OtbnModel *model, const char *imem_scope,
                                    unsigned imem_words, const char *dmem_scope,
                                    unsigned dmem_words,
                                    const char *design_scope, svLogic start_i,
                                    unsigned start_addr, unsigned status,
                                    svBitVecVal *err_code /* bit [31:0] */) {
  assert(model && imem_scope && dmem_scope && design_scope && err_code);

  // Run model checks if needed. This usually happens just after an operation
  // has finished.
  bool check_rtl = (design_scope[0] != '\0');
  if (check_rtl && (status & CHECK_DUE_BIT)) {
    switch (check_model(model, dmem_scope, dmem_words, design_scope)) {
      case 1:
        // Match (success)
        break;

      case 0:
        // Mismatch
        status |= FAILED_CMP_BIT;
        break;

      default:
        // Something went wrong
        return (status & ~RUNNING_BIT) | FAILED_STEP_BIT;
    }
    status &= ~CHECK_DUE_BIT;
  }

  // Start the model if requested
  if (start_i) {
    switch (start_model(model, imem_scope, imem_words, dmem_scope, dmem_words,
                        start_addr)) {
      case 0:
        // All good
        status |= RUNNING_BIT;
        break;

      default:
        // Something went wrong.
        return (status & ~RUNNING_BIT) | FAILED_STEP_BIT;
    }
  }

  // If the model isn't running, there's nothing more to do.
  if (!(status & RUNNING_BIT))
    return status;

  // Step the model once
  uint32_t int_err_code;
  switch (step_model(model, check_rtl, &int_err_code)) {
    case 0:
      // Still running: no change
      break;

    case 1:
      // Finished
      status = (status & ~RUNNING_BIT) | CHECK_DUE_BIT;
      set_err_code(err_code, int_err_code);
      break;

    default:
      // Something went wrong
      return (status & ~RUNNING_BIT) | FAILED_STEP_BIT;
  }

  // If we're still running, there's nothing more to do.
  if (status & RUNNING_BIT)
    return status;

  // If we've just stopped running and there's no RTL, load the contents of
  // DMEM back from the ISS
  if (!check_rtl) {
    switch (load_dmem(model, dmem_scope, dmem_words)) {
      case 0:
        // Success
        break;

      default:
        // Failed to load DMEM
        return (status & ~RUNNING_BIT) | FAILED_STEP_BIT;
    }
  }

  return status;
}
