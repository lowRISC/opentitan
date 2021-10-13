// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "otbn_model.h"

#include <algorithm>
#include <cassert>
#include <cstring>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>

#include "iss_wrapper.h"
#include "otbn_model_dpi.h"
#include "otbn_trace_checker.h"
#include "sv_scoped.h"
#include "sv_utils.h"

// Read (the start of) the contents of a file at path as a vector of bytes.
// Expects num_bytes bytes of data. On failure, throws a std::runtime_error.
static std::vector<uint8_t> read_vector_from_file(const std::string &path,
                                                  size_t num_bytes);

// Write a vector of bytes to a new file at path. On failure, throws a
// std::runtime_error.
static void write_vector_to_file(const std::string &path,
                                 const std::vector<uint8_t> &data);

extern "C" {
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

static bool is_xz(svLogic l) { return l == sv_x || l == sv_z; }

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

    // otbn_stack_element_peek is defined in otbn_stack_snooper_if.sv. Possible
    // return values are: 0 on success, if we've returned an element. 1 if the
    // stack doesn't have an element at index i. 2 if something terrible has
    // gone wrong (such as a completely bogus index).
    assert(peek_result <= 2);

    if (peek_result == 2) {
      std::ostringstream oss;
      oss << "Failed to peek into RTL to get value of stack element " << i
          << " at scope `" << stack_scope << "'.";
      throw std::runtime_error(oss.str());
    }

    if (peek_result == 1) {
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

OtbnModel::OtbnModel(const std::string &mem_scope,
                     const std::string &design_scope, unsigned imem_size_words,
                     unsigned dmem_size_words)
    : mem_util_(mem_scope),
      design_scope_(design_scope),
      imem_size_words_(imem_size_words),
      dmem_size_words_(dmem_size_words) {}

OtbnModel::~OtbnModel() {}

int OtbnModel::take_loop_warps(const OtbnMemUtil &memutil) {
  ISSWrapper *iss = ensure_wrapper();
  if (!iss)
    return -1;

  try {
    iss->clear_loop_warps();
  } catch (std::runtime_error &err) {
    std::cerr << "Error when clearing loop warps: " << err.what() << "\n";
    return -1;
  }

  for (auto &pr : memutil.GetLoopWarps()) {
    auto &key = pr.first;
    uint32_t addr = key.first;
    uint32_t from_cnt = key.second;
    uint32_t to_cnt = pr.second;

    try {
      iss->add_loop_warp(addr, from_cnt, to_cnt);
    } catch (const std::runtime_error &err) {
      std::cerr << "Error when adding loop warp: " << err.what() << "\n";
      return -1;
    }
  }

  return 0;
}

int OtbnModel::start() {
  const MemArea &imem = mem_util_.GetMemArea(true);

  ISSWrapper *iss = ensure_wrapper();
  if (!iss)
    return -1;

  std::string dfname(iss->make_tmp_path("dmem"));
  std::string ifname(iss->make_tmp_path("imem"));

  try {
    write_vector_to_file(dfname, get_sim_memory(false));
    write_vector_to_file(ifname, get_sim_memory(true));
  } catch (const std::exception &err) {
    std::cerr << "Error when dumping memory contents: " << err.what() << "\n";
    return -1;
  }

  try {
    iss->load_d(dfname);
    iss->load_i(ifname);
    iss->start();
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when starting ISS: " << err.what() << "\n";
    return -1;
  }

  return 0;
}

void OtbnModel::edn_step(svLogicVecVal *edn_rnd_data /* logic [31:0] */) {
  ISSWrapper *iss = ensure_wrapper();

  iss->edn_step(edn_rnd_data->aval);
}

void OtbnModel::edn_rnd_cdc_done() {
  ISSWrapper *iss = ensure_wrapper();
  iss->edn_rnd_cdc_done();
}

int OtbnModel::step(svLogic edn_urnd_data_valid,
                    svBitVecVal *status /* bit [7:0] */,
                    svBitVecVal *insn_cnt /* bit [31:0] */,
                    svBitVecVal *err_bits /* bit [31:0] */,
                    svBitVecVal *stop_pc /* bit [31:0] */) {
  assert(insn_cnt && err_bits && stop_pc);

  ISSWrapper *iss = ensure_wrapper();
  if (!iss)
    return -1;

  assert(!is_xz(edn_urnd_data_valid));

  try {
    if (edn_urnd_data_valid) {
      iss->edn_urnd_reseed_complete();
    }

    switch (iss->step(has_rtl())) {
      case -1:
        // Something went wrong, such as a trace mismatch. We've already printed
        // a message to stderr so can just return -1.
        return -1;

      case 1:
        // The simulation has stopped. Fill in status, insn_cnt, err_bits and
        // stop_pc. Note that status should never have anything in its top 24
        // bits.
        if (iss->get_mirrored().status >> 8) {
          throw std::runtime_error("STATUS register had non-empty top bits.");
        }
        set_sv_u8(status, iss->get_mirrored().status);
        set_sv_u32(insn_cnt, iss->get_mirrored().insn_cnt);
        set_sv_u32(err_bits, iss->get_mirrored().err_bits);
        set_sv_u32(stop_pc, iss->get_mirrored().stop_pc);
        return 1;

      case 0:
        // The simulation is still running. Update status and insn_cnt.
        if (iss->get_mirrored().status >> 8) {
          throw std::runtime_error("STATUS register had non-empty top bits.");
        }
        set_sv_u8(status, iss->get_mirrored().status);
        set_sv_u32(insn_cnt, iss->get_mirrored().insn_cnt);
        return 0;

      default:
        // This shouldn't happen
        assert(0);
    }
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when stepping ISS: " << err.what() << "\n";
    return -1;
  }
}

int OtbnModel::check() const {
  if (!has_rtl())
    return 1;

  ISSWrapper *iss = iss_.get();
  if (!iss) {
    std::cerr << "Cannot check OTBN model: ISS has not started.\n";
    return -1;
  }

  bool good = true;

  good &= OtbnTraceChecker::get().Finish();

  try {
    good &= check_dmem(*iss);
  } catch (const std::exception &err) {
    std::cerr << "Failed to check DMEM: " << err.what() << "\n";
    return -1;
  }

  try {
    good &= check_regs(*iss);
  } catch (const std::exception &err) {
    std::cerr << "Failed to check registers: " << err.what() << "\n";
    return -1;
  }

  try {
    good &= check_call_stack(*iss);
  } catch (const std::exception &err) {
    std::cerr << "Failed to check call stack: " << err.what() << "\n";
    return -1;
  }

  return good ? 1 : 0;
}

int OtbnModel::load_dmem() {
  ISSWrapper *iss = iss_.get();
  if (!iss) {
    std::cerr << "Cannot load dmem from OTBN model: ISS has not started.\n";
    return -1;
  }

  const MemArea &dmem = mem_util_.GetMemArea(false);

  std::string dfname(iss->make_tmp_path("dmem_out"));
  try {
    iss->dump_d(dfname);
    set_sim_memory(false, read_vector_from_file(dfname, dmem.GetSizeBytes()));
  } catch (const std::exception &err) {
    std::cerr << "Error when loading dmem from ISS: " << err.what() << "\n";
    return -1;
  }
  return 0;
}

void OtbnModel::reset() {
  ISSWrapper *iss = iss_.get();
  if (iss)
    iss->reset(has_rtl());
}

ISSWrapper *OtbnModel::ensure_wrapper() {
  if (!iss_) {
    try {
      iss_.reset(new ISSWrapper());
    } catch (const std::runtime_error &err) {
      std::cerr << "Error when constructing ISS wrapper: " << err.what()
                << "\n";
      return nullptr;
    }
  }
  assert(iss_);
  return iss_.get();
}

std::vector<uint8_t> OtbnModel::get_sim_memory(bool is_imem) const {
  const MemArea &mem_area = mem_util_.GetMemArea(is_imem);
  return mem_area.Read(0, mem_area.GetSizeWords());
}

void OtbnModel::set_sim_memory(bool is_imem, const std::vector<uint8_t> &data) {
  mem_util_.GetMemArea(is_imem).Write(0, data);
}

bool OtbnModel::check_dmem(ISSWrapper &iss) const {
  const MemArea &dmem = mem_util_.GetMemArea(false);
  uint32_t dmem_bytes = dmem.GetSizeBytes();

  std::string dfname(iss.make_tmp_path("dmem_out"));

  iss.dump_d(dfname);
  std::vector<uint8_t> iss_data = read_vector_from_file(dfname, dmem_bytes);
  assert(iss_data.size() == dmem_bytes);

  std::vector<uint8_t> rtl_data = get_sim_memory(false);
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

bool OtbnModel::check_regs(ISSWrapper &iss) const {
  assert(design_scope_.size());

  std::string base_scope =
      design_scope_ +
      ".u_otbn_rf_base.gen_rf_base_ff.u_otbn_rf_base_inner.u_snooper";
  std::string wide_scope =
      design_scope_ +
      ".u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.u_snooper";

  auto rtl_gprs = get_rtl_regs<uint32_t>(base_scope);
  auto rtl_wdrs = get_rtl_regs<ISSWrapper::u256_t>(wide_scope);

  std::array<uint32_t, 32> iss_gprs;
  std::array<ISSWrapper::u256_t, 32> iss_wdrs;
  iss.get_regs(&iss_gprs, &iss_wdrs);

  bool good = true;

  for (int i = 0; i < 32; ++i) {
    // Register index 1 is call stack, which is checked separately
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

bool OtbnModel::check_call_stack(ISSWrapper &iss) const {
  assert(design_scope_.size());

  std::string call_stack_snooper_scope =
      design_scope_ + ".u_otbn_rf_base.u_call_stack_snooper";

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

OtbnModel *otbn_model_init(const char *mem_scope, const char *design_scope,
                           unsigned imem_words, unsigned dmem_words) {
  assert(mem_scope && design_scope);
  return new OtbnModel(mem_scope, design_scope, imem_words, dmem_words);
}

void otbn_model_destroy(OtbnModel *model) { delete model; }

void edn_model_step(OtbnModel *model,
                    svLogicVecVal *edn_rnd_data /* logic [31:0] */) {
  model->edn_step(edn_rnd_data);
}

void edn_model_rnd_cdc_done(OtbnModel *model) { model->edn_rnd_cdc_done(); }

unsigned otbn_model_step(OtbnModel *model, svLogic start, unsigned model_state,
                         svLogic edn_urnd_data_valid,
                         svBitVecVal *status /* bit [7:0] */,
                         svBitVecVal *insn_cnt /* bit [31:0] */,
                         svBitVecVal *err_bits /* bit [31:0] */,
                         svBitVecVal *stop_pc /* bit [31:0] */) {
  assert(model && status && insn_cnt && err_bits && stop_pc);

  // Run model checks if needed. This usually happens just after an operation
  // has finished.
  if (model->has_rtl() && (model_state & CHECK_DUE_BIT)) {
    switch (model->check()) {
      case 1:
        // Match (success)
        break;

      case 0:
        // Mismatch
        model_state |= FAILED_CMP_BIT;
        break;

      default:
        // Something went wrong
        return (model_state & ~RUNNING_BIT) | FAILED_STEP_BIT;
    }
    model_state &= ~CHECK_DUE_BIT;
  }

  assert(!is_xz(start));

  // Start the model if requested
  if (start) {
    switch (model->start()) {
      case 0:
        // All good
        model_state |= RUNNING_BIT;
        break;

      default:
        // Something went wrong.
        return (model_state & ~RUNNING_BIT) | FAILED_STEP_BIT;
    }
  }

  // If the model isn't running, there's nothing more to do.
  if (!(model_state & RUNNING_BIT))
    return model_state;

  // Step the model once
  switch (
      model->step(edn_urnd_data_valid, status, insn_cnt, err_bits, stop_pc)) {
    case 0:
      // Still running: no change
      break;

    case 1:
      // Finished
      model_state = (model_state & ~RUNNING_BIT) | CHECK_DUE_BIT;
      break;

    default:
      // Something went wrong
      return (model_state & ~RUNNING_BIT) | FAILED_STEP_BIT;
  }

  // If we're still running, there's nothing more to do.
  if (model_state & RUNNING_BIT)
    return model_state;

  // If we've just stopped running and there's no RTL, load the contents of
  // DMEM back from the ISS
  if (!model->has_rtl()) {
    switch (model->load_dmem()) {
      case 0:
        // Success
        break;

      default:
        // Failed to load DMEM
        return (model_state & ~RUNNING_BIT) | FAILED_STEP_BIT;
    }
  }

  return model_state;
}

void otbn_model_reset(OtbnModel *model) {
  assert(model);
  model->reset();
}

void otbn_take_loop_warps(OtbnModel *model, OtbnMemUtil *memutil) {
  assert(model && memutil);
  model->take_loop_warps(*memutil);
}
