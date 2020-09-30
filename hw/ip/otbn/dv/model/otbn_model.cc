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
#include "sv_scoped.h"

extern "C" int simutil_verilator_get_mem(int index, svBitVecVal *val);
extern "C" int simutil_verilator_set_mem(int index, const svBitVecVal *val);
extern "C" int otbn_rf_peek(int index, svBitVecVal *val);

// Use simutil_verilator_get_mem to read data one word at a time from the given
// scope and collect the results up in a vector of uint8_t values.
static std::vector<uint8_t> get_sim_memory(const char *scope, size_t num_words,
                                           size_t word_size) {
  SVScoped scoped(scope);

  // simutil_verilator_get_mem passes data as a packed array of svBitVecVal
  // words. It only works for memories of size at most 256 bits, so we can just
  // allocate 256/8 = 32 bytes as 32/sizeof(svBitVecVal) words on the stack.
  assert(word_size <= 256 / 8);
  svBitVecVal buf[256 / 8 / sizeof(svBitVecVal)];

  std::vector<uint8_t> ret;

  for (size_t w = 0; w < num_words; w++) {
    if (!simutil_verilator_get_mem(w, buf)) {
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

// Use simutil_verilator_get_mem to write data one word at a time to the given
// scope.
static void set_sim_memory(const std::vector<uint8_t> &data, const char *scope,
                           size_t num_words, size_t word_size) {
  SVScoped scoped(scope);

  assert(num_words * word_size == data.size());

  // See get_sim_memory for why this array is sized like this.
  assert(word_size <= 256 / 8);
  svBitVecVal buf[256 / 8 / sizeof(svBitVecVal)];

  for (size_t w = 0; w < num_words; w++) {
    const uint8_t *p = &data[w * word_size];
    memcpy(buf, p, word_size);

    if (!simutil_verilator_set_mem(w, buf)) {
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

extern "C" ISSWrapper *otbn_model_init() {
  try {
    return new ISSWrapper();
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when constructing ISS wrapper: " << err.what() << "\n";
    return nullptr;
  }
}

extern "C" void otbn_model_destroy(ISSWrapper *model) { delete model; }

// Start a new run with the model, writing IMEM/DMEM and jumping to the given
// start address. Returns 0 on success; -1 on failure.
extern "C" int otbn_model_start(ISSWrapper *model, const char *imem_scope,
                                int imem_words, const char *dmem_scope,
                                int dmem_words, int start_addr) {
  assert(model);
  assert(imem_words >= 0);
  assert(dmem_words >= 0);
  assert(start_addr >= 0 && start_addr < (imem_words * 4));

  std::string ifname(model->make_tmp_path("imem"));
  std::string dfname(model->make_tmp_path("dmem"));

  try {
    dump_memory_to_file(dfname, dmem_scope, dmem_words, 32);
    dump_memory_to_file(ifname, imem_scope, imem_words, 4);
  } catch (const std::exception &err) {
    std::cerr << "Error when dumping memory contents: " << err.what() << "\n";
    return -1;
  }

  try {
    model->load_d(dfname);
    model->load_i(ifname);
    model->start(start_addr);
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when starting ISS: " << err.what() << "\n";
    return -1;
  }

  return 0;
}

// Step once in the model. Returns 1 if the model has finished, 0 if not and -1
// on failure.
extern "C" int otbn_model_step(ISSWrapper *model) {
  assert(model);
  try {
    return model->step() ? 1 : 0;
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when stepping ISS: " << err.what() << "\n";
    return -1;
  }
}

// Grab contents of dmem from the model and load it back into the RTL. Returns
// 0 on success; -1 on failure.
extern "C" int otbn_model_load_dmem(ISSWrapper *model, const char *dmem_scope,
                                    int dmem_words) {
  assert(model);
  std::string dfname(model->make_tmp_path("dmem_out"));
  try {
    model->dump_d(dfname);
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
static bool otbn_model_check_dmem(ISSWrapper *model, const char *dmem_scope,
                                  int dmem_words) {
  assert(model);
  assert(dmem_words >= 0);

  size_t dmem_bytes = dmem_words * 32;
  std::string dfname(model->make_tmp_path("dmem_out"));

  model->dump_d(dfname);
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

// Compare contents of ISS registers with those from the design. Prints
// messages to stderr on failure or mismatch. Returns true on success; false on
// mismatch. Throws a std::runtime_error on failure.
static bool otbn_model_check_regs(ISSWrapper *model,
                                  const std::string &design_scope) {
  assert(model);

  std::string base_scope =
      design_scope + ".gen_rf_base_ff.u_otbn_rf_base.u_snooper";
  std::string wide_scope =
      design_scope + ".gen_rf_bignum_ff.u_otbn_rf_bignum.u_snooper";

  auto rtl_gprs = get_rtl_regs<uint32_t>(base_scope);
  auto rtl_wdrs = get_rtl_regs<ISSWrapper::u256_t>(wide_scope);

  std::array<uint32_t, 32> iss_gprs;
  std::array<ISSWrapper::u256_t, 32> iss_wdrs;
  model->get_regs(&iss_gprs, &iss_wdrs);

  bool good = true;

  for (int i = 0; i < 32; ++i) {
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

// Check model against RTL when a run has finished. Prints messages to
// stderr on failure or mismatch. Returns 1 for a match, 0 for a
// mismatch, -1 for some other failure.
extern "C" int otbn_model_check(ISSWrapper *model, const char *dmem_scope,
                                int dmem_words, const char *design_scope) {
  assert(model);
  assert(dmem_words >= 0);
  assert(design_scope);

  bool good = true;
  try {
    good &= otbn_model_check_dmem(model, dmem_scope, dmem_words);
  } catch (const std::exception &err) {
    std::cerr << "Failed to check DMEM: " << err.what() << "\n";
    return -1;
  }

  try {
    good &= otbn_model_check_regs(model, design_scope);
  } catch (const std::exception &err) {
    std::cerr << "Failed to check registers: " << err.what() << "\n";
    return -1;
  }

  return good ? 1 : 0;
}
