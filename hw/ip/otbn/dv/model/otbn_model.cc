// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cassert>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <svdpi.h>

#include "iss_wrapper.h"

// Candidate for hw/dv/verilator/cpp
/**
 * Guard class for SV Scope
 *
 * This guard ensures that all functions in the context where it is instantiated
 * are executed in an SVScope. It will restore the previous scope at destruction
 * and thereby make sure that the previous scope will be restored for all paths
 * that exit the scope.
 */
class SVScoped {
 private:
  svScope prev_scope_ = 0;

 public:
  SVScoped(std::string scopeName) : SVScoped(scopeName.c_str()) {}
  SVScoped(const char *scopeName) : SVScoped(svGetScopeFromName(scopeName)) {}

  SVScoped(svScope scope) { prev_scope_ = svSetScope(scope); }
  ~SVScoped() { svSetScope(prev_scope_); }
};

extern "C" int simutil_verilator_get_mem(int index, const svBitVecVal *val);
extern "C" int simutil_verilator_set_mem(int index, const svBitVecVal *val);

// Use simutil_verilator_get_mem to read data one word at a time from the given
// scope, writing it to a file at path. Each word is word_size bytes long.
//
// Raises a runtime_error on failure.
static void dump_memory(const std::string &path, const char *scope,
                        size_t num_words, size_t word_size) {
  std::filebuf fb;
  if (!fb.open(path.c_str(), std::ios::out | std::ios::binary)) {
    std::ostringstream oss;
    oss << "Cannot open the file '" << path << "'.";
    throw std::runtime_error(oss.str());
  }

  SVScoped scoped(scope);

  // simutil_verilator_get_mem passes data as a packed array of svBitVecVal
  // words. It only works for memories of size at most 256 bits, so we can just
  // allocate 256/8 = 32 bytes as 32/sizeof(svBitVecVal) words on the stack.
  assert(word_size <= 256 / 8);
  svBitVecVal buf[256 / 8 / sizeof(svBitVecVal)];

  for (size_t w = 0; w < num_words; w++) {
    if (!simutil_verilator_get_mem(w, buf)) {
      std::ostringstream oss;
      oss << "Cannot get memory at word " << w << " from scope " << scope
          << ".\n";
      throw std::runtime_error(oss.str());
    }

    // Write out the first word_size bytes of data
    std::streamsize chars_out =
        fb.sputn(reinterpret_cast<const char *>(buf), word_size);

    if (chars_out != word_size) {
      std::ostringstream oss;
      oss << "Cannot write word " << w << " to '" << path << "'.\n";
      throw std::runtime_error(oss.str());
    }
  }
}

// Read data from the given file and then use simutil_verilator_set_mem to
// write it into the simulation one word at a time. Each word is word_size
// bytes long.
//
// Raises a runtime_error on failure.
static void load_memory(const std::string &path, const char *scope,
                        size_t num_words, size_t word_size) {
  std::filebuf fb;
  if (!fb.open(path.c_str(), std::ios::in | std::ios::binary)) {
    std::ostringstream oss;
    oss << "Cannot open the file '" << path << "'.";
    throw std::runtime_error(oss.str());
  }

  SVScoped scoped(scope);

  // See dump_memory, above, for why this array is sized like this.
  assert(word_size <= 256 / 8);
  svBitVecVal buf[256 / 8 / sizeof(svBitVecVal)];

  for (size_t w = 0; w < num_words; w++) {
    std::streamsize chars_in =
        fb.sgetn(reinterpret_cast<char *>(buf), word_size);

    if (chars_in != word_size) {
      std::ostringstream oss;
      oss << "Cannot read word " << w << " from '" << path << "'.\n";
      throw std::runtime_error(oss.str());
    }

    if (!simutil_verilator_set_mem(w, buf)) {
      std::ostringstream oss;
      oss << "Cannot set memory at word " << w << " for scope " << scope
          << ".\n";
      throw std::runtime_error(oss.str());
    }
  }
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

extern "C" int otbn_model_run(ISSWrapper *model, const char *imem_scope,
                              int imem_words, const char *dmem_scope,
                              int dmem_words, int start_addr) {
  assert(model);
  assert(imem_words >= 0);
  assert(dmem_words >= 0);
  assert(start_addr >= 0 && start_addr < (imem_words * 4));

  std::string ifname(model->make_tmp_path("imem"));
  std::string dfname(model->make_tmp_path("dmem"));

  try {
    dump_memory(dfname, dmem_scope, dmem_words, 32);
    dump_memory(ifname, imem_scope, imem_words, 4);
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when dumping memory contents: " << err.what() << "\n";
    return 0;
  }

  try {
    model->load_d(dfname.c_str());
    model->load_i(ifname.c_str());
    model->start(start_addr);
    unsigned cycles = model->run();
    model->dump_d(dfname.c_str());

    load_memory(dfname, dmem_scope, dmem_words, 32);
    return cycles;

  } catch (const std::runtime_error &err) {
    std::cerr << "Error when running ISS: " << err.what() << "\n";
    return 0;
  }
}
