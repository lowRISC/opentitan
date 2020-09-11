// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cassert>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <ftw.h>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <svdpi.h>
#include <sys/stat.h>

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

// Guard class to create (and possibly delete) temporary directories.
struct TmpDir {
  std::string path;

  ~TmpDir() { cleanup(); }

  // Construct a temporary directory. Throw a runtime_error if something goes
  // wrong.
  void make() {
    // Clean up anything we had already.
    cleanup();
    path = TmpDir::make_tmp_dir();
  }

 private:
  // A wrapper around mkdtemp that respects TMPDIR
  static std::string make_tmp_dir() {
    const char *tmpdir = getenv("TMPDIR");
    if (!tmpdir)
      tmpdir = "/tmp";

    std::string tmp_template(tmpdir);
    tmp_template += "/otbn_XXXXXX";

    if (!mkdtemp(&tmp_template.at(0))) {
      std::ostringstream oss;
      oss << ("Cannot create temporary directory for OTBN simulation "
              "with template ")
          << tmp_template << ": " << strerror(errno);
      throw std::runtime_error(oss.str());
    }

    // The backing string for tmp_template will have been populated by mkdtemp.
    return tmp_template;
  }

  // Return true if the OTBN_MODEL_KEEP_TMP environment variable is set to 1.
  static bool should_keep_tmp() {
    const char *keep_str = getenv("OTBN_MODEL_KEEP_TMP");
    if (!keep_str)
      return false;
    return (strcmp(keep_str, "1") == 0) ? true : false;
  }

  // Called by nftw when we're deleting the temporary directory
  static int ftw_callback(const char *fpath, const struct stat *sb,
                          int typeflag, struct FTW *ftwbuf) {
    // The libc remove() function calls unlink or rmdir as necessary. Ignore
    // any failures: we'll check that we managed to delete the directory when
    // nftw finishes.
    remove(fpath);

    // Tell nftw to keep going
    return 0;
  }

  // Recursively delete the temporary directory
  void cleanup() {
    if (path.empty())
      return;

    if (TmpDir::should_keep_tmp()) {
      std::cerr << "Keeping temporary directory at " << path
                << " because OTBN_MODEL_KEEP_TMP=1.\n";
      return;
    }

    // We're not supposed to keep the directory. Try to delete it and its
    // contents. Ignore any failures: we'll just check whether it's gone
    // afterwards.
    nftw(path.c_str(), TmpDir::ftw_callback, 4, FTW_DEPTH | FTW_PHYS);

    // Is there still anything at path? If so, we failed. Print something to
    // stderr to tell the user what's going on.
    struct stat statbuf;
    if (stat(path.c_str(), &statbuf) == 0) {
      std::cerr << "ERROR: Failed to delete OTBN temporary directory at "
                << path << ".\n";
    }
  }
};

extern "C" int run_model(const char *imem_scope, int imem_words,
                         const char *dmem_scope, int dmem_words,
                         int start_addr) {
  assert(imem_words >= 0);
  assert(dmem_words >= 0);
  assert(start_addr >= 0 && start_addr < (imem_words * 4));

  std::unique_ptr<ISSWrapper> wrapper;
  try {
    wrapper.reset(new ISSWrapper());
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when constructing ISS wrapper: " << err.what() << "\n";
    return 0;
  }

  TmpDir tmpdir;
  try {
    tmpdir.make();
  } catch (const std::runtime_error &err) {
    std::cerr << err.what() << "\n";
    return 0;
  }

  std::string ifname(tmpdir.path + "/imem");
  std::string dfname(tmpdir.path + "/dmem");
  std::string tfname(tmpdir.path + "/trace");

  try {
    dump_memory(dfname, dmem_scope, dmem_words, 32);
    dump_memory(ifname, imem_scope, imem_words, 4);
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when dumping memory contents: " << err.what() << "\n";
    return 0;
  }

  try {
    wrapper->load_d(dfname.c_str());
    wrapper->load_i(ifname.c_str());
    wrapper->start(start_addr);
    unsigned cycles = wrapper->run();
    wrapper->dump_d(dfname.c_str());

    load_memory(dfname, dmem_scope, dmem_words, 32);
    return cycles;

  } catch (const std::runtime_error &err) {
    std::cerr << "Error when running ISS: " << err.what() << "\n";
    return 0;
  }
}
