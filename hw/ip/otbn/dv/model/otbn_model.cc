// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cassert>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <svdpi.h>
#include <sys/stat.h>

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

// Guard class to safely delete C strings
struct CStrDeleter {
  void operator()(char *p) const { std::free(p); }
};
typedef std::unique_ptr<char, CStrDeleter> c_str_ptr;

extern "C" int simutil_verilator_get_mem(int index, const svBitVecVal *val);
extern "C" int simutil_verilator_set_mem(int index, const svBitVecVal *val);

// Use simutil_verilator_get_mem to read data one word at a time from the given
// scope, writing it to a file at path. Each word is word_size bytes long.
//
// Raises a runtime_error on failure.
static void dump_memory(const char *path, const char *scope, size_t num_words,
                        size_t word_size) {
  std::filebuf fb;
  if (!fb.open(path, std::ios::out | std::ios::binary)) {
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
static void load_memory(const char *path, const char *scope, size_t num_words,
                        size_t word_size) {
  std::filebuf fb;
  if (!fb.open(path, std::ios::in | std::ios::binary)) {
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

// Read a 4-byte little-endian unsigned value from the given file which is
// supposed to represent the number of cycles taken by the simulation and
// return it.
//
// Raises a runtime_error on failure.
static uint32_t load_cycles(const char *path) {
  std::filebuf fb;
  if (!fb.open(path, std::ios::in | std::ios::binary)) {
    std::ostringstream oss;
    oss << "Cannot open the file '" << path << "'.";
    throw std::runtime_error(oss.str());
  }

  char buf[4];
  if (fb.sgetn(buf, 4) != 4) {
    std::ostringstream oss;
    oss << "Failed to read 4 bytes from '" << path << "'.";
    throw std::runtime_error(oss.str());
  }

  // Re-pack the little-endian value we just read.
  uint32_t ret = 0;
  for (int i = 0; i < 4; ++i) {
    ret += (uint32_t)buf[i] << 8 * i;
  }
  return ret;
}

// Find the otbn Python model, based on our executable path, and
// return it. On failure, throw a std::runtime_error with a
// description of what went wrong.
//
// This works by searching upwards from the binary location to find a git
// directory (which is assumed to be the OpenTitan toplevel). It won't work if
// you copy the binary somewhere else: if we need to support that sort of
// thing, we'll have to figure out a "proper" installation procedure.
static std::string find_otbn_model() {
  c_str_ptr self_path(realpath("/proc/self/exe", NULL));
  if (!self_path) {
    std::ostringstream oss;
    oss << "Cannot resolve /proc/self/exe: " << strerror(errno);
    throw std::runtime_error(oss.str());
  }

  // Take a copy of self_path as a std::string and modify it, walking backwards
  // over '/' characters and appending .git each time. After the first
  // iteration, last_pos is the position of the character before the final
  // slash (where the path looks something like "/path/to/check/.git")
  std::string path_buf(self_path.get());

  struct stat git_dir_stat;

  size_t last_pos = std::string::npos;
  for (;;) {
    size_t last_slash = path_buf.find_last_of('/', last_pos);

    // self_path was absolute, so there should always be a '/' at position
    // zero.
    assert(last_slash != std::string::npos);
    if (last_slash == 0) {
      // We've got to the slash at the start of an absolute path (and "/.git"
      // is probably not the path we want!). Give up.
      std::ostringstream oss;
      oss << "Cannot find a git top-level directory containing "
          << self_path.get() << ".\n";
      throw std::runtime_error(oss.str());
    }

    // Replace everything after last_slash with ".git". The first time around,
    // this will turn "/path/to/elf-file" to "/path/to/.git". After that, it
    // will turn "/path/to/check/.git" to "/path/to/.git". Note that last_slash
    // is strictly less than the string length (because it's an element index),
    // so last_slash + 1 won't fall off the end.
    path_buf.replace(last_slash + 1, std::string::npos, ".git");
    last_pos = last_slash - 1;

    // Does path_buf name a directory? If so, we've found the enclosing git
    // directory.
    if (stat(path_buf.c_str(), &git_dir_stat) == 0 &&
        S_ISDIR(git_dir_stat.st_mode)) {
      break;
    }
  }

  // If we get here, path_buf points at a .git directory. Resolve from there to
  // the expected model name, then use realpath to canonicalise the path. If it
  // fails, there was no script there.
  path_buf += "/../hw/ip/otbn/dv/otbnsim/otbnsim.py";
  char *model_path = realpath(path_buf.c_str(), NULL);
  if (!model_path) {
    std::ostringstream oss;
    oss << "Cannot find otbnsim.py, at '" << path_buf
        << "' (guessed by searching upwards from '" << self_path.get()
        << "').\n";
    throw std::runtime_error(oss.str());
  }

  return std::string(model_path);
}

extern "C" int run_model(const char *imem_scope, int imem_words,
                         const char *dmem_scope, int dmem_words,
                         int start_addr) {
  assert(imem_words >= 0);
  assert(dmem_words >= 0);
  assert(start_addr >= 0 && start_addr < (imem_words * 4));

  char dir[] = "/tmp/otbn_XXXXXX";
  char ifname[] = "/tmp/otbn_XXXXXX/imem";
  char dfname[] = "/tmp/otbn_XXXXXX/dmem";
  char cfname[] = "/tmp/otbn_XXXXXX/cycles";
  char tfname[] = "/tmp/otbn_XXXXXX/trace";

  if (mkdtemp(dir) == nullptr) {
    std::cerr << "Cannot create temporary directory" << std::endl;
    return 0;
  }

  std::memcpy(ifname, dir, strlen(dir));
  std::memcpy(dfname, dir, strlen(dir));
  std::memcpy(cfname, dir, strlen(dir));
  std::memcpy(tfname, dir, strlen(dir));

  try {
    dump_memory(dfname, dmem_scope, dmem_words, 32);
    dump_memory(ifname, imem_scope, imem_words, 4);
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when dumping memory contents: " << err.what() << "\n";
    return 0;
  }

  std::string model_path;
  try {
    model_path = find_otbn_model();
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when searching for OTBN model: " << err.what() << "\n";
    return 0;
  }

  std::ostringstream cmd;
  cmd << model_path << " " << imem_words << " " << ifname << " " << dmem_words
      << " " << dfname << " " << cfname << " " << tfname << " " << start_addr;

  if (std::system(cmd.str().c_str()) != 0) {
    std::cerr << "Failed to execute model (cmd was: '" << cmd.str() << "').\n";
    return 0;
  }

  try {
    load_memory(dfname, dmem_scope, dmem_words, 32);
    return load_cycles(cfname);
  } catch (const std::runtime_error &err) {
    std::cerr << "Error when loading sim results: " << err.what() << "\n";
    return 0;
  }
}
