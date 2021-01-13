// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "iss_wrapper.h"

#include <cassert>
#include <cstring>
#include <fcntl.h>
#include <ftw.h>
#include <iostream>
#include <memory>
#include <regex>
#include <signal.h>
#include <sstream>
#include <sys/stat.h>
#include <sys/wait.h>

#include "otbn_trace_checker.h"

// Guard class to safely delete C strings
namespace {
struct CStrDeleter {
  void operator()(char *p) const { std::free(p); }
};
}  // namespace
typedef std::unique_ptr<char, CStrDeleter> c_str_ptr;

// Guard class to create (and possibly delete) temporary directories.
struct TmpDir {
  std::string path;

  TmpDir() : path(TmpDir::make_tmp_dir()) {}
  ~TmpDir() { cleanup(); }

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

// Find the top of the OpenTitan repository
//
// If REPO_TOP is defined, use that. Otherwise, this will only work if we're
// running from a binary inside the git repository. This happens with the
// default paths (which put BUILD_BIN at $REPO_TOP/build-bin). If we can't find
// an enclosing repository, throw a std::runtime_error.
static std::string find_repo_top() {
  const char *from_env = getenv("REPO_TOP");
  if (from_env)
    return std::string(from_env);

  // No environment variable. Work from /proc/self/exe.
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
          << self_path.get()
          << (". To run the OTBN model outside of the repo, "
              "set the $REPO_TOP environment variable.");
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

  // If we get here, path_buf points at a .git directory, and also ends in
  // ".git". Resize to trim off the trailing "/.git"
  assert(path_buf.size() > 5);
  path_buf.resize(path_buf.size() - 5);
  return path_buf;
}

// Find the otbn Python model. On failure, throw a std::runtime_error with a
// description of what went wrong.
static std::string find_otbn_model() {
  std::string path = find_repo_top() + "/hw/ip/otbn/dv/otbnsim/stepped.py";
  c_str_ptr abs_path(realpath(path.c_str(), NULL));
  if (!abs_path) {
    std::ostringstream oss;
    oss << "Cannot find otbnsim.py, at '" << path << "'.\n";
    throw std::runtime_error(oss.str());
  }

  return std::string(abs_path.get());
}

// Read 8 hex characters from str as a uint32_t.
static uint32_t read_hex_32(const char *str) {
  char buf[9];
  memcpy(buf, str, 8);
  buf[8] = '\0';
  return strtoul(buf, nullptr, 16);
}

// Read through trace output (in the lines argument) to pick up any write to
// the named CSR register. If there is no such write, return default_val.
static uint32_t read_ext_reg(const std::string &reg_name,
                             const std::vector<std::string> &lines,
                             uint32_t default_val) {
  // We're interested in lines that show an update to the external register
  // called reg_name. These look something like this:
  //
  //   ! otbn.$REG_NAME: 0x00000000
  std::regex re("! otbn\\." + reg_name + ": 0x([0-9a-f]{8})");
  std::smatch match;

  uint32_t val = default_val;

  for (const auto &line : lines) {
    if (std::regex_match(line, match, re)) {
      // Ahah! We have a match. We have captured exactly 8 hex digits, so know
      // that we can safely parse them to a uint32_t without risking a parse
      // failure or overflow.
      assert(match.size() == 2);
      val = (uint32_t)strtoul(match[1].str().c_str(), nullptr, 16);
    }
  }

  return val;
}

ISSWrapper::ISSWrapper() : tmpdir(new TmpDir()) {
  std::string model_path(find_otbn_model());

  // We want two pipes: one for writing to the child process, and the other for
  // reading from it. We set the O_CLOEXEC flag so that the child process will
  // drop all the fds when it execs.
  int fds[4];
  for (int i = 0; i < 2; ++i) {
    if (pipe2(fds + 2 * i, O_CLOEXEC)) {
      std::ostringstream oss;
      oss << "Failed to open pipe " << i << " for ISS: " << strerror(errno);
      throw std::runtime_error(oss.str());
    }
  }

  // fds[0] and fds[2] are the read ends of two pipes, with write ends at
  // fds[1] and fds[3], respectively.
  //
  // We'll attach fds[0] to the child's stdin and fds[3] to the child's stdout.
  // That means we write to fds[1] to send data to the child and read from
  // fds[2] to get data back.
  pid_t pid = fork();
  if (pid == -1) {
    // Something went wrong.
    std::ostringstream oss;
    oss << "Failed to fork to create ISS process: " << strerror(errno);
    throw std::runtime_error(oss.str());
  }

  if (pid == 0) {
    // We are the child process. Attach stdin/stdout. (No need to close the
    // pipe fds: we'll close them as part of the exec.)
    close(0);
    if (dup2(fds[0], 0) == -1) {
      std::cerr << "Failed to set stdin in ISS subprocess: " << strerror(errno)
                << "\n";
      abort();
    }
    close(1);
    if (dup2(fds[3], 1) == -1) {
      std::cerr << "Failed to set stdout in ISS subprocess: " << strerror(errno)
                << "\n";
      abort();
    }
    // Finally, exec the ISS
    execl(model_path.c_str(), model_path.c_str(), NULL);
  }

  // We are the parent process and pid is the PID of the child. Close the pipe
  // ends that we don't need (because the child is using them)
  close(fds[0]);
  close(fds[3]);

  child_pid = pid;

  // Finally, construct FILE* streams for the fds (which will make life easier
  // when we actually use them to communicate with the child process)
  child_write_file = fdopen(fds[1], "w");
  child_read_file = fdopen(fds[2], "r");

  // The fdopen calls should have succeeded (because we know the fds are
  // valid). Add an assertion to make sure nothing weird happens.
  assert(child_write_file);
  assert(child_read_file);
}

ISSWrapper::~ISSWrapper() {
  // Stop the child process if it's still running. No need to be nice: we'll
  // just send a SIGKILL. Also, no need to check whether it's running first: we
  // can just fire off the signal and ignore whether it worked or not.
  kill(child_pid, SIGKILL);

  // Now wait for the child. This should be a very short wait.
  waitpid(child_pid, NULL, 0);

  // Close the child file handles.
  fclose(child_write_file);
  fclose(child_read_file);
}

void ISSWrapper::load_d(const std::string &path) {
  std::ostringstream oss;
  oss << "load_d " << path << "\n";
  run_command(oss.str(), nullptr);
}

void ISSWrapper::load_i(const std::string &path) {
  std::ostringstream oss;
  oss << "load_i " << path << "\n";
  run_command(oss.str(), nullptr);
}

void ISSWrapper::dump_d(const std::string &path) const {
  std::ostringstream oss;
  oss << "dump_d " << path << "\n";
  run_command(oss.str(), nullptr);
}

void ISSWrapper::start(uint32_t addr) {
  std::ostringstream oss;
  oss << "start " << addr << "\n";
  run_command(oss.str(), nullptr);
}

std::pair<bool, uint32_t> ISSWrapper::step(bool gen_trace) {
  std::vector<std::string> lines;
  run_command("step\n", &lines);
  if (gen_trace) {
    OtbnTraceChecker::get().OnIssTrace(lines);
  }

  // The busy flag is bit 0 of the STATUS register, so is cleared on this cycle
  // if we see a write that sets the value to an even number.
  bool done = (read_ext_reg("STATUS", lines, 1) & 1) == 0;
  uint32_t err_code = done ? read_ext_reg("ERR_BITS", lines, 0) : 0;
  return std::make_pair(done, err_code);
}

void ISSWrapper::get_regs(std::array<uint32_t, 32> *gprs,
                          std::array<u256_t, 32> *wdrs) {
  assert(gprs && wdrs);

  std::vector<std::string> lines;
  run_command("print_regs\n", &lines);

  // A record of which registers we've seen (to check we see each
  // register exactly once). GPR i sets bit i. WDR i sets bit 32 + i.
  uint64_t seen_mask = 0;

  // Lines look like
  //
  //  x3  = 0x12345678
  //  w10 = 0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef

  std::regex re("\\s*([wx][0-9]{1,2})\\s*=\\s*0x([0-9a-f]+)");
  std::smatch match;

  for (const std::string &line : lines) {
    if (line == "PRINT_REGS")
      continue;

    if (!std::regex_match(line, match, re)) {
      std::ostringstream oss;
      oss << "Invalid line in ISS print_register output (`" << line << "').";
      throw std::runtime_error(oss.str());
    }

    assert(match.size() == 3);

    std::string reg_name = match[1].str();
    std::string str_value = match[2].str();

    assert(reg_name.size() <= 3);
    assert(reg_name[0] == 'w' || reg_name[0] == 'x');
    bool is_wide = reg_name[0] == 'w';
    int reg_idx = atoi(reg_name.c_str() + 1);

    assert(reg_idx >= 0);
    if (reg_idx >= 32) {
      std::ostringstream oss;
      oss << "Invalid register name in ISS output (`" << reg_name
          << "'). Line was `" << line << "'.";
      throw std::runtime_error(oss.str());
    }

    unsigned idx_seen = reg_idx + (is_wide ? 32 : 0);
    if ((seen_mask >> idx_seen) & 1) {
      std::ostringstream oss;
      oss << "Duplicate lines writing register " << reg_name << ".";
      throw std::runtime_error(oss.str());
    }

    unsigned num_u32s = is_wide ? 8 : 1;
    unsigned expected_value_len = 8 * num_u32s;
    if (str_value.size() != expected_value_len) {
      std::ostringstream oss;
      oss << "Value for register " << reg_name << " has " << str_value.size()
          << " hex characters, but we expected " << expected_value_len << ".";
      throw std::runtime_error(oss.str());
    }

    uint32_t *dst = is_wide ? &(*wdrs)[reg_idx].words[7] : &(*gprs)[reg_idx];
    for (unsigned i = 0; i < num_u32s; ++i) {
      *dst = read_hex_32(&str_value[8 * i]);
      --dst;
    }

    seen_mask |= ((uint64_t)1 << idx_seen);
  }

  // Check that we've seen all the registers
  if (~seen_mask) {
    std::ostringstream oss;
    oss << "Some registers were missing from print_register output. Mask: 0x"
        << std::hex << seen_mask << ".";
    throw std::runtime_error(oss.str());
  }
}

std::vector<uint32_t> ISSWrapper::get_call_stack() {
  std::vector<std::string> lines;
  run_command("print_call_stack\n", &lines);

  std::regex re("\\s*0x([0-9a-f]+)");
  std::smatch match;
  std::vector<uint32_t> call_stack;

  for (const std::string &line : lines) {
    if (line == "PRINT_CALL_STACK")
      continue;

    if (!std::regex_match(line, match, re)) {
      std::ostringstream oss;
      oss << "Invalid line in ISS print_call_stack output (`" << line << "').";
      throw std::runtime_error(oss.str());
    }

    assert(match.size() == 2);

    std::string str_value = match[1];

    if (str_value.size() != 8) {
      std::ostringstream oss;
      oss << "Value from call stack " << str_value << " has "
          << str_value.size() << " hex characters, but we expected 8.";
      throw std::runtime_error(oss.str());
    }

    uint32_t call_stack_entry = read_hex_32(str_value.c_str());

    call_stack.push_back(call_stack_entry);
  }

  return call_stack;
}

std::string ISSWrapper::make_tmp_path(const std::string &relative) const {
  return tmpdir->path + "/" + relative;
}

bool ISSWrapper::read_child_response(std::vector<std::string> *dst) const {
  char buf[256];
  bool continuation = false;

  for (;;) {
    // fgets reads a line, or fills buf, whichever happens first. It always
    // writes the terminating null, so setting the second last position to \0
    // beforehand can detect whether we filled buf without needing a call to
    // strlen: buf is full if and only if this gets written with something
    // other than a null.
    buf[sizeof buf - 2] = '\0';

    if (!fgets(buf, sizeof buf, child_read_file)) {
      // Failed to read from child, or EOF
      return false;
    }

    // If buf is ".\n", and we're not continuing another line, we're done.
    if (!continuation && (0 == strcmp(buf, ".\n"))) {
      return true;
    }

    // Have we read an entire line? If not, fgets will have written something
    // other than \0 or \n to the second last entry in buf.
    char canary = buf[sizeof buf - 2];
    bool next_continuation = !(canary == '\0' || canary == '\n');

    // We have some informative response from the child. Take a copy if dst is
    // not null, stripping any trailing newline.
    if (dst) {
      if (continuation) {
        assert(dst->size());
        dst->back() += buf;
      } else {
        dst->push_back(std::string(buf));
      }

      // If !next_continuation then we read an entire line. If we didn't get to
      // EOF, the last character of dst->back() is a newline. Drop it.
      if (!next_continuation && dst->back().back() == '\n') {
        dst->back().pop_back();
      }
    }

    // Set the continuation flag if we filled buf without a newline.
    continuation = next_continuation;
  }
}

bool ISSWrapper::run_command(const std::string &cmd,
                             std::vector<std::string> *dst) const {
  assert(cmd.size() > 0);
  assert(cmd.back() == '\n');

  fputs(cmd.c_str(), child_write_file);
  fflush(child_write_file);
  return read_child_response(dst);
}
