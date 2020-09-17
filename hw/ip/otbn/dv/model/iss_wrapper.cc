// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "iss_wrapper.h"

#include <cassert>
#include <cstring>
#include <fcntl.h>
#include <iostream>
#include <memory>
#include <regex>
#include <signal.h>
#include <sstream>
#include <sys/stat.h>
#include <sys/wait.h>

// Guard class to safely delete C strings
namespace {
struct CStrDeleter {
  void operator()(char *p) const { std::free(p); }
};
}
typedef std::unique_ptr<char, CStrDeleter> c_str_ptr;

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
  path_buf += "/../hw/ip/otbn/dv/otbnsim/stepped.py";
  c_str_ptr model_path(realpath(path_buf.c_str(), NULL));
  if (!model_path) {
    std::ostringstream oss;
    oss << "Cannot find otbnsim.py, at '" << path_buf
        << "' (guessed by searching upwards from '" << self_path.get()
        << "').\n";
    throw std::runtime_error(oss.str());
  }

  return std::string(model_path.get());
}

ISSWrapper::ISSWrapper() {
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

void ISSWrapper::load_d(const char *path) {
  std::ostringstream oss;
  oss << "load_d " << path << "\n";
  run_command(oss.str(), nullptr);
}

void ISSWrapper::load_i(const char *path) {
  std::ostringstream oss;
  oss << "load_i " << path << "\n";
  run_command(oss.str(), nullptr);
}

void ISSWrapper::dump_d(const char *path) const {
  std::ostringstream oss;
  oss << "dump_d " << path << "\n";
  run_command(oss.str(), nullptr);
}

void ISSWrapper::start(uint32_t addr) {
  std::ostringstream oss;
  oss << "start " << addr << "\n";
  run_command(oss.str(), nullptr);
}

size_t ISSWrapper::run() {
  size_t cycles = 0;
  std::vector<std::string> lines;

  for (;;) {
    ++cycles;
    lines.clear();
    run_command("step\n", &lines);
    if (saw_busy_cleared(lines))
      break;
  }
  return cycles;
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

    // Otherwise it's some informative response from the child: take a copy if
    // dst is not null.
    if (dst) {
      if (continuation) {
        assert(dst->size());
        dst->back() += buf;
      } else {
        dst->push_back(std::string(buf));
      }
    }

    // Set the continuation flag if we filled buf without a newline. Our
    // "canary" value at the end will be \0 or \n if and only if we got a
    // newline (or EOF) before the end of the buffer.
    char canary = buf[sizeof buf - 2];
    continuation = !(canary == '\0' || canary == '\n');
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

bool ISSWrapper::saw_busy_cleared(std::vector<std::string> &lines) const {
  // We're interested in lines that show an update to otbn.STATUS. These look
  // something like this:
  //
  //   otbn.STATUS &= ~ 0x000001 (from HW) (now 0x000000)
  //
  // The \n picks up the newline that we expect at the end of each line.
  std::regex re("\\s*otbn\\.STATUS.*0x[0-9]+\\)\n");

  bool is_cleared = false;

  for (const auto &line : lines) {
    if (std::regex_match(line, re)) {
      // Ahah! We have a match. At this point, we can cheat because we happen
      // to know that the the busy bit is bit zero, so we just need to check
      // whether the last character of the hex constant is even. Since the
      // regex has a fixed number (2) of characters after the hex constant, we
      // can just count back from the end of the string.
      char last_digit = (&line.back())[-2];

      int as_num;
      if ('0' <= last_digit && last_digit <= '9') {
        as_num = last_digit - '0';
      } else {
        assert('a' <= last_digit && last_digit <= 'f');
        as_num = 10 + (last_digit - 'a');
      }

      is_cleared = !(as_num & 1);
    }
  }

  return is_cleared;
}
