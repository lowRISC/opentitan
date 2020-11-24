// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Helper code for the UVM testbench. The corresponding SV declarations are in
// otbn_env_pkg.sv.

#include <cassert>
#include <cstring>
#include <dirent.h>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <sys/types.h>

namespace {
struct DirDeleter {
  void operator()(DIR *dir) const {
    // Ignore the return value from closedir: the only way it can fail is if
    // dir was an invalid descriptor, which it isn't.
    (void)closedir(dir);
  }
};

typedef std::unique_ptr<DIR, DirDeleter> dir_ptr;

// Return true if this name looks like it might be an ELF file (must be
// <FOO>.elf for some non-empty <FOO>).
static bool IsElfFileName(const char *name) {
  size_t len = strlen(name);
  return (len >= 5) && (memcmp(name + len - 4, ".elf", 4) == 0);
}

class OtbnTestHelper {
 public:
  std::string dir_path_;
  std::string file_path_;

  OtbnTestHelper(const std::string dir_path) : dir_path_(dir_path) {}

  int CountFilesInDir() const {
    dir_ptr dir(opendir(dir_path_.c_str()));
    if (!dir)
      return 0;

    int count = 0;
    for (;;) {
      struct dirent *entry = readdir(dir.get());
      if (!entry)
        break;

      if (entry->d_type != DT_REG)
        continue;

      // Only look at files ending in .elf
      if (!IsElfFileName(entry->d_name)) {
        continue;
      }

      ++count;
    }

    return count;
  }

  void SetFile(unsigned idx) {
    file_path_ = "";

    dir_ptr dir(opendir(dir_path_.c_str()));
    if (!dir) {
      return;
    }

    unsigned count = 0;
    for (;;) {
      struct dirent *entry = readdir(dir.get());
      if (!entry)
        break;

      if (entry->d_type != DT_REG)
        continue;

      if (!IsElfFileName(entry->d_name))
        continue;

      if (count == idx) {
        std::ostringstream oss;
        oss << dir_path_ << "/" << entry->d_name;
        file_path_ = oss.str();
        return;
      }

      ++count;
    }

    // We ran out of entries before we got to index.
  }
};
}  // namespace

// Make an OTBN test helper
extern "C" OtbnTestHelper *OtbnTestHelperMake(const char *path) {
  assert(path != nullptr);
  return new OtbnTestHelper(path);
}

// Free an OTBN test helper
extern "C" void OtbnTestHelperFree(OtbnTestHelper *helper) {
  assert(helper != nullptr);
  delete helper;
}

// Count the number of regular files in the directory at path. If path does not
// name a directory (or names a directory that cannot be opened for some
// reason), return zero.
extern "C" int OtbnTestHelperCountFilesInDir(OtbnTestHelper *helper) {
  assert(helper != nullptr);
  return helper->CountFilesInDir();
}

// Get a file in the given directory. The file is that at position index when
// stepping through the directory with readdir(). On success, returns the path.
// On failure, returns an empty string.
extern "C" const char *OtbnTestHelperGetFilePath(OtbnTestHelper *helper,
                                                 int index) {
  assert(helper != nullptr);
  assert(index >= 0);

  helper->SetFile(index);
  return helper->file_path_.c_str();
}
