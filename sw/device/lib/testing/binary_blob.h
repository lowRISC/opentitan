// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_BINARY_BLOB_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_BINARY_BLOB_H_

#include <cstring>
#include <string>

#include "gtest/gtest.h"

namespace testutil {
template <typename T>
class BinaryBlob {
 public:
  BinaryBlob(const T &data) : data_(data) {}

  BinaryBlob(const void *ptr, size_t len) {
    assert(len <= sizeof(data_) &&
           "Length must be less than or equal to the size of the object.");
    memcpy(&data_, ptr, len);
  }

  /**
   * Resets the offset pointer to zero.
   */
  BinaryBlob &Reset() {
    offset_ = 0;
    return *this;
  }

  /**
   * Seeks the offset pointer relative to the current position.
   */
  BinaryBlob &Seek(ssize_t delta) {
    offset_ += delta;
    CheckOffset("seek");
    return *this;
  }

  /**
   * Tries to find the item within the data, starting at the offset pointer.
   *
   * @param item The item to find.
   * @return bool whether or not the item was found.
   */
  template <typename U>
  bool TryFind(const U &item) {
    const char *data = reinterpret_cast<const char *>(&data_) + offset_;
    size_t len = sizeof(data_) - offset_;
    const char *found =
        reinterpret_cast<const char *>(memmem(data, len, &item, sizeof(item)));
    if (found) {
      offset_ = found - data;
      return true;
    } else {
      return false;
    }
  }

  /**
   * Finds the item within the data, starting at the offset pointer.
   */
  template <typename U>
  BinaryBlob &Find(const U &item) {
    assert(TryFind(item) && "Item not found.");
    return *this;
  }

  /**
   * Read from the offset.
   */
  template <typename U>
  U Read() {
    U tmp;
    CheckOffset("read");
    const char *data = reinterpret_cast<const char *>(&data_) + offset_;
    memcpy(&tmp, data, sizeof(tmp));
    offset_ += sizeof(tmp);
    return tmp;
  }

  /**
   * Read from the offset.
   */
  template <typename U>
  BinaryBlob &Write(const U &val) {
    CheckOffset("write");
    char *data = reinterpret_cast<char *>(&data_) + offset_;
    memcpy(data, &val, sizeof(val));
    offset_ += sizeof(val);
    return *this;
  }

  T *get() { return &data_; }

 private:
  void CheckOffset(const std::string &what) {
    ASSERT_GE(offset_, 0) << what << " offset out of range";
    ASSERT_LT(offset_, sizeof(data_)) << what << " offset out of range";
  }

  T data_{};
  ssize_t offset_ = 0;
};

}  // namespace testutil
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_BINARY_BLOB_H_
