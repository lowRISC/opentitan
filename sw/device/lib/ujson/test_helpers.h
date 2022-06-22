// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_UJSON_TEST_HELPERS_H_
#define OPENTITAN_SW_DEVICE_LIB_UJSON_TEST_HELPERS_H_

#include <string>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/ujson/ujson.h"

namespace test_helpers {
class SourceSink {
 public:
  SourceSink() {}
  SourceSink(const std::string &source) : source_(source) {}

  const std::string &Sink() { return sink_; }

  ujson_t UJson() {
    return ujson_init((void *)this, &SourceSink::getc, &SourceSink::putbuf);
  }

  void Reset() {
    pos_ = 0;
    sink_.clear();
  }

  void Reset(const std::string &source) {
    Reset();
    source_ = source;
  }

  status_t GetChar() {
    if (pos_ < source_.size()) {
      return OK_STATUS(static_cast<uint8_t>(source_[pos_++]));
    } else {
      return RESOURCE_EXHAUSTED();
    }
  }

  status_t PutBuf(const char *buf, size_t len) {
    sink_.append(buf, len);
    return OK_STATUS();
  }

 private:
  static status_t getc(void *self) {
    return static_cast<SourceSink *>(self)->GetChar();
  }

  static status_t putbuf(void *self, const char *buf, size_t len) {
    return static_cast<SourceSink *>(self)->PutBuf(buf, len);
  }

  size_t pos_ = 0;
  std::string source_;
  std::string sink_;
};
}  // namespace test_helpers
#endif  // OPENTITAN_SW_DEVICE_LIB_UJSON_TEST_HELPERS_H_
