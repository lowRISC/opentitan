// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_SERIAL_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_SERIAL_H_
#include "usbdev_stream.h"

class USBDevSerial : public USBDevStream {
 public:
  USBDevSerial(unsigned id, uint32_t transfer_bytes, bool retrieve, bool check,
               bool send, bool verbose)
      : USBDevStream(id, transfer_bytes, retrieve, check, send, verbose) {}
  ~USBDevSerial();

  bool Open(const char *in_name, const char *out_name);

  virtual void Close();

  /**
   * Service this serial stream.
   *
   * @return true iff the stream is still operational.
   */
  virtual bool Service();

 private:
  /**
   *
   */
  bool ServiceIN();
  /**
   *
   */
  bool ServiceOUT();

  /**
   * Input port handle
   */
  int in_;
  /**
   * Output port handle
   */
  int out_;
  /**
   * Stream signature
   */
  usbdev_stream_sig_t sig_;
  /**
   * Input port name
   */
  //  char in_name[FILENAME_MAX];
  /**
   * Output port name
   */
  //  char out_name[FILENAME_MAX];
};

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_SERIAL_H_
