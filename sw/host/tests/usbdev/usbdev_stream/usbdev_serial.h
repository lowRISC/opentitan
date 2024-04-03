// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_SERIAL_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_SERIAL_H_
#include "usbdev_stream.h"

/**
 * Bulk Transfer Stream over ttyUSBn serial connection using File Descriptors.
 */
class USBDevSerial : public USBDevStream {
 public:
  USBDevSerial(unsigned id, uint32_t transfer_bytes, bool retrieve, bool check,
               bool send, bool verbose)
      : USBDevStream(id, transfer_bytes, retrieve, check, send, verbose) {}
  ~USBDevSerial();

  /**
   * Open the input and output ports to the board/device for this stream.
   *
   * @param  in_name   Device name of input serial port.
   * @param  out_name  Device name of output serial port.
   * @return true iff successful.
   */
  bool Open(const char *in_name, const char *out_name);
  /**
   * Finalize the stream, prior to shutting down.
   */
  virtual void Stop();
  /**
   * Pause the stream, prior to suspending the device.
   */
  virtual void Pause();
  /**
   * Resume stremaing.
   */
  virtual bool Resume();
  /**
   * Return a summary report of the stream settings or status.
   *
   * @param  status    Indicates whether settings or status requested.
   * @param  verbose   true iff a more verbose report is required.
   * @return Status report
   */
  virtual std::string Report(bool status = false, bool verbose = false) const;
  /**
   * Service this serial stream.
   *
   * @return true iff the stream is still operational.
   */
  virtual bool Service();

 private:
  /**
   * Retrieving of IN traffic from device.
   *
   * @return true iff the stream is still operational.
   */
  bool ServiceIN();
  /**
   * Sending of OUT traffic to device.
   *
   * @return true iff the stream is still operational.
   */
  bool ServiceOUT();
  /**
   * Open the input and output ports for this stream.
   *
   * @return true iff opened successfully.
   */
  bool OpenPorts();

  // Input port handle.
  int in_;

  // Output port handle.
  int out_;

  // Input port name.
  std::string inPort_;

  // Output port name.
  std::string outPort_;

  // Stream signature.
  // Note: this is constructed piecemeal as the bytes are received from the
  // device.
  usbdev_stream_sig_t sig_;
};

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_SERIAL_H_
