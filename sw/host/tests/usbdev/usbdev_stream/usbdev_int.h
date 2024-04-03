// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_INT_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_INT_H_
#include <queue>

#include "usb_device.h"
#include "usbdev_stream.h"

// Interrupt and Bulk Transfer-based streams to usbdev; as far as the host-
// and device-side code at application level is concerned, these are the same.
//
// The differences are at the service/delivery level offered by the lower USB
// layers.
class USBDevInt : public USBDevStream {
 public:
  USBDevInt(USBDevice *dev, bool bulk, unsigned id, uint32_t transfer_bytes,
            bool retrieve, bool check, bool send, bool verbose)
      : USBDevStream(id, transfer_bytes, retrieve, check, send, verbose),
        dev_(dev),
        bulk_(bulk),
        failed_(false),
        inActive_(false),
        outActive_(false),
        xfrIn_(nullptr),
        xfrOut_(nullptr) {}
  /**
   * Open an Interrupt connection to specified device interface.
   *
   * @param  interface  Interface number.
   * @return The success of the operation.
   */
  bool Open(unsigned interface);
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
   * Service this Interrupt stream.
   *
   * @return true iff the stream is still operational.
   */
  virtual bool Service();

 private:
  /**
   * Diagnostic utility function to display the content of libusb Bulk/Interrupt
   * transfer.
   *
   * @param  xfr     The Interrupt transfer to be displayed.
   */
  void DumpIntTransfer(struct libusb_transfer *xfr) const;
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
   * Callback function supplied to libusb for IN transfers; transfer has
   * completed and requires attention.
   *
   * @param  xfr     The transfer that has completed.
   */
  void CallbackIN(struct libusb_transfer *xfr);
  /**
   * Callback function supplied to libusb for OUT transfers; transfer has
   * completed and requires attention.
   *
   * @param  xfr     The transfer that has completed.
   */
  void CallbackOUT(struct libusb_transfer *xfr);
  /**
   * Stub callback function supplied to libusb for IN transfers.
   *
   * @param  xfr     The transfer that has completed.
   */
  static void LIBUSB_CALL CbStubIN(struct libusb_transfer *xfr);
  /**
   * Stub callback function supplied to libusb for OUT transfers.
   *
   * @param  xfr     The transfer that has completed.
   */
  static void LIBUSB_CALL CbStubOUT(struct libusb_transfer *xfr);

  // USB device.
  USBDevice *dev_;

  // Bulk Transfer Type?
  bool bulk_;

  // The number of the interface being used by this stream.
  unsigned interface_;

  // Has this stream experienced a failure?
  bool failed_;

  // Is an IN transfer in progress?
  bool inActive_;

  // Is an OUT transfer in progress?
  bool outActive_;

  // Do we currently have an IN transfer?
  struct libusb_transfer *xfrIn_;

  // Do we currently have an OUT transfer?
  struct libusb_transfer *xfrOut_;

  // Maximum packet size for this stream.
  uint8_t maxPacketSize_;

  // Endpoint numbers used by this stream.
  uint8_t epIn_;
  uint8_t epOut_;

  // Stream signature.
  // Note: this is constructed piecemeal as the bytes are received from the
  // device.
  usbdev_stream_sig_t sig_;

  // No timeout at present; the device-side code is responsible for signaling
  // test completion/failure. This may need to change for CI tests.
  static constexpr unsigned kDataTimeout = 0U;
};

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_INT_H_
