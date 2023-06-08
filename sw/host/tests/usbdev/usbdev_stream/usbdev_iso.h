// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_ISO_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_ISO_H_
#include <queue>

#include "usb_device.h"
#include "usbdev_stream.h"

class USBDevIso : public USBDevStream {
 public:
  USBDevIso(USBDevice *dev, unsigned id, uint32_t transfer_bytes, bool retrieve,
            bool check, bool send, bool verbose)
      : USBDevStream(id, transfer_bytes, retrieve, check, send, verbose),
        dev_(dev),
        inActive_(false),
        outActive_(false),
        xfrIn_(nullptr),
        xfrOut_(nullptr) {}

  /**
   *
   *
   */
  bool Open(unsigned interface);

  /**
   *
   *
   */
  virtual void Close();

  /**
   * Service this Isochronous stream.
   *
   * @return true iff the stream is still operational.
   */
  virtual bool Service();

 private:
  void DumpIsoTransfer(struct libusb_transfer *xfr) const;

  bool ServiceIN();
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

  // TODO: If these remain this simple, strip them!
  /**
   *
   */
  void AddPacket(uint32_t len) { pktLen_.push(len); }
  /**
   *
   */
  bool RemovePacket(uint32_t *len) {
    if (!pktLen_.empty()) {
      *len = pktLen_.front();
      pktLen_.pop();
      return true;
    }
    return false;
  }

  // USB device.
  USBDevice *dev_;

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

  // Expected device-side sequence number of next IN packet.
  uint16_t tst_seq_;

  // Lengths of packets (in bytes) of the Isochronous Data packets held in the
  // circular buffer.
  std::queue<uint32_t> pktLen_;

  // Isochronous traffic
  uint8_t inBuffer[USBDevice::kDevIsoMaxPacketSize];

  // TODO: timeout parameters need consideration.
  //  static constexpr unsigned kIsoTimeout = 0U;
  static constexpr unsigned kIsoTimeout = 0U;

  // Since the USB device is Full Speed it supports only one Isochronous
  // Data packet per bus frame.
  static constexpr unsigned kNumIsoPackets = 1U;
};

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_ISO_H_
