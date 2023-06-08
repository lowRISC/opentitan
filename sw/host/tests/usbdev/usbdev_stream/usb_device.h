// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USB_DEVICE_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USB_DEVICE_H_
#include <iostream>

#include "libusb.h"

class USBDevice {
 public:
  USBDevice(bool verbose = false)
      : verbose_(verbose), manual_(false), ctx_(nullptr), devh_(nullptr) {}

  // DPI test numbers
  typedef enum usb_testutils_test_number {
    kUsbTestNumberSmoke = 0,
    kUsbTestNumberStreams,
    kUsbTestNumberIso,
    kUsbTestNumberMixed,
    kUsbTestNumberSuspend,
    kUsbTestNumberExc,
  } usb_testutils_test_number_t;

  // Our USB device has a maximum packet size of just 64 bytes even for
  // Isochronous transfers.
  static constexpr unsigned kDevIsoMaxPacketSize = 0x40U;

  /**
   * Initialize USB device before test; called once at startup.
   *
   * @param  vendorID   Vendor ID code of the USB device.
   * @param  productID  Product ID code of the USB device.
   * @return true iff initialization was successful.
   */
  bool Init(uint16_t productID, uint16_t vendorID);
  /**
   * Finalize USB device before completing test.
   *
   * @return true iff finalization was successful.
   */
  bool Fin();
  /**
   * (Re)open the device. If the device is already open, this function just
   * returns immediately.
   *
   * @return true iff opening was successful, or the device was already open.
   */
  bool Open();
  /**
   * Close the device, if open. If the device is already closed, this function
   * just returns immediately.
   *
   * @return true iff closing was successful, or the device was already closed.
   */
  bool Close();
  /**
   * Service the device; keep libusb transfers being processed.
   *
   * @return true iff the device is still operational.
   */
  bool Service();
  /**
   * Claim an interface on the device.
   *
   * @param interface The interface number of the interface to be claimed.
   * @return The result of the operation.
   */
  int ClaimInterface(unsigned interface) const {
    return libusb_claim_interface(devh_, (int)interface);
  }
  /**
   * Release an interface on the device.
   *
   * @param interface The interface number of the interface to be claimed.
   * @return The result of the operation.
   */
  int ReleaseInterface(unsigned interface) const {
    return libusb_release_interface(devh_, (int)interface);
  }
  /**
   * Emit a textual report of an error returned by libusb.
   *
   * @param  rc      Return code from libusb function.
   * @return false as a convenience for indicating failure to caller.
   */
  inline bool ErrorUSB(const char *prefix, int rc) {
    std::cerr << prefix << " (" << rc << ", " << libusb_error_name(rc) << ")"
              << std::endl;
    return false;
  }
  /**
   * Retrieve libusb device handle.
   *
   * @return The device handle, or nullptr if none eg. device not open.
   */
  libusb_device_handle *DeviceHandle() const { return devh_; }
  /**
   * Fill Isochronous transfer descriptor,
   */
  void FillIsoTransfer(struct libusb_transfer *xfr, uint8_t ep, uint8_t *buffer,
                       size_t len, unsigned num_iso_packets,
                       libusb_transfer_cb_fn callback, void *user_data,
                       unsigned timeout_ms) const {
    libusb_fill_iso_transfer(xfr, devh_, ep, buffer, len, num_iso_packets,
                             callback, user_data, timeout_ms);
  }

  void SetIsoPacketLengths(struct libusb_transfer *xfr, unsigned len) const {
    libusb_set_iso_packet_lengths(xfr, len);
  }
  /**
   * Allocate a transfer descriptor to be completed by the caller.
   *
   * @return  Pointer to transfer transcript, or NULL if allocation failed.
   */
  struct libusb_transfer *AllocTransfer(unsigned iso_packets) const {
    return libusb_alloc_transfer((int)iso_packets);
  }
  /**
   * Free an allocated transfer descriptor.
   *
   * @param  xfr     The transfer descriptor to be freed.
   */
  void FreeTransfer(struct libusb_transfer *xfr) const {
    return libusb_free_transfer(xfr);
  }
  /**
   * Submit a transfer for processing.
   *
   * @param  xfr     The transfer to be submitted.
   */
  int SubmitTransfer(struct libusb_transfer *xfr) const {
    return libusb_submit_transfer(xfr);
  }

  /**
   * Read Test Descriptor from the DUT using a Vendor-Specific command.
   *
   * @return true iff the operation was successful.
   */
  bool ReadTestDesc();
  /**
   * Reset and Reconfigure the DUT.
   *
   * @return true iff the operation was successful.
   */
  bool Reset();
  /**
   * Suspend device.
   *
   * @return true iff the operation was successful.
   */
  bool Suspend();
  /**
   * Resume operation of suspended device.
   */
  bool Resume();
  /**
   * Disconnect and reconnect device.
   *
   * @param true iff the operation was succesful.
   */
  bool Disconnect();

  // Verbose logging/reporting.
  bool verbose_;

  // Test phases/behavior are being directed/controlled manually.
  bool manual_;

  // Context information for libusb
  libusb_context *ctx_;

  // Vendor ID of USB device.
  uint16_t vendorID_;
  // Product ID of USB device.
  uint16_t productID_;

  // Device handle
  libusb_device_handle *devh_;

  // Device descriptor
  libusb_device_descriptor devDesc_;

  // Device path (bus number - ports numbers)
  std::string devPath_;

  usb_testutils_test_number_t testNumber_;

  uint8_t testArg_[4];

  // TODO: We should introduce a timeout on libusb Control Transfers
  static const unsigned kControlTransferTimeout = 0u;

  // Vendor-Specific Commands
  static const uint8_t kVendorTestConfig = 0x7cu;
  static const uint8_t kVendorTestStatus = 0x7eu;
};

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USB_DEVICE_H_
