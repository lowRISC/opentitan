// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USB_DEVICE_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USB_DEVICE_H_
#include <iostream>

// The 'usbdev_serial' class may be used on platforms where libusb support is
// not available; libusb is required to exercise Isochronous streams, Interrupt
// streams and Control Transfers.
#if STREAMTEST_LIBUSB
#include <libusb-1.0/libusb.h>
#endif

class USBDevice {
 public:
#if STREAMTEST_LIBUSB
  USBDevice(bool verbose = false)
      : verbose_(verbose),
        state_(StateStreaming),
        ctx_(nullptr),
        devh_(nullptr) {}
#else
  USBDevice(bool verbose = false)
      : verbose_(verbose), state_(StateStreaming), devh_(false) {}
#endif

  // Device states.
  enum USBDevState {
    StateStreaming,
    StateSuspending,
    StateSuspended,
    StateResuming
  };

  // DPI test numbers.
  typedef enum usb_testutils_test_number {
    kUsbTestNumberSmoke = 0,
    kUsbTestNumberStreams,
    kUsbTestNumberIso,
    kUsbTestNumberMixed,
    kUsbTestNumberSuspend,
    kUsbTestNumberExc,
  } usb_testutils_test_number_t;

  // Test/stream flags; these are common with device-side software.
  typedef enum {
    /**
     * Mask for extracting the stream ID number.
     */
    kUsbdevStreamFlagID = 0x0FU,
    /**
     * Host shall retrieve IN data from the device for this stream.
     */
    kUsbdevStreamFlagRetrieve = 0x10U,
    /**
     * Host shall check that IN data matches as expected.
     */
    kUsbdevStreamFlagCheck = 0x20U,
    /**
     * DPI model (or Host) shall retry IN data fetches, where possible.
     */
    kUsbdevStreamFlagRetry = 0x40U,
    /**
     * Host shall send OUT data to the device for this stream.
     */
    kUsbdevStreamFlagSend = 0x80U,
    /**
     * Default stream flags; for non-libusb builds.
     */
    kUsbdevStreamFlagsDefault = kUsbdevStreamFlagRetrieve |
                                kUsbdevStreamFlagCheck |
                                kUsbdevStreamFlagRetry | kUsbdevStreamFlagSend
  } usbdev_stream_flags_t;

  // Vendor-Specific requests.
  static constexpr uint8_t kVendorGetData = 0x7du;
  static constexpr uint8_t kVendorPutData = 0x7fu;

  // Maximum packet size of 64 bytes is used for Control, Interrupt and Bulk
  // Transfers.
  static constexpr unsigned kDevDataMaxPacketSize = 0x40U;

  // Our USB device has a maximum packet size of just 64 bytes even for
  // Isochronous transfers; this may one day be increased.
  static constexpr unsigned kDevIsoMaxPacketSize = 0x40U;

  /**
   * Initialize USB device before test; called once at startup.
   *
   * @param  vendorID   Vendor ID code of the USB device.
   * @param  productID  Product ID code of the USB device.
   * @param  devAddress Device address (0 for first accessible device).
   * @param  busNumber  Bus number (if devAddress non-zero).
   * @return true iff initialization was successful.
   */
  bool Init(uint16_t productID, uint16_t vendorID, uint8_t devAddress = 0u,
            uint8_t busNumber = 0u);
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

#if STREAMTEST_LIBUSB
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
   * Fill Control Transfer descriptor.
   */
  void FillControlTransfer(struct libusb_transfer *xfr, uint8_t ep,
                           uint8_t *buffer, libusb_transfer_cb_fn callback,
                           void *user_data, unsigned timeout_ms) {
    libusb_fill_control_transfer(xfr, devh_, buffer, callback, user_data,
                                 timeout_ms);
    // Complete the endpoint number because we're _not_ always targeting
    // Endpoint Zero.
    xfr->endpoint = ep;
  }
  /**
   * Fill Bulk Transfer descriptor.
   */
  void FillBulkTransfer(struct libusb_transfer *xfr, uint8_t ep,
                        uint8_t *buffer, size_t len,
                        libusb_transfer_cb_fn callback, void *user_data,
                        unsigned timeout_ms) const {
    libusb_fill_bulk_transfer(xfr, devh_, ep, buffer, len, callback, user_data,
                              timeout_ms);
  }
  /**
   * Fill Interrupt Transfer descriptor.
   */
  void FillIntTransfer(struct libusb_transfer *xfr, uint8_t ep, uint8_t *buffer,
                       size_t len, libusb_transfer_cb_fn callback,
                       void *user_data, unsigned timeout_ms) const {
    libusb_fill_interrupt_transfer(xfr, devh_, ep, buffer, len, callback,
                                   user_data, timeout_ms);
  }
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
  /**
   * Complete the lengths of the packets in this Isochronous transfer, assuming
   * that packets are of uniform size.
   *
   * @param  xfr     Isochronous transfer to be completed.
   * @param  len     Total length of all packets within the transfer.
   */
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
   * Cancel a pending transfer.
   *
   * @param  xfr     The transfer to be cancelled.
   */
  int CancelTransfer(struct libusb_transfer *xfr) const {
    return libusb_cancel_transfer(xfr);
  }
#endif

  /**
   * Read Test Descriptor from the DUT using a Vendor-Specific command.
   *
   * @return true iff the operation was successful.
   */
  bool ReadTestDesc();
  /**
   * Return the test number from the test descriptor.
   *
   * @return test number
   */
  uint8_t TestNumber() const { return testNumber_; }
  /**
   * Return the specified test argument from the test descriptor.
   *
   * @param  arg     Argument number.
   * @return test argument
   */
  uint8_t TestArg(unsigned arg) const {
    // Presently all defined tests support up to 4 arguments.
    return (arg < 4U) ? testArg_[arg] : 0U;
  }
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
  /**
   * Returns the current state of the device.
   *
   * @return current state.
   */
  USBDevState CurrentState() const { return state_; }
  /**
   * Sets the current state of the device in the Suspend/Resume signaling.
   *
   * @param  state   The current state of the device.
   */
  void SetState(USBDevState state) { state_ = state; }

 private:
  // Verbose logging/reporting.
  bool verbose_;

  // Current device state.
  USBDevState state_;

  // Vendor ID of USB device.
  uint16_t vendorID_;
  // Product ID of USB device.
  uint16_t productID_;

  // Specified bus number.
  uint8_t busSpec_;
  // Specified device address.
  uint8_t addrSpec_;

  // Bus number of the device we're using.
  uint8_t busNumber_;
  // (Bus-local) device address of the device we're using.
  uint8_t devAddress_;

#if STREAMTEST_LIBUSB
  // Context information for libusb.
  libusb_context *ctx_;

  // Device handle.
  libusb_device_handle *devh_;

  // Device descriptor.
  libusb_device_descriptor devDesc_;
#else
  // Device handle; just retain whether open/closed.
  bool devh_;
#endif

  // Device path (bus number - ports numbers).
  std::string devPath_;

  usb_testutils_test_number_t testNumber_;

  uint8_t testArg_[4];

  // TODO: We should introduce a timeout on libusb Control Transfers.
  static const unsigned kControlTransferTimeout = 0u;

  // Vendor-Specific Commands.
  static const uint8_t kVendorTestConfig = 0x7cu;
  static const uint8_t kVendorTestStatus = 0x7eu;
};

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USB_DEVICE_H_
