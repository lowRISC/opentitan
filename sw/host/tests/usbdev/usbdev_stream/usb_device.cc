// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "usb_device.h"

#include <cstring>
#include <fcntl.h>
#include <iostream>
#include <linux/usbdevice_fs.h>
#include <unistd.h>

// Initialize USB access, with intent to use a device with the given properties.
bool USBDevice::Init(uint16_t vendorID, uint16_t productID) {
  // Initialize libusb
  int rc = libusb_init_context(&ctx_, NULL, 0);
  if (rc < 0) {
    return ErrorUSB("ERROR: Initializing libusb", rc);
  }

  // Remember vendor and product IDs because the device may be opened and
  // closed many times during the test.
  vendorID_ = vendorID;
  productID_ = productID;
  return true;
}

// Finalize use of the device.
bool USBDevice::Fin() {
  (void)Close();
  libusb_exit(ctx_);
  return true;
}

// Open the device, if not already open.
bool USBDevice::Open() {
  // Check whether we have already opened the device.
  if (devh_) {
    return true;
  }

  // Locate our USB device
  std::cout << "Locating USB device" << std::endl;
  unsigned numTries = 30u;
  bool found = false;
  do {
    // No device handle at present
    devh_ = nullptr;

    // We need to traverse a list of all devices before opening it; since
    // we require the port numbers leading to our device, we cannot take the
    // easier approach of using _open_device_with_vid_pid()
    libusb_device **dev_list;
    ssize_t num_devs = libusb_get_device_list(ctx_, &dev_list);
    int idx;
    for (idx = 0; idx < num_devs; idx++) {
      int rc = libusb_get_device_descriptor(dev_list[idx], &devDesc_);
      if (rc >= 0) {
        if (verbose_) {
          std::cout << "Device: "
                    << "VendorID: " << std::hex << devDesc_.idVendor
                    << " ProductID: " << devDesc_.idProduct << std::dec
                    << std::endl;
        }
        if (devDesc_.idVendor == vendorID_ &&
            devDesc_.idProduct == productID_) {
          break;
        }
      }
    }
    if (idx < num_devs) {
      // We have found the device in which we're interested; obtain the list
      // of port numbers
      libusb_device *dev = dev_list[idx];
      uint8_t bus = libusb_get_bus_number(dev);
      if (verbose_) {
        std::cout << "Device path: " << (unsigned)bus << "-";
      }
      devPath_ = std::to_string(bus) + '-';
      uint8_t ports[8];
      int rc = libusb_get_port_numbers(dev, ports, sizeof(ports));
      if (rc >= 0) {
        unsigned num_ports = (unsigned)rc;
        for (unsigned idx = 0u; idx < num_ports; idx++) {
          if (verbose_) {
            std::cout << (unsigned)ports[idx];
          }
          devPath_ += std::to_string(ports[idx]);
          if (idx + 1 < num_ports) {
            std::cout << '.';
            devPath_ += '.';
          }
        }
        std::cout << std::endl;
      } else {
        std::cerr << "Error getting port list: " << libusb_error_name(rc)
                  << std::endl;
        return false;
      }

      // Open a handle to our device
      rc = libusb_open(dev, &devh_);
      if (rc < 0) {
        std::cerr << "Error opening device: " << libusb_error_name(rc)
                  << std::endl;
        return false;
      }

      // Unreference all devices and release device list
      libusb_free_device_list(dev_list, 1u);
    }

    if (devh_) {
      found = true;
    } else if (numTries-- > 0u) {
      // Retry a number of times before reporting failure.
      std::cout << '.' << std::flush;
      sleep(1);
    } else {
      std::cerr << "Unable to locate USB device" << std::endl;
      return false;
    }
  } while (!found);

  // Report that we have at least found the device.
  std::cout << "Device found" << std::endl;
  if (verbose_) {
    std::cout << " - Path: " << devPath_ << std::endl;
  }

  // We need to detach the kernel driver and claim the interface to have maximal
  // control, eg. suspending device.
  int rc = libusb_set_auto_detach_kernel_driver(devh_, 1u);
  if (rc < 0) {
    std::cerr << "Error detaching kernel driver: " << libusb_error_name(rc)
              << std::endl;
    return false;
  }

  // Read and check the currently active configuration; this should just be 1
  // since our test software sets up only a single configuration.
  int config;
  rc = libusb_get_configuration(devh_, &config);
  if (rc < 0) {
    std::cerr << "Error getting configuration: " << libusb_error_name(rc)
              << std::endl;
  }

  std::cout << "Configuration: " << config << std::endl;
  return true;
}

// Close the device, if open.
bool USBDevice::Close() {
  if (devh_) {
    libusb_close(devh_);
    devh_ = nullptr;
  }
  return true;
}

bool USBDevice::Service() {
  struct timeval tv = {0};
  int rc = libusb_handle_events_timeout(ctx_, &tv);
  if (rc < 0) {
    return ErrorUSB("ERROR: Handling events", rc);
  }
  return true;
}

// TODO:
uint16_t get_le16(const uint8_t *p) { return p[0] | (p[1] << 8); }

bool USBDevice::ReadTestDesc() {
  std::cout << "Reading Test Descriptor" << std::endl;

  if (!Open()) {
    return false;
  }

  // Send a Vendor-Specific command to read the test descriptor
  uint8_t testDesc[0x10u];
  int rc =
      libusb_control_transfer(devh_, 0xc2u, kVendorTestConfig, 0u, 0u, testDesc,
                              sizeof(testDesc), kControlTransferTimeout);
  if (rc < 0) {
    std::cerr << "Error reading test descriptor: " << libusb_error_name(rc)
              << std::endl;
    return false;
  }

  if (verbose_) {
    std::cout << "Test Descriptor:" << std::endl;
    for (unsigned idx = 0u; idx < sizeof(testDesc); idx++) {
      printf("%u: 0x%02x\n", idx, testDesc[idx]);
    }
  }

  // Validate the received test descriptor.
  const uint8_t test_sig_head[] = {0x7eu, 0x57u, 0xc0u, 0xf1u};
  const uint8_t test_sig_tail[] = {0x1fu, 0x0cu, 0x75u, 0xe7u};
  const uint8_t *dp = testDesc;
  if (!memcmp(dp, test_sig_head, 4) && 0x10u == get_le16(&dp[4]) &&
      !memcmp(&dp[12], test_sig_tail, 4)) {
    usb_testutils_test_number_t testNum =
        (usb_testutils_test_number_t)get_le16(&dp[6]);

    if (verbose_) {
      std::cout << "Test number: " << testNum << " args " << std::hex
                << (int)dp[8] << " " << (int)dp[9] << " " << (int)dp[10] << " "
                << (int)dp[11] << std::dec << std::endl;
    }

    // Retain the test number and the test arguments.
    testNumber_ = testNum;
    testArg_[0] = dp[8];
    testArg_[1] = dp[9];
    testArg_[2] = dp[10];
    testArg_[3] = dp[11];
    return true;
  }
  return false;
}

bool USBDevice::Suspend() {
  std::cout << "Suspending Device" << std::endl;

  // We need to relinquish our access to the device otherwise the kernel
  // will refuse to autosuspend the device!
  Close();

  std::string powerPath = "/sys/bus/usb/devices/" + devPath_ + "/power/";
  std::string filename = powerPath + "autosuspend_delay_ms";
  // TODO: tidy this...probably move to a utility function
  int fd = open(filename.c_str(), O_WRONLY);
  if (fd < 0) {
    std::cerr << "Failed to open '" << filename << "'" << std::endl;
    return false;
  }
  (void)write(fd, "0", 1);
  close(fd);

  //
  filename = powerPath + "control";
  fd = open(filename.c_str(), O_WRONLY);
  if (fd < 0) {
    std::cerr << "Failed to open '" << filename << "'" << std::endl;
    std::cerr << "  (Note: this requires sudo permissions)" << std::endl;
    return false;
  }
  (void)write(fd, "auto", 4);

  close(fd);

  return false;
}

bool USBDevice::Resume() {
  std::cout << "Resuming Device" << std::endl;

  if (!Open()) {
    return false;
  }

  std::string powerPath = "/sys/bus/usb/devices/" + devPath_ + "/power/";
  std::string filename = powerPath + "control";

  int fd = open(filename.c_str(), O_WRONLY);
  if (fd < 0) {
    std::cerr << "Failed to open '" << filename << "'" << std::endl;
    return false;
  }
  (void)write(fd, "on", 2);
  close(fd);

  return false;
}

bool USBDevice::Disconnect() {
  // TODO: Are we able to implement a Disconnect/Reconnect function here?
  //       Most hubs do not have the capacity to power cycle an individual
  //       port.
  //
  // Power Off
  // Power On

  return false;
}
