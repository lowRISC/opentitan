// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// usb_suspend_test
//
// Simple application that permits discovery, suspending, resuming and resetting
// of OpenTitan USB device.
//
// Note: Requires sudo permissions in order to use sysfs for autosuspend and
// resume behavior.

#include <cctype>
#include <cerrno>
#include <cstdbool>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <iostream>
#include <linux/usbdevice_fs.h>
#include <sys/ioctl.h>
#include <unistd.h>

#include "libusb.h"

/**
 * Test phases; named according to the event that we are expecting to occur.
 */
typedef enum {
  /**
   * First test phase just tests regular Suspend/Resume signaling; after we've
   * resumed, we expect a Bus Reset from the DPI/Host.
   */
  kSuspendPhaseSuspend = 0u,
  /**
   * This test phase instructs the DPI model to put the DUT into Suspend long
   * enough that this software will attempt to put the device into its Normal
   * Sleep state and exercise the AON/Wakeup module, stopping the clocks but not
   * powering down.
   */
  kSuspendPhaseSleepResume,
  /*
   * The AON/Wakeup module will cause us to awaken in response to a bus reset.
   */
  kSuspendPhaseSleepReset,
  /**
   * As above, but this time we're expecting a VBUS/SENSE loss.
   */
  kSuspendPhaseSleepDisconnect,
  /**
   * Mirrors Resume detection for normal sleep, but this time we enter Deep
   * Sleep and the power is removed too.
   */
  kSuspendPhaseDeepResume,
  /**
   * Mirrors Bus Reset detection for normal sleep, but this time we enter Deep
   * Sleep and the power is removed too.
   */
  kSuspendPhaseDeepReset,
  /**
   * As above, but this time we're expecting a VBUS/SENSE loss.
   */
  kSuspendPhaseDeepDisconnect,
  /**
   * Final phase; shut down.
   */
  kSuspendPhaseShutdown,
} usbdev_suspend_phase_t;

// DPI test numbers
typedef enum usb_testutils_test_number {
  kUsbTestNumberSmoke = 0,
  kUsbTestNumberStreams,
  kUsbTestNumberIso,
  kUsbTestNumberMixed,
  kUsbTestNumberSuspend,
  kUsbTestNumberExc,
} usb_testutils_test_number_t;

class USBDevice {
 public:
  USBDevice() : verbose_(false), manual_(false), devh_(nullptr) {}

  /**
   * Run test to completion.
   */
  bool RunTest();
  /**
   * (Re)open the device. If the device is already open, this function just
   * returns immediately.
   */
  bool Open();
  /**
   * Close the device, if open. If the device is already closed, this function
   * just returns immediately.
   */
  bool Close();
  /**
   * Parse command line arguments and retain settings.
   *
   * @return true iff command line arguments accepted.
   */
  bool ParseArgs(int argc, char *argv[]);

  /**
   * Report command line syntax.
   */
  void ReportSyntax();

  /**
   * Is test progress being directed/controlled manually?
   */
  inline bool ManualControl() const { return manual_; }
  /**
   * Returns the current phase of the test
   */
  inline usbdev_suspend_phase_t TestPhase() const { return _testPhase; }
  /**
   * Returns microseconds corresponding to the given number of bus frame delays.
   */
  static inline uint32_t TimeFrames(unsigned frames) { return frames * 1000u; }
  /**
   *
   */
  bool Delay(uint32_t time_us, bool with_traffic = true);
  /**
   * Read Test Descriptor from the DUT using a Vendor-Specific command.
   *
   * @return true iff the operation was succesful.
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
  /**
   * Return the textual name of the specified test phase.
   *
   * @param  phase     Test phase.
   * @return           Textual name.
   */
  static const char *PhaseName(usbdev_suspend_phase_t phase);

  // Verbose logging/reporting.
  bool verbose_;

  // Test phases/behavior are being directed/controlled manually.
  bool manual_;

  // Device handle
  libusb_device_handle *devh_;

  // Device descriptor
  libusb_device_descriptor _devDesc;

  // Device path (bus number - ports numbers)
  std::string _devPath;

  // Current phase within the Suspend-Sleep-Wakeup-Resume testing sequence.
  usbdev_suspend_phase_t _testPhase;

  uint8_t _testArg[4];

  // TODO: We should introduce a timeout on libusb Control Transfers
  static const unsigned kControlTransferTimeout = 0u;

  static const uint16_t kVendorID = 0x18d1u;
  static const uint16_t kProductID = 0x503au;
  static const int kInterface = 1;

  // Vendor-Specific Commands
  static const uint8_t kVendorTestConfig = 0x7cu;
  static const uint8_t kVendorTestStatus = 0x7eu;

  static const unsigned kFramesUntilSuspend = 2u;
  static const unsigned kFramesUntilSleep = 2u;
  static const unsigned kFramesUntilResume = 4u;
  static const unsigned kFramesUntilReset = 4u;
  static const unsigned kFramesUntilDisconnect = 4u;
  static const unsigned kFramesUntilResumed = 4u;
  static const unsigned kFramesUntilNextPhase = 4u;
};

// Context information for libusb
static libusb_context *ctx = NULL;

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
    // TODO: sadly this does not work for our requirements?
    if (false) {
      devh_ = libusb_open_device_with_vid_pid(ctx, kVendorID, kProductID);
    } else {
      // No device handle at present
      devh_ = nullptr;

      // We need to traverse a list of all devices before opening it; since
      // we require the port numbers leading to our device, we cannot take the
      // easier approach of using _open_device_with_vid_pid()
      libusb_device **dev_list;
      ssize_t num_devs = libusb_get_device_list(ctx, &dev_list);
      int idx;
      for (idx = 0; idx < num_devs; idx++) {
        int rc = libusb_get_device_descriptor(dev_list[idx], &_devDesc);
        if (rc >= 0) {
          if (verbose_) {
            std::cout << "Device: "
                      << "VendorID: " << std::hex << _devDesc.idVendor
                      << " ProductID: " << _devDesc.idProduct << std::dec
                      << std::endl;
          }
          if (_devDesc.idVendor == kVendorID &&
              _devDesc.idProduct == kProductID) {
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
        _devPath = std::to_string(bus) + '-';
        uint8_t ports[8];
        int rc = libusb_get_port_numbers(dev, ports, sizeof(ports));
        if (rc >= 0) {
          unsigned num_ports = (unsigned)rc;
          for (unsigned idx = 0u; idx < num_ports; idx++) {
            std::cout << (unsigned)ports[idx];
            _devPath += std::to_string(ports[idx]);
            if (idx + 1 < num_ports) {
              std::cout << '.';
              _devPath += '.';
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
    std::cout << " - Path: " << _devPath << std::endl;
  }

  // We need to detach the kernel driver and claim the interface to have maximal
  // control
  int rc = libusb_set_auto_detach_kernel_driver(devh_, 1u);
  if (rc < 0) {
    std::cerr << "Error detaching kernel driver: " << libusb_error_name(rc)
              << std::endl;
    return false;
  }
  rc = libusb_claim_interface(devh_, kInterface);
  if (rc < 0) {
    std::cerr << "Error claiming interface: " << libusb_error_name(rc)
              << std::endl;
    // TODO: shutdown
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

// Return the name of a test phase
const char *USBDevice::PhaseName(usbdev_suspend_phase_t phase) {
  switch (phase) {
    case kSuspendPhaseSuspend:
      return "Suspend";
    case kSuspendPhaseSleepResume:
      return "SleepResume";
    case kSuspendPhaseSleepReset:
      return "SleepReset";
    case kSuspendPhaseSleepDisconnect:
      return "SleepDisconnect";
    case kSuspendPhaseDeepResume:
      return "DeepResume";
    case kSuspendPhaseDeepReset:
      return "DeepReset";
    case kSuspendPhaseDeepDisconnect:
      return "DeepDisconnect";
    case kSuspendPhaseShutdown:
      return "Shutdown";
    default:
      return "<Unknown>";
  }
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

  std::cout << "Test Descriptor:" << std::endl;
  for (unsigned idx = 0u; idx < sizeof(testDesc); idx++) {
    printf("%u: 0x%02x\n", idx, testDesc[idx]);
  }

  // Validate the received test descriptor.
  const uint8_t test_sig_head[] = {0x7eu, 0x57u, 0xc0u, 0xf1u};
  const uint8_t test_sig_tail[] = {0x1fu, 0x0cu, 0x75u, 0xe7u};
  const uint8_t *dp = testDesc;
  if (!memcmp(dp, test_sig_head, 4) && 0x10u == get_le16(&dp[4]) &&
      !memcmp(&dp[12], test_sig_tail, 4)) {
    usb_testutils_test_number_t testNum =
        (usb_testutils_test_number_t)get_le16(&dp[6]);
    if (testNum != kUsbTestNumberSuspend) {
      std::cerr << "Unexpected test number: " << (unsigned)testNum << std::endl;
      return false;
    }

    // Although we needn't retain the test number, having checked it, the test
    // phase does vary and determines the actions we must perform.
    _testPhase = (usbdev_suspend_phase_t)dp[8];

    //  TODO: Retain the test arguments?
    _testArg[0] = dp[8];
    _testArg[1] = dp[9];
    _testArg[2] = dp[10];
    _testArg[3] = dp[11];

    std::cout << "Test number: " << testNum << " Test Phase: "
              << PhaseName((usbdev_suspend_phase_t)_testArg[0]) << std::endl;
    return true;
  }

  return false;
}

bool USBDevice::Delay(uint32_t time_us, bool with_traffic) {
  while (time_us > 0) {
    uint32_t delay_us = time_us;
    if (verbose_) {
      std::cout << "Delaying " << time_us << "us "
                << (with_traffic ? " - with traffic" : "no traffic")
                << std::endl;
    }
    if (with_traffic) {
      delay_us = 1000u;
      // Service streams
    }
    usleep(delay_us);
    time_us -= delay_us;
  }
  return true;
}

bool USBDevice::Reset() {
  std::cout << "Resetting Device" << std::endl;

  if (!Open()) {
    return false;
  }

  int rc = libusb_reset_device(devh_);
  if (rc < 0) {
    return false;
  }
  return true;
}

bool USBDevice::Suspend() {
  std::cout << "Suspending Device" << std::endl;

  // We need to relinquish our access to the device otherwise the kernel
  // will refuse to autosuspend the device!
  Close();

  std::string powerPath = "/sys/bus/usb/devices/" + _devPath + "/power/";
  std::string filename = powerPath + "autosuspend_delay_ms";
  // TODO: tidy this...probably move to a utility function
  int fd = open(filename.c_str(), O_WRONLY);
  if (fd < 0) {
    std::cerr << "Failed to open '" << filename << "'" << std::endl;
    std::cerr << "  (Note: this requires sudo permissions)" << std::endl;
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

  std::string powerPath = "/sys/bus/usb/devices/" + _devPath + "/power/";
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

bool USBDevice::ParseArgs(int argc, char *argv[]) {
  for (int i = 1; i < argc; i++) {
    if (argv[i][0] == '-') {
      switch (tolower(argv[i][1])) {
        case 'm':
          manual_ = true;
          break;
        case 'v':
          verbose_ = true;
          break;
        default:
          ReportSyntax();
          std::cerr << "Unrecognised/invalid option '" << argv[i] << "'"
                    << std::endl;
          return false;
      }
    }
  }
  return true;
}

void USBDevice::ReportSyntax() {
  std::cerr << "Command line syntax:\n\tusb_suspend_test [-m]" << std::endl;
}

bool USBDevice::RunTest() {
  // Repeat until the DUT indicates that the test is complete.
  bool passed = false;
  bool quit = false;
  while (!quit) {
    // Wait for a little while...
    if (ManualControl()) {
      // Await keypress
      std::cout << "Press (D)isconnect, (R)esume, (S)uspend, read (T)est "
                   "descriptor, X to reset\n"
                   "Press Q to quit\n"
                << std::endl;
      int ch = getchar();
      switch (toupper(ch)) {
        // Reset device
        // Note: this is not just a Bus Reset; it will cause the driver to
        // attempt to reinstate the previous configuration; our device-side test
        // software expects this before proceeding.
        case 'D':
          Disconnect();
          break;
        case 'Q':
          quit = true;
          break;
        case 'R':
          Resume();
          break;
        case 'S':
          Suspend();
          break;
        case 'T':
          // Read test descriptor to collect the current test phase.
          if (!ReadTestDesc()) {
            return false;
          }
          break;
        case 'X':
          Reset();
          break;
        default:
          break;
      }
    } else {
      // Read test descriptor to collect the current test phase.
      if (!ReadTestDesc()) {
        return false;
      }
      // Wait a little and then Suspend the device.
      // The device will respond to the absence of traffic (including SOF) by
      // entering a suspend state; for those test phases in which the Suspended
      // state persists for longer, the software will put the device into a
      // Sleep state.
      if (!Delay(TimeFrames(kFramesUntilSuspend)) || !Suspend()) {
        return false;
      }
      //
      switch (TestPhase()) {
        case kSuspendPhaseSleepResume:
        case kSuspendPhaseDeepResume:
          // We want to wait for the device to enter sleep...
          if (!Delay(TimeFrames(kFramesUntilSleep), false)) {
            return false;
          }
          // no break
        case kSuspendPhaseSuspend:
          if (!Delay(TimeFrames(kFramesUntilSleep + kFramesUntilResume),
                     false)) {
            return false;
          }
          // Initiate Resume Signaling.
          if (!Resume() || !Delay(TimeFrames(kFramesUntilNextPhase), true)) {
            return false;
          }
          break;
        case kSuspendPhaseSleepReset:
        case kSuspendPhaseDeepReset:
          if (!Delay(TimeFrames(kFramesUntilSleep + kFramesUntilReset),
                     false) ||
              !Reset()) {
            return false;
          }
          break;
        case kSuspendPhaseSleepDisconnect:
        case kSuspendPhaseDeepDisconnect:
          if (!Delay(TimeFrames(kFramesUntilSleep + kFramesUntilDisconnect),
                     false) ||
              !Disconnect()) {
            return false;
          }
          break;
        case kSuspendPhaseShutdown:
          passed = true;
          quit = true;
          break;
      }
    }
  }
  return passed;
}

int main(int argc, char **argv) {
  USBDevice dev;

  // Parse command line arguments
  if (!dev.ParseArgs(argc, argv)) {
    return 1;
  }

  // Initialize libusb
  int rc = libusb_init_context(&ctx, NULL, 0);
  if (rc < 0) {
    std::cerr << "Error initializing libusb: " << libusb_error_name(rc)
              << std::endl;
    return 3;
  }

  if (!dev.Open()) {
    return 2;
  }

  bool passed = dev.RunTest();

  if (!dev.ManualControl()) {
    std::cout << "Test " << (passed ? "passed" : "failed") << std::endl;
  }

  dev.Close();

  libusb_exit(ctx);

  return 0;
}
