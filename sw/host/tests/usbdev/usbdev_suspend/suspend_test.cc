// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// suspend_test
//
// Simple application that permits discovery, suspending, resuming and resetting
// of OpenTitan USB device. An approximation of connect/disconnect is available
// via control of the hub port but most hubs do not actually drop VBUS.
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

#include "usb_device.h"

static constexpr unsigned kFramesUntilSuspend = 2u;
static constexpr unsigned kFramesUntilSleep = 2u;
static constexpr unsigned kFramesUntilResume = 4u;
static constexpr unsigned kFramesUntilReset = 4u;
static constexpr unsigned kFramesUntilDisconnect = 4u;
static constexpr unsigned kFramesUntilResumed = 4u;
static constexpr unsigned kFramesUntilNextPhase = 4u;

// Parse a command line option, retrieving a byte and indicating
// success/failure.
bool GetByte(const char **pp, uint8_t &byte) {
  const char *p = *pp;
  if (isdigit(*p)) {
    uint32_t n = 0u;
    do {
      n = (n * 10) + *p++ - '0';
    } while (n < 0x100u && isdigit(*p));
    if (n < 0x100u) {
      byte = (uint8_t)n;
      *pp = p;
      return true;
    }
  }
  return false;
}

// Parse a command line option specifying the bus number and device address.
bool GetDevice(const char *p, uint8_t &busNumber, uint8_t &devAddress) {
  return GetByte(&p, busNumber) && (*p++ == ':') && GetByte(&p, devAddress) &&
         *p == '\0';
}

static void ReportSyntax() {
  std::cout
      << "Usage:\n"
      << "  suspend_test [-m][-v]\n"
      << "               [[-d<bus>:<address>] | [--device <bus>:<address>]]"
      << "\n\n"
         "   --device   programmatically specify a particular USB device by "
         "bus\n"
         "              number and device address (see 'lsusb' output).\n"
         "  -d   specify a particular USB device by bus number"
         " and device address"
      << std::endl;
}

/**
 * Parse command line arguments and retain settings.
 *
 * @param  argc       Argument count
 * @param  argv       Argument vector
 * @param  manual     Receives manual operation on/off
 * @param  verbose    Receives verbose reporting on/off
 * @param  busNumber  Receives bus number of specific USB device
 * @param  devAddress Receives device address of specific USB device
 * @return true iff command line arguments accepted.
 */
static bool ParseArgs(int argc, char *argv[], bool &manual, bool &verbose,
                      uint8_t &busNumber, uint8_t &devAddress) {
  for (int i = 1; i < argc; i++) {
    if (argv[i][0] == '-') {
      switch (tolower(argv[i][1])) {
        case 'm':
          manual = true;
          break;
        case 'v':
          verbose = true;
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

static bool RunTest(USBDevice &dev) {
  // Repeat until the DUT indicates that the test is complete.
  bool passed = false;
  bool quit = false;
  while (!quit) {
    // Wait for a little while...
    if (dev.ManualControl()) {
      // Await keypress
      std::cout
          << "Press (C)onnect, (D)isconnect, (R)esume, (S)uspend, read (T)est "
             "descriptor, X to reset\n"
             "Press Q to quit\n"
          << std::endl;
      int ch = getchar();
      switch (toupper(ch)) {
        case 'C':
          dev.Connect();
          break;
        case 'D':
          dev.Disconnect();
          break;
        case 'Q':
          quit = true;
          break;
        case 'R':
          dev.Resume();
          break;
        case 'S':
          dev.Suspend();
          break;
        case 'T':
          // Read test descriptor to collect the current test phase.
          if (!dev.ReadTestDesc()) {
            return false;
          }
          break;
        // Reset device
        // Note: this is not just a Bus Reset; it will cause the driver to
        // attempt to reinstate the previous configuration; our device-side test
        // software expects this before proceeding.
        case 'X':
          dev.Reset();
          break;
        default:
          break;
      }
    } else {
      // Read test descriptor to collect the current test phase.
      if (!dev.ReadTestDesc()) {
        return false;
      }
      // Wait a little and then Suspend the device.
      // The device will respond to the absence of traffic (including SOF) by
      // entering a suspend state; for those test phases in which the Suspended
      // state persists for longer, the software will put the device into a
      // Sleep state.
      if (!dev.Delay(dev.TimeFrames(kFramesUntilSuspend)) || !dev.Suspend()) {
        return false;
      }
      //
      switch (dev.TestPhase()) {
        case USBDevice::kSuspendPhaseSleepResume:
        case USBDevice::kSuspendPhaseDeepResume:
          // We want to wait for the device to enter sleep...
          if (!dev.Delay(dev.TimeFrames(kFramesUntilSleep), false)) {
            return false;
          }
          // no break
        case USBDevice::kSuspendPhaseSuspend:
          if (!dev.Delay(dev.TimeFrames(kFramesUntilSleep + kFramesUntilResume),
                         false)) {
            return false;
          }
          // Initiate Resume Signaling.
          if (!dev.Resume() ||
              !dev.Delay(dev.TimeFrames(kFramesUntilNextPhase), true)) {
            return false;
          }
          break;
        case USBDevice::kSuspendPhaseSleepReset:
        case USBDevice::kSuspendPhaseDeepReset:
          if (!dev.Delay(dev.TimeFrames(kFramesUntilSleep + kFramesUntilReset),
                         false) ||
              !dev.Reset()) {
            return false;
          }
          break;
        case USBDevice::kSuspendPhaseSleepDisconnect:
        case USBDevice::kSuspendPhaseDeepDisconnect:
          if (!dev.Delay(
                  dev.TimeFrames(kFramesUntilSleep + kFramesUntilDisconnect),
                  false) ||
              !dev.Disconnect()) {
            return false;
          }
          break;
        case USBDevice::kSuspendPhaseShutdown:
          passed = true;
          quit = true;
          break;
      }
    }
  }
  return passed;
}

int main(int argc, char **argv) {
  const uint16_t kVendorID = 0x18d1u;
  const uint16_t kProductID = 0x503au;
  uint8_t devAddress = 0u;
  uint8_t busNumber = 0u;
  bool verbose = false;
  bool manual = false;

  // Parse command line arguments.
  if (!ParseArgs(argc, argv, manual, verbose, devAddress, busNumber)) {
    return 1;
  }

  // Initialize libusb and open device.
  USBDevice dev(verbose, manual);
  if (!dev.Init(kVendorID, kProductID, devAddress, busNumber)) {
    return 2;
  }

  if (!dev.Open()) {
    return 2;
  }

  bool passed = RunTest(dev);

  if (!dev.ManualControl()) {
    std::cout << "Test " << (passed ? "passed" : "failed") << std::endl;
  }

  dev.Close();

  return 0;
}
