// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "usbdpi_test.h"

#include <assert.h>

#include "usbdpi.h"

#define AML_HACK 1

// Timeout constants for Suspend/Resume test
//   (these may differ depending upon whether the RTL has been modified to
//    reduce the simulation time!)
#if AML_HACK
static const unsigned kSuspendTimeout = 750u;
static const unsigned kActiveInterval = 150u;
static const unsigned kSleepTimeout = 1000u;
static const unsigned kResumeInterval = 300u;
#else
static const unsigned kSuspendTimeout = 4000u;
static const unsigned kActiveInterval = 2000u;
static const unsigned kSleepTimeout = 8000u;
static const unsigned kResumeInterval = 3000u;
#endif

// Return the number of test frames required to exceed the given delay in
// microseconds; this is required to ensure that the timers in the DUT reach
// the required level to produce suspend/resume signaling etc
static const unsigned test_frames(uint32_t usecs) {
  // FRAME_INTERVAL is specified in bit intervals (1/12th us)
  return ((12u * usecs + FRAME_INTERVAL - 1) / FRAME_INTERVAL);
}

// Test-specific initialization
void usbdpi_test_init(usbdpi_ctx_t *ctx) {
  // Test-specific initialization code
  bool ok = false;
  switch (ctx->test_number) {
    case kUsbTestNumberSmoke:
      // The simple smoke test (usbdev_test) does not require any parameters
      // or special initialization at present
      ok = true;
      break;

    // Initialize streaming, or ISO streaming test
    case kUsbTestNumberMixed:
    case kUsbTestNumberIso:
    case kUsbTestNumberStreams: {
      // Number of concurrent byte streams
      const unsigned nstreams = ctx->test_arg[0] & 0xfU;
      // Poll device for IN packets in streaming test?
      bool retrieve = (ctx->test_arg[0] & 0x10U) != 0U;
      // Checking of received data against expected LFSR output
      bool checking = (ctx->test_arg[0] & 0x20U) != 0U;
      // Request retrying of IN packets, feigning error
      bool retrying = (ctx->test_arg[0] & 0x40U) != 0U;
      // Attempt to send OUT packets to device
      bool send = (ctx->test_arg[0] & 0x80U) != 0U;

      // Isochronous streams?
      bool iso = (ctx->test_number == kUsbTestNumberIso);

      if (nstreams <= USBDPI_MAX_STREAMS) {
        uint8_t xfr_types[USBDPI_MAX_STREAMS];

        // Complete the transfer types
        if (ctx->test_number == kUsbTestNumberMixed) {
          // The transfer types are specified in additional test arguments;
          // 2 bits per stream, with the USB-defined standard coding, lowest-
          // numbered stream in the LSBs.
          uint32_t mixed_types = (ctx->test_arg[3] << 16) |
                                 (ctx->test_arg[2] << 8) | ctx->test_arg[1];
          for (unsigned id = 0U; id < nstreams; id++) {
            xfr_types[id] = (mixed_types & 3U);
            // Control Transfer endpoints are not yet supported.
            assert(xfr_types[id] != USB_TRANSFER_TYPE_CONTROL);
            mixed_types >>= 2;
          }
        } else {
          // For Iso and Stream tests, all streams have the same transfer type.
          for (unsigned id = 0U; id < nstreams; id++) {
            xfr_types[id] =
                iso ? USB_TRANSFER_TYPE_ISOCHRONOUS : USB_TRANSFER_TYPE_BULK;
          }
        }
        ok = streams_init(ctx, nstreams, xfr_types, retrieve, checking,
                          retrying, send);
      }
    } break;

    // Suspend/Resume/Disconnect/Reconnect test
    case kUsbTestNumberSuspend:
      // This test iterates through a number of phases, performing a bus reset
      // and reinitializing the device each time; OTTF test software supplies
      // the test phase in a modified per-phase test descriptor
      ctx->test_phase = (usbdev_suspend_phase_t)ctx->test_arg[0];
      ok = true;
      break;

    // Exceptional Traffic test
    case kUsbTestNumberExc:
      // No test arguments at present
      ok = true;
      break;

    default:
      assert(!"Unrecognised/unsupported test in USBDPI");
      break;
  }

  // TODO - commute this to a proper test failure at run time
  assert(ok);
}

// Return the next step in the test sequence
usbdpi_test_step_t usbdpi_test_seq_next(usbdpi_ctx_t *ctx,
                                        usbdpi_test_step_t step) {
  // Default to disconnecting and stopping
  usbdpi_test_step_t next_step = STEP_BUS_DISCONNECT;

  switch (step) {
    // Bus reset (VBUS newly present...)
    case STEP_BUS_RESET:
      next_step = STEP_SET_DEVICE_ADDRESS;
      break;
    // Standard device set up sequence
    case STEP_SET_DEVICE_ADDRESS:
      next_step = STEP_GET_DEVICE_DESCRIPTOR;
      break;
    case STEP_GET_DEVICE_DESCRIPTOR:
      next_step = STEP_GET_CONFIG_DESCRIPTOR;
      break;
    case STEP_GET_CONFIG_DESCRIPTOR:
      next_step = STEP_GET_FULL_CONFIG_DESCRIPTOR;
      break;
    case STEP_GET_FULL_CONFIG_DESCRIPTOR:
      next_step = STEP_SET_DEVICE_CONFIG;
      break;
      // TODO - a real host issues additional GET_DESCRIPTOR commands at
      // this point, reading device qualifier and endpoint information

    case STEP_SET_DEVICE_CONFIG:
      next_step = STEP_GET_TEST_CONFIG;
      break;

    case STEP_SET_TEST_STATUS:
      next_step = STEP_BUS_DISCONNECT;
      break;

    case STEP_BUS_DISCONNECT:
      // deassert VBUS
      ctx->driving &= ~P2D_SENSE;
      break;

    // At this point we have discovered which test we are to perform
    default:
      switch (ctx->test_number) {
        // Streaming test (usbdev_stream_test), Iso (usbdev_iso_test) and
        // Mixed (usbdev_mixed_test)
        case kUsbTestNumberMixed:
        case kUsbTestNumberIso:
        case kUsbTestNumberStreams:
          switch (step) {
            case STEP_GET_TEST_CONFIG:
              next_step = STEP_STREAM_SERVICE;
              break;

            default:
              // The single state that keeps aggressively polling for IN
              // packets, processing them and pushing them OUT to the
              // device. The device test software is responsible for
              // terminating the test and reporting its status
              next_step = STEP_STREAM_SERVICE;
              break;
          }
          break;

        // Suspend/Resume/Disconnect/Reconnect testing
        case kUsbTestNumberSuspend:
          switch (step) {
            case STEP_GET_TEST_CONFIG:
              if (ctx->test_phase) {
                next_step = STEP_SUSPEND_LONG;
              } else {
                next_step = STEP_SUSPEND;
              }
              ctx->substep = 0u;
              break;

            // Must remain in SUSPEND for 4ms for the Suspend detection, and
            // this is presently a variable number of (simulated) bus frames
            case STEP_SUSPEND:
              if (++ctx->substep >= test_frames(kSuspendTimeout)) {
                next_step = STEP_ACTIVE;
                ctx->substep = 0u;
              } else {
                next_step = STEP_SUSPEND;
              }
              break;

            case STEP_ACTIVE:
              if (++ctx->substep >= test_frames(kActiveInterval)) {
                next_step = STEP_BUS_RESET;
              } else {
                next_step = STEP_ACTIVE;
              }
              break;

            // Must remain in SUSPEND_LONG for 8ms for Suspend detection and
            // then the test code to go to sleep, and this is presently a
            // variable number of (simulated) bus frames
            case STEP_SUSPEND_LONG:
              if (++ctx->substep >= test_frames(kSleepTimeout)) {
                switch (ctx->test_phase) {
                  // Leave Suspended state by Resume Signaling
                  case kSuspendPhaseSleepActivity:
                  case kSuspendPhaseDeepActivity:
                    next_step = STEP_RESUME;
                    break;

                  // Leave Suspended state by Bus Reset
                  case kSuspendPhaseSleepReset:
                  case kSuspendPhaseDeepReset:
                    next_step = STEP_BUS_RESET;
                    break;

                  // Leave Suspended state by Disconnection
                  default:
                    assert(ctx->test_phase == kSuspendPhaseDeepDisconnect);
                    // no break
                  case kSuspendPhaseSleepDisconnect:
                    next_step = STEP_BUS_DISCONNECT;
                    break;
                }
                ctx->substep = 0u;
              } else {
                next_step = STEP_SUSPEND_LONG;
              }
              break;

            case STEP_RESUME:
              if (++ctx->substep >= test_frames(kResumeInterval)) {
                // Advance the test phase
                switch (ctx->test_phase) {
                  case kSuspendPhaseSleepActivity:
                    ctx->test_phase = kSuspendPhaseSleepReset;
                    break;
                  default:
                    assert(ctx->test_phase == kSuspendPhaseDeepActivity);
                    ctx->test_phase = kSuspendPhaseDeepReset;
                    break;
                }
                // Disconnect the device to signal successful test completion
                next_step = STEP_SUSPEND_LONG;
              } else {
                next_step = STEP_RESUME;
              }
              break;

            default:
              // TODO: any more states that we need to cover here?
              break;
          }
          break;

        case kUsbTestNumberExc:
          // Test exceptional bus traffic such as accesses to invalid endpoints,
          // generation of Request Errors...
          switch (step) {
            case STEP_GET_TEST_CONFIG:
              next_step = STEP_ENDPT_UNIMPL_SETUP;
              break;

            // Test each of SETUP, IN and OUT to an unimplemented endpoint;
            // traffic shall be ignored
            case STEP_ENDPT_UNIMPL_SETUP:
              next_step = STEP_ENDPT_UNIMPL_OUT;
              break;
            case STEP_ENDPT_UNIMPL_OUT:
              next_step = STEP_ENDPT_UNIMPL_IN;
              break;
            case STEP_ENDPT_UNIMPL_IN:
              next_step = STEP_DEVICE_UK_SETUP;
              break;
            // Test traffic to a different device address
            case STEP_DEVICE_UK_SETUP:
              next_step = STEP_UK_SETUP_REQ;
              break;

            // Test unknown Setup Request (software-defined behavior, but it
            // should request STALLing)
            case STEP_UK_SETUP_REQ:
            case STEP_SUSPEND:
              // Final resting state
              next_step = STEP_SUSPEND;
              break;

            default:
              break;
          }
          break;

        // Default behavior; usbdev_test
        default:
          // TODO - for now we're just maintaining the existing timing
          // sequence
          switch (step) {
            case STEP_GET_TEST_CONFIG:
              next_step = STEP_FIRST_READ;
              break;

            case STEP_FIRST_READ:
              next_step = STEP_READ_BAUD;
              break;
            case STEP_READ_BAUD:
              next_step = STEP_SECOND_READ;
              break;
            case STEP_SECOND_READ:
              next_step = STEP_SET_BAUD;
              break;
            case STEP_SET_BAUD:
              next_step = STEP_THIRD_READ;
              break;
            case STEP_THIRD_READ:
              next_step = STEP_TEST_ISO1;
              break;

            case STEP_TEST_ISO1:
              next_step = STEP_TEST_ISO2;
              break;
            case STEP_TEST_ISO2:
            case STEP_SUSPEND:
              // Final resting state
              next_step = STEP_SUSPEND;
              break;

            default:
              break;
          }
          break;
      }
      break;
  }
  return next_step;
}
