// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "usbdpi_test.h"

#include <assert.h>

#include "usbdpi.h"

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

    case kUsbTestNumberPinCfg:
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
      next_step = STEP_GET_DEVICE_DESCRIPTOR;
      break;
    // Standard device set up sequence
    case STEP_GET_DEVICE_DESCRIPTOR:
      next_step = STEP_SET_DEVICE_ADDRESS;
      break;
    // TODO: a real host issues a second Bus Reset at this point, before
    // proceeding to read the device descriptor again and then set the address.
    case STEP_SET_DEVICE_ADDRESS:
      next_step = STEP_GET_CONFIG_DESCRIPTOR;
      break;
    case STEP_GET_CONFIG_DESCRIPTOR:
      next_step = STEP_GET_FULL_CONFIG_DESCRIPTOR;
      break;
    case STEP_GET_FULL_CONFIG_DESCRIPTOR:
      next_step = STEP_SET_DEVICE_CONFIG;
      break;
      // TODO: a real host issues additional GET_DESCRIPTOR commands at
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

        // Pin configuration test need only proceed as far as reading the
        // test configuration, at which point it knows to reset the device;
        // the software detects this and proceeds to the next configuration.
        case kUsbTestNumberPinCfg:
          next_step = STEP_BUS_RESET;
          break;

        // Default behavior; usbdev_test and usbdev_pincfg_test
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
            // case STEP_READ_BAUD:
            //   next_step = STEP_SECOND_READ;
            //   break;
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
            // case STEP_TEST_ISO2:
            //   next_step = STEP_ENDPT_UNIMPL_SETUP;
            //   break;
            case STEP_ENDPT_UNIMPL_SETUP:
              next_step = STEP_ENDPT_UNIMPL_SETUP;
              break;
            case STEP_ENDPT_UNIMPL_OUT:
              next_step = STEP_ENDPT_UNIMPL_IN;
              break;
            case STEP_ENDPT_UNIMPL_IN:
              next_step = STEP_DEVICE_UK_SETUP;
              break;
            case STEP_DEVICE_UK_SETUP:
              next_step = STEP_IDLE_START;
              break;

            case STEP_IDLE_END:
              // Final resting state
              next_step = STEP_IDLE_END;
              break;

            // TODO - for now this is still required to advance through
            // the test steps
            case STEP_IDLE_START:
            case STEP_TEST_ISO2:
            case STEP_READ_BAUD:
            default:
              next_step = (usbdpi_test_step_t)((unsigned)step + 1U);
              break;
          }
          break;
      }
      break;
  }
  return next_step;
}
