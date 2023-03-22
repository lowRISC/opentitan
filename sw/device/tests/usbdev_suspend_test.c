// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB suspend/resume test
//
// Basic test of suspend/resume signaling and disconnect/reconnect behavior.
// The DPI model sets up the device largely for the purpose of reading the test
// configuration. Having ascertained the specific testing behavior that is
// required, it then proceeds to
//
//-----------------------------------------------------------------------------
// Test state flow
//-----------------------------------------------------------------------------
//
// [PhaseSuspend]
//
// Power On Reset -> Configuration -> DPI drops SOF -> Suspend -> Resume ->
//                -> DPI performs Bus Reset ...
//
// Three 'Normal Sleep' phases may be started from Power On Reset (to aid dev),
// or a Bus Reset if that a Bus Reset or Disconnect was the most recent wake
// stimulus. If that wake stimulus was Resume Signaling, then configuration does
// not occur again.
//
// [PhaseSleepAcivity]
// [PhaseSleepReset]
// [PhaseSleepDisconnect]
//
//  ... Bus Reset ->
// Power On Reset -> Configuration ->
//                 [from prev] ... -> DPI drops SOF -> Suspend -> Activate AON
//                -> Normal Sleep -> DPI produces wake stimulus -> Resume
//                -> Deactivate AON ... [to next]
//
// [PhaseDeepActivity]
// [PhaseDeepReset]
// [PhaseDeepDisconnect]
//
//  ... Bus Reset ->
// Power On Reset -> Configuration ->
//                 [from prev] ... -> DPI drops SOF -> Suspend -> Actvivate AON
//                -> Deep Sleep -> DPI produces wake stimulus -> Resume
//                -> Deactivate AON .. [to next]
//
// Test Complete
//
//-----------------------------------------------------------------------------


//-----------------------------------------------------------------------------
// Summary notes from USB 2.0 Specification to aid apprehension (see the spec.
// itself for details):
// 
// Device starts transitioning to the Suspend state after observing a constant
// Idle state on bus for more than 3.0ms, and must be in Suspend state after no
// more than 10ms of bus inactivity. Pull-up resistor must remain asserted.
//
// Resuming from Suspend state is achieved by the host at any time by any non-
// signaling, for at leasat 20ms. This is followed by a standard, low-speed EOP
// (two low-speed bit times of SE0 followed by a J). Traffic, even if only SOF,
// must be resumed within 3ms after entering the Idle state (J), to prevent
// the device re-entering Suspend.
// Additionally, the host must provide a 10ms resume recovery time during which
// it will not attempt to access the device.
//
// Suspending/Resuming may occur from any Device State (Powered, Default,
// Address or Configured), and the device returns to its pre-Suspend state.
//-----------------------------------------------------------------------------

#include <inttypes.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/usb_testutils.h"
#include "sw/device/lib/testing/usb_testutils_controlep.h"
#include "sw/device/lib/testing/usb_testutils_streams.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "sw/device/lib/testing/autogen/isr_testutils.h"

// Are we expecting a full frame interval?
// TODO: this must match the setting in the DPI model, but we do not have the
// ability to share header files.
// TODO: also note that this shall always be 1 for physical hosts.
#define FULL_FRAME 1

#if FULL_FRAME
#define USBDPI_FRAME_INTERVAL 1000  // 1ms frame time
#else
#define USBDPI_FRAME_INTERVAL 500  // 0.5ms
#endif

/**
 * Timeout constants in microseconds;
 */
#define TIMEOUT_RESUME_MISSED 4500u
// #define TIMEOUT_

#define TIMEOUT_WAKEUP_RESUME 3000u
#define TIMEOUT_FINISH_MISSED 2000u

/**
 * Durations that are specified in terms of bus frames, however long those
 * simulated bus frames happen to be (ie. these intervals are determined by
 * the DPI host behavior rather than the USB protocol specification)
 */
#define FRAMES_INITIATE_SUSPEND 4u

#define FRAMES_INITIATE_RESUME 4u

#define FRAMES_LONG_SUSPEND 8u

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
  kSuspendPhaseSleepActivity,
  /*
   * The AON/Wakeup module will cause us to awaken in response to a bus reset.
   */
  kSuspendPhaseSleepReset,
  /**
   * As above, but this time we're expecting a VBUS/SENSE loss.
   */
  kSuspendPhaseSleepDisconnect,
  /**
   * Mirrors activity detection for normal sleep, but this time we enter Deep
   * Sleep and the power is removed too.
   */
  kSuspendPhaseDeepActivity,
  /**
   * Mirrors Bus Reset detection for normal sleep, but this time we enter Deep
   * Sleep and the power is removed too.
   */
  kSuspendPhaseDeepReset,
  /**
   * As above, but this time we're expecting a VBUS/SENSE loss.
   */
  kSuspendPhaseDeepDisconnect,
} usbdev_suspend_phase_t;

/**
 * Test states
 */
typedef enum {
  kSuspendTestReset = 0u,
  /**
   * Waiting for the DPI/Host to suspend the device, for normal Suspend/Resume
   * behavior, not involving AON/Wakeup functionality.
   */
  kSuspendTestWaitSuspend,
  kSuspendTestWaitResume,
  kSuspendTestWaitBusReset,
  /**
   * Waiting for the DPI/Host to suspend the device, expecting a longer suspend
   * period, during which we put the device into Normal/Deep Sleep using the
   * AON/Wakeup functionality.
   */
  kSuspendTestWaitLongSuspend,
  /**
   *
   */
  kSuspendTestWaitSuspendTimeout,
  /**
   * We have instructed the AON/Wakeup module to wake over control of the USB
   * signals; it does not do so immediately...
   */
  kSuspendTestActivatedAON,
  kSuspendTestPowerdown,
  kSuspendTestAONWakeup,
  kSuspendTestWaitResumeTimeout,
  kSuspendTestWaitFinish,
  kSuspendTestComplete,
  kSuspendTestFailed,
} usbdev_suspend_test_state_t;

/**
 * Test context
 */
typedef struct usbdev_suspend_ctx {
  /**
   * Access to usb_testutils context
   */
  usb_testutils_ctx_t *usbdev;
  /**
   * Current test state
   */
  usbdev_suspend_test_state_t test_state;
  /**
   * Current test phase
   */
  usbdev_suspend_phase_t test_phase;
  /**
   * Timeout catching any failure of test to advance as expected
   */
  ibex_timeout_t timeout;
  /**
   * Most recent status of wakeup monitor
   */
  dif_usbdev_wake_status_t wake_status;
  /**
   * Test descriptor for current test phase
   */
  uint8_t test_dscr[USB_TESTUTILS_TEST_DSCR_LEN];
} usbdev_suspend_ctx_t;

/**
 * Retained state; to be held in the Retention SRAM during Deep Sleep
 */
typedef struct {
  /**
   * Host-suppplied device address on the USB.
   */
  uint8_t dev_address;
  /**
   * Selected device configuration number.
   */
  uint8_t dev_config;
  /**
   * Test phase.
   */
  uint8_t test_phase;
} usbdev_retn_state_t;

/**
 * Configuration values for USB.
 */
static const uint8_t config_descriptors[] = {
    USB_CFG_DSCR_HEAD(
        USB_CFG_DSCR_LEN + 2 * (USB_INTERFACE_DSCR_LEN + 2 * USB_EP_DSCR_LEN),
        2),
    VEND_INTERFACE_DSCR(0, 2, 0x50, 1),
    USB_BULK_EP_DSCR(0, 1, 32, 0),
    USB_BULK_EP_DSCR(1, 1, 32, 4),
    VEND_INTERFACE_DSCR(1, 2, 0x50, 1),
    USB_BULK_EP_DSCR(0, 2, 32, 0),
    USB_BULK_EP_DSCR(1, 2, 32, 4),
};

/**
 * USB device context types.
 */
static usb_testutils_ctx_t usbdev;
static usb_testutils_controlep_ctx_t usbdev_control;
static usb_testutils_streams_ctx_t usbdev_streams;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;
/**
 * Rstmgr handle
 */
static dif_rstmgr_t rstmgr;
/**
 * Pwrmgr handle
 */
static dif_pwrmgr_t pwrmgr;
/**
 * Interrupt controller handle
 */
static dif_rv_plic_t rv_plic;
/**
 * Shall we perform streaming traffic simultaneously?
 */
static bool with_traffic = true;
/**
 * Do we expect this host to put the device into suspend?
 */
static bool host_suspends = true;
/**
 * Do we expect the device to remember over a deep sleep?
 *
 * TODO: this is JUST for bring up; we rely upon the host to reconfigure the
 * device upon reconnection in this case.
 */
static const bool device_remembers = false;
/**
 * Verbose logging? Mostly useful on FPGA; be warned that it can affect
 * timing in simulation, and in particular will likely break Verilator simus.
 */
static bool verbose = false;
/**
 * Initial phase of test
 *   (this should be kSuspendPhaseSuspend normally, to run all phases in
 *    sequence, but it can be useful to advance it manually during development).
 */
static const usbdev_suspend_phase_t init_phase = kSuspendPhaseSuspend;
//static const usbdev_suspend_phase_t init_phase = kSuspendPhaseSleepReset;
//static const usbdev_suspend_phase_t init_phase = kSuspendPhaseSleepDisconnect;
//static const usbdev_suspend_phase_t init_phase = kSuspendPhaseDeepReset;
//static const usbdev_suspend_phase_t init_phase = kSuspendPhaseDeepDisconnect;

static plic_isr_ctx_t plic_ctx = {.rv_plic = &rv_plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};

static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

// Configuration for streaming layer; we'll just have a couple of Bulk transfer
// streams with traffic and checking in both directions. More involved
// configurations are exercised in other tests.
static const unsigned nstreams = 2U;
static const usb_testutils_transfer_type_t xfr_types[] = {kUsbTransferTypeBulk,
                                                          kUsbTransferTypeBulk};
// Full traffic and checking
static const usbdev_stream_flags_t test_flags =
    kUsbdevStreamFlagRetrieve | kUsbdevStreamFlagCheck |
    kUsbdevStreamFlagRetry | kUsbdevStreamFlagSend;
// We don't expect it to complete; data transfer is exercised and checked in
// other tests.
static const uint32_t transfer_bytes = 0x100 << 20;

// Monotonic time in microseconds
// static uint32_t time_now(void) {
//  uint64_t now = ibex_mcycle_read();
//}

// Return the duration of 'n' bus frames in microseconds
// static uint32_t time_frames(unsigned n) { return n * USBDPI_FRAME_INTERVAL; }

// Return a timeout in microseconds, scaled for the test target; longer timeout
// periods are more appropriate for FPGA tests and decidedly undesirable for
// Verilator top-level simulations
static uint32_t time_frames(unsigned n) {
  uint32_t scale = 1u;
  switch (kDeviceType) {
    case kDeviceFpgaCw310:
      //      scale = 20u;
      scale = 1000u;
      break;
    default:
      break;
  }
  return scale * n * USBDPI_FRAME_INTERVAL;
}

// Return the name of a test phase
static const char *phase_name(usbdev_suspend_phase_t phase) {
  switch (phase) {
    case kSuspendPhaseSuspend:
      return "Suspend";
    case kSuspendPhaseSleepActivity:
      return "SleepActivity";
    case kSuspendPhaseSleepReset:
      return "SleepReset";
    case kSuspendPhaseSleepDisconnect:
      return "SleepDisconnect";
    case kSuspendPhaseDeepActivity:
      return "DeepActivity";
    case kSuspendPhaseDeepReset:
      return "DeepReset";
    case kSuspendPhaseDeepDisconnect:
      return "DeepDisconnect";
    default:
      return "<Unknown>";
  }
}

// Return the name of a test state
static const char *state_name(usbdev_suspend_test_state_t state) {
  switch (state) {
    case kSuspendTestReset:
      return "Reset";
    case kSuspendTestWaitSuspend:
      return "Suspend";
    case kSuspendTestWaitResume:
      return "Resume";
    case kSuspendTestWaitBusReset:
      return "BusReset";
    case kSuspendTestWaitLongSuspend:
      return "LongSuspend";
    case kSuspendTestWaitSuspendTimeout:
      return "SuspendTimeout";
    case kSuspendTestActivatedAON:
      return "ActivatedAON";
    case kSuspendTestPowerdown:
      return "Powerdown";
    case kSuspendTestAONWakeup:
      return "AONWakeup";
    case kSuspendTestWaitResumeTimeout:
      return "ResumeTimeout";
    case kSuspendTestWaitFinish:
      return "WaitFinish";
    case kSuspendTestComplete:
      return "Complete";
    case kSuspendTestFailed:
      return "Failed";
    default:
      return "<Unknown>";
  }
}

// Transition to a (new) test state
static void state_enter(usbdev_suspend_ctx_t *ctx,
                        usbdev_suspend_test_state_t state) {
  if (verbose) {
    LOG_INFO("entering state %s", state_name(state));
  }
  ctx->test_state = state;
}

// Set a time out for the current test state
static void timeout_set(usbdev_suspend_ctx_t *ctx, uint32_t interval_us) {
  if (verbose) {
    uint64_t now = ibex_mcycle_read();
    uint64_t then = now + interval_us;
    LOG_INFO("setting timeout to 0x%x%x (at 0x%x%x)", (uint32_t)(then >> 32),
             (uint32_t)then, (uint32_t)(now >> 32), (uint32_t)now);
  }
  ctx->timeout = ibex_timeout_init(interval_us);
}

// Set a time out, in frames, for the current test state
static void timeout_frames_set(usbdev_suspend_ctx_t *ctx,
                               uint32_t interval_frames) {
  timeout_set(ctx, time_frames(interval_frames));
}

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  dif_pwrmgr_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);
  if (verbose) {
    LOG_INFO("Received IRQ in normal sleep");
  }

  // Check that both the peripheral and the irq id is correct
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}

static void test_phase_set(usbdev_suspend_ctx_t *ctx,
                           usbdev_suspend_phase_t phase) {
  /**
   * Test descriptor; indicates to the DPI model that we're interested in
   * testing bus Suspend/Resume signaling, Reset signaling and Remote Wakeup
   * behavior.
   */

  if (verbose) {
    LOG_INFO("test_phase_set %u", phase);
  }
  uint8_t test_descriptor[] = {USB_TESTUTILS_TEST_DSCR(kUsbTestNumberSuspend,
                                                       phase,  // Test phase
                                                       0, 0, 0)};

  memcpy(ctx->test_dscr, test_descriptor, sizeof(ctx->test_dscr));
}

// Callback handler for link events
static status_t link_callback(void *ctx_v,
                              dif_usbdev_irq_state_snapshot_t snapshot,
                              dif_usbdev_link_state_t link_state) {
  usbdev_suspend_ctx_t *ctx = (usbdev_suspend_ctx_t *)ctx_v;

  if (snapshot & (1u << kDifUsbdevIrqFrame)) {
    if (verbose) {
      // For FPGA testing, we deliberately extend all of the timeout periods to
      // make the activity viewable. This is therefore just an indication of
      // activity/progress.
      static int hb = 0;
      if (++hb > 1000) {
        LOG_INFO("SOF");
        hb = 0;
      }
    }

    // TODO: We are supplied with the SOF interrupts to help inform our decision
    //  but these are normally much too frequent to be reporting them
    snapshot &= ~(1u << kDifUsbdevIrqFrame);
  }

  // Report connection/reset events
  if (snapshot &
      ((1u << kDifUsbdevIrqPowered) | (1u << kDifUsbdevIrqDisconnected))) {
    LOG_INFO("VBUS: %sonnected",
             (link_state == kDifUsbdevLinkStateDisconnected) ? "Disc" : "C");
  }
  if (snapshot & (1u << kDifUsbdevIrqLinkReset)) {
    LOG_INFO("Link reset");
  }
  if (snapshot & (1u << kDifUsbdevIrqHostLost)) {
    LOG_INFO("Host lost");
  }

  // Report suspend/resume status changes
  if (snapshot &
      ((1u << kDifUsbdevIrqLinkSuspend) | (1u << kDifUsbdevIrqLinkResume))) {
    switch (link_state) {
      case kDifUsbdevLinkStatePoweredSuspended:
      case kDifUsbdevLinkStateSuspended:
        LOG_INFO("Suspended");
        break;

      case kDifUsbdevLinkStateResuming:
        LOG_INFO("Resuming");
        break;

      case kDifUsbdevLinkStateActiveNoSof:
        LOG_INFO("Resuming no SOF");
        break;

      case kDifUsbdevLinkStateActive:
        LOG_INFO("Resumed");
        break;

      default:
        break;
    }
  }

  // State machine anticipates the behavior of the host/DPI model, checking that
  // the expected events are reported within the expected time intervals, and
  // advances accordingly through the test states.

  switch (ctx->test_state) {
    case kSuspendTestReset:
      break;

    // We're expecting the host to drop the SOF heartbeat indicating that we
    // should suspend... (STEP_IDLE_)
    case kSuspendTestWaitSuspend:
      if (snapshot & (1u << kDifUsbdevIrqLinkSuspend)) {
        timeout_set(ctx, TIMEOUT_RESUME_MISSED);
        state_enter(ctx, kSuspendTestWaitResume);
      }
      break;

    // After a short delay, the host should resume automatically...
    // (STEP_ACTIVE_)
    case kSuspendTestWaitResume:
      if (snapshot & (1u << kDifUsbdevIrqLinkResume)) {
        state_enter(ctx, kSuspendTestWaitBusReset);
      }
      break;

    // A bus reset is performed by the host before it then sets up the device
    // again
    case kSuspendTestWaitBusReset:
      if (snapshot & (1u << kDifUsbdevIrqLinkReset)) {
        // The first test phase (Suspend/Resume without AON/Wakeup involvement)
        // is terminated by a deliberate Bus Reset, advancing us to the next
        // phase.
        if (ctx->test_phase == kSuspendPhaseSuspend) {
          // After the deliberate bus reset from the DPI/Host we shall return a
          // modified test descriptor that instructs the DPI model to enter a
          // different test phase...
          test_phase_set(ctx, kSuspendPhaseSleepReset);
        }
        state_enter(ctx, kSuspendTestReset);
      }
      break;

    // This time we're expecting a much longer Suspend...
    case kSuspendTestWaitLongSuspend:
      if (snapshot & (1u << kDifUsbdevIrqLinkSuspend)) {
        timeout_frames_set(ctx, FRAMES_LONG_SUSPEND);
        state_enter(ctx, kSuspendTestWaitSuspendTimeout);
      }
      break;

    // We're _waiting for a timeout_ to occur, so we're not expecting any
    // events at this point...
    case kSuspendTestWaitSuspendTimeout:
      if (snapshot) {
        // TODO:
        state_enter(ctx, kSuspendTestFailed);
      }
      break;

    case kSuspendTestActivatedAON:
      // TODO: should respond to a resume event, and seize back control!
      break;
    case kSuspendTestPowerdown:
      break;
    case kSuspendTestAONWakeup:
      break;

    case kSuspendTestWaitResumeTimeout:
      break;

    case kSuspendTestWaitFinish:
      // We've resumed, we're just waiting for the host to perform some simple
      // traffic and then disconnect to signal test completion
      if (snapshot & (1u << kDifUsbdevLinkStateDisconnected)) {
        state_enter(ctx, kSuspendTestComplete);
      }
      break;

    case kSuspendTestFailed:
      break;

    default:
      LOG_INFO("Unknown/invalid test state %u (%s)", ctx->test_state,
               state_name(ctx->test_state));
      state_enter(ctx, kSuspendTestFailed);
      break;
  }

  return OK_STATUS();
}

// TODO: redirect logging information in Verilator t-l sim because any attempt
// to use the UART will introduce long delays and break the test.
static size_t base_dev_uart(void *data, const char *buf, size_t len) {
  for (size_t i = 0; i < len; ++i) {
    *(uint32_t *)0x411f0084 = ((uint8_t *)buf)[i];
  }
  return len;
}
static buffer_sink_t base_stdout = {
    .data = NULL,
    // Note: Using `&base_dev_null` causes this variable to be placed in the
    // .data section and triggers the assertion in rom.ld.
    .sink = base_dev_uart,
};

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  usbdev_suspend_ctx_t ctx;

//  CHECK(kDeviceType == kDeviceSimVerilator || kDeviceType == kDeviceSimDV ||
//            kDeviceType == kDeviceFpgaCw310,
//        "This test is not expected to run on platforms other than the "
//        "Verilator simulation or CW310 FPGA. It needs the USB DPI model "
//        "or host application.");

  LOG_INFO("Running USBDEV_SUSPEND test");

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  switch (kDeviceType) {
    case kDeviceSimVerilator:
      // steal the UART output and send it via a faster mechanism
      base_set_stdout(base_stdout);
      // no break
    // Do NOT steal the UART output in this case because DVsim has a back door
    // for rapid logging.
    case kDeviceSimDV:
      // DPI model performs suspend/resume signaling in response to reading our
      // test description.
      host_suspends = true;

      // DPI model can perform traffic and will deliberately avoid performing
      // traffic during the periods when it stops sending the bus frames
      with_traffic = true;
      break;

    // We do NOT rely upon the physical host to suspend our device.
    default:
      host_suspends = false;
      with_traffic = false;
      // Presently, the FPGA build is expected to be observed/monitored by a
      // developer, so verbose reporting is appropriate.
      verbose = true;
      break;
  }

  // TODO: let's learn to walk first
  with_traffic = false;

  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  // Initialize pwrmgr.
  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  // Initialize the PLIC.
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &rv_plic));

  // Initialize rstmgr
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&rv_plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);

  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(&pwrmgr, kDifPwrmgrReqTypeWakeup,
                                              kDifPwrmgrWakeupRequestSourceFour,
                                              kDifToggleEnabled));

  // Enable pwrmgr interrupt.
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Check if there was a HW reset caused by the wdog bite.
  dif_rstmgr_reset_info_bitfield_t rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  // Initialize testing context and state machine
  ctx.usbdev = &usbdev;

  if (rst_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time");
    test_phase_set(&ctx, init_phase);
    state_enter(&ctx, kSuspendTestReset);
  } else {
    LOG_INFO("Resuming from power down!");
    // Recover state from the retention RAM

    // TODO: we need the device address, and the test phase
//    test_phase_set(&ctx, kSuspendPhaseSleepReset);
//    test_phase_set(&ctx, kSuspendPhaseSleepDisconnect);
//    test_phase_set(&ctx, kSuspendPhaseDeepReset);
//    test_phase_set(&ctx, kSuspendPhaseDeepDisconnect);

    state_enter(&ctx, kSuspendTestPowerdown);
  }

  do {
    // Call `usbdev_init` here so that DPI will not start until the
    // simulation has finished all of the printing, which takes a while
    // if `--trace` was passed in.
    CHECK_STATUS_OK(usb_testutils_init(ctx.usbdev, /*pinflip=*/false,
                                       /*en_diff_rcvr=*/false,
                                       /*tx_use_d_se0=*/false));

    // Register our interest in link events
    CHECK_STATUS_OK(
        usb_testutils_link_callback_register(ctx.usbdev, link_callback, &ctx));

    // Set up Endpoint Zero for Control Transfers, at which point the interface
    // becomes enabled and we must be responsive to USB traffic.
    CHECK_STATUS_OK(usb_testutils_controlep_init(
        &usbdev_control, ctx.usbdev, 0, config_descriptors,
        sizeof(config_descriptors), ctx.test_dscr, sizeof(ctx.test_dscr)));

    if (ctx.test_state == kSuspendTestPowerdown && device_remembers) {
      // TODO: pick up the device address from retention RAM
      // Collect the device address from the magician's hat! We happen to know
      // that our DPI model always sets address 2
      const uint8_t dev_address = 2U;

      // NOTE: We've run through the usb_testutils/controlep_init sequence as
      // normal because this sets up our endpoints as they were before, whilst
      // requiring less information to be stored in the retention RAM, but we
      // must still reinstate the device address.
      CHECK_DIF_OK(dif_usbdev_address_set(ctx.usbdev->dev, dev_address));

      // TODO: the controlep state needs to be forced to configured.
      usbdev_control.device_state = kUsbTestutilsDeviceConfigured;
      usbdev_control.usb_config = 1U;
      usbdev_control.new_dev = dev_address;

      // TODO: do we need to restore any other information?
    } else {
      // In this case, since we have no retention RAM, we must wait until the
      // host has reconfigured us.
      while (usbdev_control.device_state != kUsbTestutilsDeviceConfigured) {
        CHECK_STATUS_OK(usb_testutils_poll(ctx.usbdev));
      }
    }

    // TODO: streaming code has now been integrated, but it would probably be
    // quite useful to be able to see the device streaming activity too, not
    // just that of the host side?

    if (with_traffic) {
      // Initialise the state of the streams
      CHECK_STATUS_OK(usb_testutils_streams_init(&usbdev_streams, nstreams,
                                                 xfr_types, transfer_bytes,
                                                 test_flags, verbose));

      if (verbose) {
        LOG_INFO("Configured; starting streaming...");
      }
    } else {
      if (verbose) {
        LOG_INFO("Configured; not trying to stream...");
      }
    }

    // Enter the appropriate starting state based upon the test phase
    switch (ctx.test_phase) {
      case kSuspendPhaseSuspend:
        state_enter(&ctx, kSuspendTestWaitSuspend);
        break;

      default:
        CHECK(ctx.test_phase == kSuspendPhaseDeepDisconnect);
        // no break
      case kSuspendPhaseDeepReset:
      case kSuspendPhaseDeepActivity:
      case kSuspendPhaseSleepReset:
      case kSuspendPhaseSleepDisconnect:
        if (init_phase == ctx.test_phase) {
          // If we've started in this test phase - a development aid to shorten
          // the test - then we should not expect resume signaling
          state_enter(&ctx, kSuspendTestWaitLongSuspend);
        } else {
          state_enter(&ctx, kSuspendTestWaitResumeTimeout);
        }
        break;
    }

    // Initialize timeout to catch any failure of the host to suspend the bus
    timeout_frames_set(&ctx, FRAMES_INITIATE_SUSPEND);

    // The DPI model and our callback handler for USB link events do most of the
    // work of walking through the test states until completion
    while (ctx.test_state != kSuspendTestComplete &&
           ctx.test_state != kSuspendTestFailed &&
           ctx.test_state != kSuspendTestReset) {

      if (with_traffic) {
        // Servicing streams handles usbdev/testutils events for us.
        CHECK_STATUS_OK(usb_testutils_streams_service(&usbdev_streams));
      } else {
        // No traffic, but we must still poll the usb_testutils layer to handle
        // hardware events and callbacks.
        CHECK_STATUS_OK(usb_testutils_poll(ctx.usbdev));
      }

      ///////////////////////////////////////////////////////////////////
      // Time out handling
      ///////////////////////////////////////////////////////////////////

      if (ibex_timeout_check(&ctx.timeout)) {
        switch (ctx.test_state) {
          // Timeout is required to advance from the longer suspend state because
          // we're not expecting any host activity in this case, but must initiate
          // sleep/powerdown
          case kSuspendTestWaitSuspendTimeout:
            LOG_INFO("set_wake_enable...");
            timeout_frames_set(&ctx, 1u);
            state_enter(&ctx, kSuspendTestActivatedAON);

            CHECK_DIF_OK(
                dif_usbdev_set_wake_enable(ctx.usbdev->dev, kDifToggleEnabled));
            break;

          // Timeout
          case kSuspendTestWaitResumeTimeout:
            // TODO: force link state resume to active?
            CHECK_DIF_OK(dif_usbdev_resume_link_to_active(ctx.usbdev->dev));

            timeout_frames_set(&ctx, TIMEOUT_FINISH_MISSED);
            state_enter(&ctx, kSuspendTestWaitFinish);
            break;

          case kSuspendTestPowerdown:
            // TODO: just sit here for now?!
            break;

          // Timeout may also be required to advance from Wait(Long)Suspend if the
          // host does not attempt to suspend the device, in which case we shall
          // also need to transition from WaitResume automatically...
          case kSuspendTestWaitBusReset:
          case kSuspendTestWaitResume:
          case kSuspendTestWaitSuspend:
          case kSuspendTestWaitLongSuspend:
            if (!host_suspends) {
              bool failed = false;
              switch (ctx.test_state) {
                case kSuspendTestWaitSuspend:
                  LOG_INFO("auto-suspending");
                  timeout_frames_set(&ctx, FRAMES_INITIATE_RESUME);
                  state_enter(&ctx, kSuspendTestWaitResume);
                  break;

                case kSuspendTestWaitResume:
                  LOG_INFO("auto-resuming");
                  state_enter(&ctx, kSuspendTestWaitBusReset);
                  // TODO: we shalln't get a bus reset without provoking it, but
                  // we can do that!
                  break;

                case kSuspendTestWaitLongSuspend:
                  LOG_INFO("auto-long-suspending");
                  timeout_frames_set(&ctx, FRAMES_LONG_SUSPEND);
                  state_enter(&ctx, kSuspendTestWaitSuspendTimeout);
                  break;

                case kSuspendTestWaitBusReset:
                  LOG_INFO("auto-resetting");
                  // This will disconnect us from the bus.
                  CHECK_STATUS_OK(usb_testutils_fin(ctx.usbdev));
                  state_enter(&ctx, kSuspendTestReset);
                  break;

                default:
                  failed = true;
                  break;
              }
              if (!failed) {
                break;
              }
            }
            // no break

          // Any other timeout implies that we did not receive the expected link
          // event promptly and the test has failed
          default:
            LOG_INFO("Timed out in test state %u (%s)", ctx.test_state,
                     state_name(ctx.test_state));
            state_enter(&ctx, kSuspendTestFailed);
            break;
        }
      } else {
        /////////////////////////////////////////////////////////////////
        // Foreground timer-driven activities:
        //
        // Some monitoring activities must occur in the foreground because the
        // monitored event is neither immediate nor will it trigger a link event.
        /////////////////////////////////////////////////////////////////

        switch (ctx.test_state) {
          case kSuspendTestActivatedAON:
            // Since the AON/Wakeup operates on a low clock frequency, it may take
            // some time for it to become active....await its signal
            CHECK_DIF_OK(
                dif_usbdev_get_wake_status(ctx.usbdev->dev, &ctx.wake_status));

            LOG_INFO("wake status active %u disconnected %u bus_reset %u\n",
                     ctx.wake_status.active, ctx.wake_status.disconnected,
                     ctx.wake_status.bus_reset);

            if (ctx.wake_status.active) {
              timeout_frames_set(&ctx, 2u);
              state_enter(&ctx, kSuspendTestPowerdown);

              if (ctx.test_phase == kSuspendPhaseDeepReset ||
                  ctx.test_phase == kSuspendPhaseDeepDisconnect) {
                LOG_INFO("Requesting Deep sleep");

                // Deep sleep.
                CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
                    &pwrmgr, kDifPwrmgrWakeupRequestSourceFour,
                    /*domain_config=*/0));
              } else {
                LOG_INFO("Requesting Normal sleep");

                // Normal sleep.
                CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
                    &pwrmgr, /*wakeups=*/kDifPwrmgrWakeupRequestSourceFour,
                    /*domain_config=*/kDifPwrmgrDomainOptionCoreClockInLowPower |
                        kDifPwrmgrDomainOptionUsbClockInActivePower |
                        kDifPwrmgrDomainOptionMainPowerInLowPower));
                // Enter low power mode.
              }

              // Enter low power mode.
              LOG_INFO("Issuing WFI to enter sleep");
              wait_for_interrupt();

              // After a Normal sleep, we resume execution here; after a Deep
              // sleep we start again as if from a Power On Reset
              dif_pwrmgr_wakeup_reason_t wakeup_reason;
              CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));

              LOG_INFO("wakeup types 0x%x sources 0x%x", wakeup_reason.types,
                       wakeup_reason.request_sources);
            }
            break;

          case kSuspendTestPowerdown:
            CHECK_DIF_OK(
                dif_usbdev_get_wake_status(ctx.usbdev->dev, &ctx.wake_status));

            // There are three ways that we may exit from Deep Sleep in which
            // the AON/Wake module has been handling the bus:
            // - Disconnecion (loss of VBUS/SENSE)
            // - Bus Reset (from host)
            // - Non-Idle state detected (Resume Signaling; this is inferred by
            //   neither of the other two conditions having occurred.)
            //   Resume signaling shall last at last 20ms, but the AON/Wake
            //   module alerts us long before that time has elapsed.

            LOG_INFO("powered down active %u disconnected %u bus_reset %u\n",
                     ctx.wake_status.active, ctx.wake_status.disconnected,
                     ctx.wake_status.bus_reset);

            // Check the signal from the AON/Wakeup module
            bool got_signal;
            switch (ctx.test_phase) {
              case kSuspendPhaseSleepReset:
              case kSuspendPhaseDeepReset:
                got_signal = (ctx.wake_status.bus_reset != 0);
                break;

              default:
                CHECK(ctx.test_phase == kSuspendPhaseDeepDisconnect);
                // no break
              case kSuspendPhaseSleepDisconnect:
                got_signal = (ctx.wake_status.disconnected != 0);
                break;
            }

            if (got_signal) {
              // Signal to the AON wakeup module that it should deactivate and
              // relinquish control of the bus
              CHECK_DIF_OK(dif_usbdev_set_wake_enable(ctx.usbdev->dev,
                                                      kDifToggleDisabled));

              state_enter(&ctx, kSuspendTestAONWakeup);
            }
            break;

          case kSuspendTestAONWakeup:
            // Since the AON wakeup module operates on a much lower clock
            // frequency it may take some time for it to stop monitoring and to
            // report becoming inactive...
            CHECK_DIF_OK(
                dif_usbdev_get_wake_status(ctx.usbdev->dev, &ctx.wake_status));

            LOG_INFO("aon waking active %u disconnected %u bus_reset %u\n",
                     ctx.wake_status.active, ctx.wake_status.disconnected,
                     ctx.wake_status.bus_reset);

            if (!ctx.wake_status.active) {
              timeout_set(&ctx, TIMEOUT_WAKEUP_RESUME);
              state_enter(&ctx, kSuspendTestWaitResumeTimeout);
            }
            break;

          default:
            break;
        }
      }
    }
  } while (ctx.test_state == kSuspendTestReset);

  if (verbose) {
    LOG_INFO("Test concluding (%s)", state_name(ctx.test_state));
  }

  CHECK(ctx.test_state == kSuspendTestComplete ||
        ctx.test_state == kSuspendTestFailed);

  return (ctx.test_state == kSuspendTestComplete);
}
