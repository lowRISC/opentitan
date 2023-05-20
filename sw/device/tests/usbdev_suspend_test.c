// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB suspend/resume test
//
// Basic test of suspend/resume signaling and disconnect/reconnect behavior.
// The DPI model sets up the device and reads the test descriptor. Having
// ascertained the specific testing behavior that is required, it proceeds to
// run through the appropriate states, time delays and bus activity as
// illustrated below.
//
// TODO: Throughout this time it should be possible with a few simple changes
// to the DPI code, to keep traffic streaming to and from the device, but
// the DPI model must be modified to invoke the streaming code too, and of
// course to service the streams only during active bus frames, not when SOF
// has been suppressed (Suspend Signaling, Resume Signaling, Reset Signaling)
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
// or a Bus Reset if a Bus Reset or Disconnect was the most recent wake
// stimulus. If the wake stimulus was Resume Signaling, then configuration does
// not occur again.
//
// [PhaseSleepResume]
// [PhaseSleepReset]
// [PhaseSleepDisconnect]
//
//  ... Bus Reset ->
// Power On Reset -> Configuration ->
//                 [from prev] ... -> DPI drops SOF -> Suspend -> Activate AON
//                -> Normal Sleep -> DPI produces wake stimulus -> Wakeup
//                -> Deactivate AON ... [to next]
//
// [PhaseDeepResume]
// [PhaseDeepReset]
// [PhaseDeepDisconnect]
//
//  ... Bus Reset ->
// Power On Reset -> Configuration ->
//                 [from prev] ... -> DPI drops SOF -> Suspend -> Actvivate AON
//                -> Deep Sleep -> DPI produces wake stimulus -> Wakeup
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
#include <string.h>

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
#include "sw/device/lib/testing/sram_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/usb_testutils.h"
#include "sw/device/lib/testing/usb_testutils_controlep.h"
#include "sw/device/lib/testing/usb_testutils_streams.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/tests/usbdev_suspend_test.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "sw/device/lib/testing/autogen/isr_testutils.h"

// Set up the recording of function points for this module
#define USBUTILS_FUNCPT_FILE USBUTILS_FUNCPT_FILE_USBDEV_SUSP_TEST

// Are we expecting a full frame interval?
// TODO: this must match the setting in the DPI model, but we do not have the
// ability to share header files.
// TODO: also note that this shall always be 1 for physical hosts.
#define FULL_FRAME 0

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

// How long should we wait on FPGA for configuration to occur?
#define TIMEOUT_FPGA_CONFIG 10U * 1000U * 1000U

/**
 * Durations that are specified in terms of bus frames, however long those
 * simulated bus frames happen to be (ie. these intervals are determined by
 * the DPI host behavior rather than the USB protocol specification)
 */

#define FRAMES_CONFIG_DELAY 2u

#define FRAMES_SUSPEND_MISSED 2u

#define FRAMES_INITIATE_RESUME 2u

/**
 * Number of frame delays to wait after device signals Suspend, before we
 */
#define FRAMES_WAIT_ENTER_SLEEP 1u

#define USB_EVENT_REPORT(s) USBUTILS_TRACE(__LINE__, (s))

/**
 * Test states
 */
typedef enum {
  /**
   *
   */
  kSuspendStateReset = 0u,
  /**
   * Waiting for the DPI/Host to suspend the device, for normal Suspend/Resume
   * behavior, not involving AON/Wakeup functionality.
   */
  kSuspendStateWaitSuspend,
  kSuspendStateWaitResume,
  kSuspendStateWaitBusReset,
  /**
   * Waiting for the DPI/Host to suspend the device, expecting a longer suspend
   * period, during which we put the device into Normal/Deep Sleep using the
   * AON/Wakeup functionality.
   */
  kSuspendStateWaitLongSuspend,
  /**
   * Waiting whilst Suspended, until we decide to enter Normal/Deep Sleep.
   * The DPI model is not expected to resume communication during this time.
   */
  kSuspendStateWaitSuspendTimeout,
  /**
   * We have instructed the AON/Wakeup module to wake over control of the USB
   * signals. It does not do so immediately because it lives in a slower clock
   * domain, but the delay should be very short.
   */
  kSuspendStateActivatedAON,
  /**
   * We are expecting to fall into a Normal Sleep.
   */
  kSuspendStateNormalSleep,
  /**
   * We are expecting to fall into a Deep Sleep.
   */
  kSuspendStateDeepSleep,
  /**
   * We have just returned from a Normal Sleep.
   */
  kSuspendStateNormalWaking,
  /**
   * We have just returned from a Deep Sleep.
   */
  kSuspendStateDeepWaking,
  /**
   * We've instructed the AON/Wakeup module to relinquish its control of the
   * USB and deactivate.
   */
  kSuspendStateAONWakeup,
  kSuspendStateWaitResumeTimeout,

  // TODO: do we still want this?
  kSuspendStateWaitFinish,
  /**
   * Transition to next test phase, with the device still connected and
   * operational, ie. Resume Signaling has occurred.
   */
  kSuspendStateNextPhase,
  /**
   * Test completed successfully.
   */
  kSuspendStateComplete,
  /**
   * Test failed.
   */
  kSuspendStateFailed,
} usbdev_suspend_state_t;

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
  /**
   * Unused padding.
   */
  uint8_t pad0;
  uint32_t pad[3];
} usbdev_retn_state_t;

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
  usbdev_suspend_state_t test_state;
  /**
   * Current test phase
   */
  usbdev_suspend_phase_t test_phase;
  /**
   * Final test phase (inclusive)
   */
  usbdev_suspend_phase_t fin_phase;
  /**
   * Streaming traffic throughout test?
   */
  bool with_traffic;
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
  /**
   * Our retained state; transferred to and from Retention SRAM over Sleep
   */
  usbdev_retn_state_t retn_state;
} usbdev_suspend_ctx_t;

/**
 * Retention SRAM start address
 */
const uint32_t kRetSramBaseAddr = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR;
/**
 * Retention SRAM address at which we may store some state.
 */
const uint32_t kRetSramOwnerAddr =
    kRetSramBaseAddr + offsetof(retention_sram_t, reserved_owner);

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
 * Do we expect this host to put the device into suspend?
 */
static bool host_suspends = true;
/**
 * Verbose logging? Mostly useful on FPGA; be warned that it can affect
 * timing in simulation, and in particular will likely break Verilator simus.
 */
static bool verbose = false;

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

/**
 * Context information for suspend/resume test
 */
static usbdev_suspend_ctx_t suspend_ctx;

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
    default:
      return "<Unknown>";
  }
}

// Return the name of a test state
static const char *state_name(usbdev_suspend_state_t state) {
  switch (state) {
    case kSuspendStateReset:
      return "Reset";
    case kSuspendStateWaitSuspend:
      return "WaitSuspend";
    case kSuspendStateWaitResume:
      return "WaitResume";
    case kSuspendStateWaitBusReset:
      return "WaitBusReset";
    case kSuspendStateWaitLongSuspend:
      return "WaitLongSuspend";
    case kSuspendStateWaitSuspendTimeout:
      return "WaitSuspendTimeout";
    case kSuspendStateActivatedAON:
      return "ActivatedAON";
    case kSuspendStateNormalSleep:
      return "NormalSleep";
    case kSuspendStateDeepSleep:
      return "DeepSleep";
    case kSuspendStateNormalWaking:
      return "NormalWaking";
    case kSuspendStateDeepWaking:
      return "DeepWaking";
    case kSuspendStateAONWakeup:
      return "AONWakeup";
    case kSuspendStateWaitResumeTimeout:
      return "WaitResumeTimeout";
    case kSuspendStateWaitFinish:
      return "WaitFinish";
    case kSuspendStateNextPhase:
      return "NextPhase";
    case kSuspendStateComplete:
      return "Complete";
    case kSuspendStateFailed:
      return "Failed";
    default:
      return "<Unknown>";
  }
}

// Transition to a (new) test state
static void state_enter(usbdev_suspend_ctx_t *ctx,
                        usbdev_suspend_state_t state) {
  if (verbose) {
    LOG_INFO("entering state %s", state_name(state));
  }
  ctx->test_state = state;
}

// Set a time out for the current test state, in microseconds
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
    LOG_INFO("Received Wakeup IRQ in sleep");
  }

  // Check that both the peripheral and the irq id are correct.
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}

/**
 * Simple Retention SRAM writing (from sram_ctrl_sleep_sram_ret_contents_test.c)
 */
static void retention_sram_store(const usbdev_retn_state_t *state) {
  sram_ctrl_testutils_write(kRetSramOwnerAddr, (sram_ctrl_testutils_data_t){
                                                   .words = (uint32_t *)state,
                                                   .len = sizeof(*state) / 4});
}

/**
 * Simple Retention SRAM reading (from sram_ctrl_sleep_sram_ret_contents_test.c)
 */
static void retention_sram_load(usbdev_retn_state_t *state) {
  memcpy(state, (uint8_t *)kRetSramOwnerAddr, sizeof(*state));
}

static void phase_start(usbdev_suspend_ctx_t *ctx,
                        usbdev_suspend_phase_t phase) {
  if (verbose) {
    LOG_INFO("phase_start %u (%s)", phase, phase_name(phase));
  }
  /**
   * Test descriptor; indicates to the DPI model that we're interested in
   * testing bus Suspend/Resume signaling, Reset signaling and Remote Wakeup
   * behavior.
   */
  uint8_t test_descriptor[] = {USB_TESTUTILS_TEST_DSCR(kUsbTestNumberSuspend,
                                                       phase,  // Test phase
                                                       0, 0, 0)};

  memcpy(ctx->test_dscr, test_descriptor, sizeof(ctx->test_dscr));

  // Remember the new test phase
  ctx->test_phase = phase;
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
        USB_EVENT_REPORT("SOF");
        hb = 0;
      }
    }

    // TODO: We are supplied with the SOF interrupts to help inform our decision
    //  but these are normally much too frequent to be reporting them
    snapshot &= ~(1u << kDifUsbdevIrqFrame);
  }

  if (verbose) {
    // Report connection/reset events
    if (snapshot & (1u << kDifUsbdevIrqPowered)) {
      USB_EVENT_REPORT("VBUS Connected");
    }
    if (snapshot & (1u << kDifUsbdevIrqDisconnected)) {
      USB_EVENT_REPORT("VBUS Disconnected");
    }
    if (snapshot & (1u << kDifUsbdevIrqLinkReset)) {
      USB_EVENT_REPORT("Link reset");
    }
    if (snapshot & (1u << kDifUsbdevIrqHostLost)) {
      USB_EVENT_REPORT("Host lost");
    }

    // Report suspend/resume status changes
    if (snapshot &
        ((1u << kDifUsbdevIrqLinkSuspend) | (1u << kDifUsbdevIrqLinkResume))) {
      switch (link_state) {
        case kDifUsbdevLinkStatePoweredSuspended:
        case kDifUsbdevLinkStateSuspended:
          USB_EVENT_REPORT("Suspended");
          break;

        case kDifUsbdevLinkStateResuming:
          USB_EVENT_REPORT("Resuming");
          break;

        case kDifUsbdevLinkStateActiveNoSof:
          USB_EVENT_REPORT("Resuming no SOF");
          break;

        case kDifUsbdevLinkStateActive:
          USB_EVENT_REPORT("Resumed");
          break;

        default:
          break;
      }
    }
  }

  // State machine anticipates the behavior of the host/DPI model, checking that
  // the expected events are reported within the expected time intervals, and
  // advances accordingly through the test states.

  switch (ctx->test_state) {
    case kSuspendStateReset:
      break;

    // We're expecting the host to drop the SOF heartbeat indicating that we
    // should suspend... (STEP_IDLE_)
    case kSuspendStateWaitSuspend:
      if (snapshot & (1u << kDifUsbdevIrqLinkSuspend)) {
        timeout_set(ctx, TIMEOUT_RESUME_MISSED);
        state_enter(ctx, kSuspendStateWaitResume);
      }
      break;

    // After a short delay, the host should resume automatically...
    // (STEP_ACTIVE_)
    case kSuspendStateWaitResume:
      if (snapshot & (1u << kDifUsbdevIrqLinkResume)) {
        state_enter(ctx, kSuspendStateWaitBusReset);
      }
      break;

    // A bus reset is performed by the host before it then sets up the device
    // again
    case kSuspendStateWaitBusReset:
      if (snapshot & (1u << kDifUsbdevIrqLinkReset)) {
        // The first test phase (Suspend/Resume without AON/Wakeup involvement)
        // is terminated by a deliberate Bus Reset, advancing us to the next
        // phase.
        if (ctx->test_phase == kSuspendPhaseSuspend) {
          // After the deliberate bus reset from the DPI/Host we shall return a
          // modified test descriptor that instructs the DPI model to enter a
          // different test phase...
          phase_start(ctx, kSuspendPhaseSleepReset);
        }
        state_enter(ctx, kSuspendStateReset);
      }
      break;

    // This time we're expecting a much longer Suspend...
    case kSuspendStateWaitLongSuspend:
      if (snapshot & (1u << kDifUsbdevIrqLinkSuspend)) {
        timeout_frames_set(ctx, FRAMES_WAIT_ENTER_SLEEP);
        state_enter(ctx, kSuspendStateWaitSuspendTimeout);
      }
      break;

    // We're _waiting for a timeout_ to occur, so we're not expecting any
    // events at this point...
    case kSuspendStateWaitSuspendTimeout:
      if (snapshot) {
        // TODO:
        state_enter(ctx, kSuspendStateFailed);
      }
      break;

    case kSuspendStateActivatedAON:
      // TODO: should respond to a resume event, and seize back control!
      break;
    case kSuspendStateNormalSleep:
    case kSuspendStateDeepSleep:
      break;
    case kSuspendStateAONWakeup:
      break;

    case kSuspendStateWaitResumeTimeout:
      break;

    case kSuspendStateWaitFinish:
      // We've resumed, we're just waiting for the host to perform some simple
      // traffic and then disconnect to signal test completion
      if (snapshot & (1u << kDifUsbdevLinkStateDisconnected)) {
        state_enter(ctx, kSuspendStateComplete);
      }
      break;

    case kSuspendStateNextPhase:
      break;

    case kSuspendStateFailed:
      break;

    default:
      LOG_INFO("Unknown/invalid test state %u (%s)", ctx->test_state,
               state_name(ctx->test_state));
      state_enter(ctx, kSuspendStateFailed);
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

////////////////////////////////////////////////////////////////////////////////
// Timeout handling
//
// Timeouts generally occur if an expected event has not happened as expected,
// indicating a failure. Some timeouts, however, simply indicate that the test
// should advance - ie. a necessary delay interval has elapsed - and others are
// necessary with a physical host (FPGA runs) because the requisite behavior
// cannot be generated by the host.
////////////////////////////////////////////////////////////////////////////////
static status_t timeout_handle(usbdev_suspend_ctx_t *ctx) {
  switch (ctx->test_state) {
    // Timeout is required to advance from the longer suspend state
    // because we're not expecting any host activity in this case, but
    // must initiate sleep/powerdown
    case kSuspendStateWaitSuspendTimeout:
      LOG_INFO("set_wake_enable...");
      timeout_frames_set(ctx, 1u);
      state_enter(ctx, kSuspendStateActivatedAON);

      TRY(dif_usbdev_set_wake_enable(ctx->usbdev->dev, kDifToggleEnabled));
      break;

    // Timeout
    case kSuspendStateWaitResumeTimeout:
      // TODO:
      //             timeout_frames_set(ctx, TIMEOUT_FINISH_MISSED);
      state_enter(ctx, kSuspendStateNextPhase);
      break;

    case kSuspendStateNormalSleep:
    case kSuspendStateDeepSleep:
      LOG_INFO("Timeout waiting to enter/leave Sleep");
      state_enter(ctx, kSuspendStateFailed);
      break;

    // Timeout may also be required to advance from Wait(Long)Suspend if
    // the host does not attempt to suspend the device, in which case we
    // shall also need to transition from WaitResume automatically...
    case kSuspendStateWaitBusReset:
    case kSuspendStateWaitResume:
    case kSuspendStateWaitSuspend:
    case kSuspendStateWaitLongSuspend:
      if (!host_suspends) {
        bool failed = false;
        switch (ctx->test_state) {
          case kSuspendStateWaitSuspend:
            LOG_INFO("auto-suspending (FPGA)");
            timeout_frames_set(ctx, FRAMES_INITIATE_RESUME);
            state_enter(ctx, kSuspendStateWaitResume);
            break;

          case kSuspendStateWaitResume:
            LOG_INFO("auto-resuming (FPGA)");
            state_enter(ctx, kSuspendStateWaitBusReset);
            // TODO: we shalln't get a bus reset without provoking it, but
            // we can do that!
            break;

          case kSuspendStateWaitLongSuspend:
            LOG_INFO("auto-long-suspending (FPGA)");
            timeout_frames_set(ctx, FRAMES_WAIT_ENTER_SLEEP);
            state_enter(ctx, kSuspendStateWaitSuspendTimeout);
            break;

          case kSuspendStateWaitBusReset:
            LOG_INFO("auto-resetting (FPGA)");
            // This will disconnect us from the bus.
            CHECK_STATUS_OK(usb_testutils_fin(ctx->usbdev));
            state_enter(ctx, kSuspendStateReset);
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
      LOG_INFO("Timed out in test state %u (%s)", ctx->test_state,
               state_name(ctx->test_state));
      state_enter(ctx, kSuspendStateFailed);
      break;
  }

  return OK_STATUS();
}

////////////////////////////////////////////////////////////////////////////////
// Foreground event handling
//
// Some monitoring activities must occur in the foreground because the
// monitored event is neither immediate nor will it trigger a link
// event.
////////////////////////////////////////////////////////////////////////////////
static status_t state_service(usbdev_suspend_ctx_t *ctx) {
  uint32_t timeout = FRAMES_SUSPEND_MISSED;

  switch (ctx->test_state) {
// TODO: this restructured startup code still requires more careful consideration
// and extensive checking.

    // If we can reuse the existing software state and device configuration for
    // this phase then we avoid reinitialization...
    case kSuspendStateDeepSleep:
    case kSuspendStateReset:

      LOG_INFO("Init testutils layer in state %u (%s)", ctx->test_state,
               state_name(ctx->test_state));

      // Initialize the usb_testutils layer
      // Note: when we exit a Deep Sleep via Resume Signaling we are relying
      // upon being able to set up the state of the endpoints and device
      // registers again, rather than retaining the full software state in SRAM
      CHECK_STATUS_OK(usb_testutils_init(ctx->usbdev, /*pinflip=*/false,
                                         /*en_diff_rcvr=*/true,
                                         /*tx_use_d_se0=*/false));

      // Register our interest in link events
      CHECK_STATUS_OK(
          usb_testutils_link_callback_register(ctx->usbdev, link_callback, ctx));

      // Set up Endpoint Zero for Control Transfers, at which point the
      // interface becomes enabled and we must be responsive to USB traffic.
      CHECK_STATUS_OK(usb_testutils_controlep_init(
          &usbdev_control, ctx->usbdev, 0, config_descriptors,
          sizeof(config_descriptors), ctx->test_dscr, sizeof(ctx->test_dscr)));

      if (ctx->test_state == kSuspendStateDeepSleep) {
        // Collect the device address and configuration previously used.
        const uint8_t dev_address = ctx->retn_state.dev_address;
        const uint8_t dev_config = ctx->retn_state.dev_config;

        // NOTE: We've run through the usb_testutils/controlep_init sequence as
        // normal because this sets up our endpoints as they were before, whilst
        // requiring less information to be stored in the retention RAM, but we
        // must still reinstate the device address.
        CHECK_DIF_OK(dif_usbdev_address_set(ctx->usbdev->dev, dev_address));

        // TODO: the controlep state needs to be forced to configured.
        // TODO: introduce an API call to set/restore the state information for
        // the control endpoint, to keep things a little cleaner/more contained?
        usbdev_control.device_state = kUsbTestutilsDeviceConfigured;
        usbdev_control.usb_config = dev_config;
        usbdev_control.new_dev = dev_address;

        // At this point we expected the device to be in the Powered state, and
        // since it won't see a Bus Reset, we nudge it into the ActiveNoSOF state.
        dif_usbdev_link_state_t link_state;
        TRY(dif_usbdev_status_get_link_state(ctx->usbdev->dev, &link_state));
        TRY_CHECK(link_state == kDifUsbdevLinkStatePowered);

        TRY(dif_usbdev_resume_link_to_active(ctx->usbdev->dev));
      } else {
        // In this case, since we have no retention RAM, we must wait until the
        // host has reconfigured us; do not wait indefinitely, in case something
        // has gone wrong. It should take only a few bus frames even with the
        // older, slower DPI behavior.

        if (kDeviceType == kDeviceFpgaCw310) {
          timeout_set(ctx, TIMEOUT_FPGA_CONFIG);
        } else {
          timeout_frames_set(ctx, 8u);
        }

        // TODO: This is some manual test code that drives OT into a normal sleep
        // and resumes in response to the Bus Reset that the DPI is generating at
        // this point.
        if (false) {
          ctx->test_phase = kSuspendPhaseSleepReset;

          TRY(dif_usbdev_set_wake_enable(ctx->usbdev->dev, kDifToggleEnabled));
          state_enter(ctx, kSuspendStateActivatedAON);

          // Wait until the aon_wake module has surrendered control
          while (ctx->test_state != kSuspendStateReset) {
            state_service(ctx);
          }

          state_enter(ctx, kSuspendStateComplete);
        }

        while (usbdev_control.device_state != kUsbTestutilsDeviceConfigured &&
               !ibex_timeout_check(&ctx->timeout)) {
          CHECK_STATUS_OK(usb_testutils_poll(ctx->usbdev));
        }

        // If we're out of step with the DPI model/host, stop the test.
        TRY_CHECK(usbdev_control.device_state == kUsbTestutilsDeviceConfigured);
      }

      // TODO: This does not relate directly to the Suspend-Resume testing but
      // unexplained behavior is observed on FPGA, and so this is still required
      // until we find out why an apparently spurious Suspend event occurs?!
      //
      // #if USBUTILS_FUNCTION_POINTS && USBUTILS_FUNCPT_USE_BUFFER
      //    usbutils_funcpt_report();
      // #endif

      // TODO: streaming code has now been integrated, but it would probably be
      // quite useful to be able to see the device streaming activity too, not
      // just that of the host side?

      if (ctx->with_traffic) {
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

      // The DPI model still needs to complete the 'SET_DEVICE_CONFIG' bus frame
      // and then devote another bus frame to reading the test configuration.
      // (GET_TEST_CONFIG), so we must expect to wait longer before seeing the
      // Suspend signaling.
      timeout += FRAMES_CONFIG_DELAY;
      // no break
    case kSuspendStateNextPhase:
      // Enter the appropriate starting state based upon the test phase
      switch (ctx->test_phase) {
        case kSuspendPhaseShutdown:
          // Nothing more to be done
          state_enter(ctx, kSuspendStateComplete);
          break;

        case kSuspendPhaseSuspend:
          state_enter(ctx, kSuspendStateWaitSuspend);
          break;

        default:
          CHECK(ctx->test_phase == kSuspendPhaseDeepDisconnect);
          // no break
        case kSuspendPhaseDeepReset:
        case kSuspendPhaseDeepResume:
          state_enter(ctx, kSuspendStateDeepWaking);
          break;

        case kSuspendPhaseSleepDisconnect:
        case kSuspendPhaseSleepReset:
        case kSuspendPhaseSleepResume:
          state_enter(ctx, kSuspendStateWaitLongSuspend);
          break;
      }
      // Initialize timeout to catch any failure of the host to suspend the bus
      timeout_frames_set(ctx, timeout);
      break;

    case kSuspendStateActivatedAON:
      // Since the AON/Wakeup operates on a low clock frequency, it may
      // take some time for it to become active....await its signal
      TRY(dif_usbdev_get_wake_status(ctx->usbdev->dev, &ctx->wake_status));

      LOG_INFO("wake status active %u disconnected %u bus_reset %u\n",
               ctx->wake_status.active, ctx->wake_status.disconnected,
               ctx->wake_status.bus_reset);

      if (ctx->wake_status.active) {
        // Retain our state information
        TRY(dif_usbdev_address_get(ctx->usbdev->dev,
                                   &ctx->retn_state.dev_address));
        ctx->retn_state.dev_config = usbdev_control.usb_config;
        ctx->retn_state.test_phase = (uint8_t)ctx->test_phase;
        if (verbose) {
          LOG_INFO(" - retaining address %u config %u phase %u (%s)",
                   ctx->retn_state.dev_address, ctx->retn_state.dev_config,
                   ctx->retn_state.test_phase,
                   phase_name(ctx->retn_state.test_phase));
        }

        retention_sram_store(&ctx->retn_state);

        if (ctx->test_phase == kSuspendPhaseDeepResume ||
            ctx->test_phase == kSuspendPhaseDeepReset ||
            ctx->test_phase == kSuspendPhaseDeepDisconnect) {
          LOG_INFO("Requesting Deep sleep");

          // Deep sleep.
          //
          // Note: we must keep the 'Active USB clock enable' bit set, becausse
          // otherwise when we return to the active state, the usbdev clock will
          // not be restored.
          TRY(pwrmgr_testutils_enable_low_power(
              &pwrmgr, kDifPwrmgrWakeupRequestSourceFour,
              /*domain_config=*/kDifPwrmgrDomainOptionUsbClockInActivePower));

          // Record that we've asked to power down; timeout should never occur.
          timeout_frames_set(ctx, 2u);
          state_enter(ctx, kSuspendStateDeepSleep);
        } else {
          LOG_INFO("Requesting Normal sleep");

          // Normal sleep.
          TRY(pwrmgr_testutils_enable_low_power(
              &pwrmgr, /*wakeups=*/kDifPwrmgrWakeupRequestSourceFour,
              /*domain_config=*/
              kDifPwrmgrDomainOptionCoreClockInLowPower |
                  kDifPwrmgrDomainOptionUsbClockInActivePower |
                  kDifPwrmgrDomainOptionMainPowerInLowPower));

          // Record that we've asked to enter lower power mode; timeout should
          // never occur.
          timeout_frames_set(ctx, 2u);
          state_enter(ctx, kSuspendStateNormalSleep);
        }

        // Enter low power mode.
        LOG_INFO("Issuing WFI to enter sleep");
        wait_for_interrupt();

        //---------------------------------------------------------------
        // After a Normal sleep, we resume execution here; after a Deep
        // sleep we start again as if from a Power On Reset, but the
        // pwrmgr tells us otherwise.
        //---------------------------------------------------------------

// TODO: check the IRQ source in the event of a Normal Sleep and proceeding
// past the WFI

        // Check that a DeepSleep request did not somehow run past the WFI...
        TRY_CHECK(ctx->test_state == kSuspendStateNormalSleep);
        // ... and we should be in one of these test phases.
        TRY_CHECK(ctx->retn_state.test_phase == kSuspendPhaseSleepResume ||
                  ctx->retn_state.test_phase == kSuspendPhaseSleepReset ||
                  ctx->retn_state.test_phase == kSuspendPhaseSleepDisconnect);

        // Retrieve it (Q: do we need to?)
        usbdev_retn_state_t stored_state;
        retention_sram_load(&stored_state);
        if (verbose) {
          LOG_INFO(" - retained address %u config %u phase %u (%s)",
                   stored_state.dev_address, stored_state.dev_config, stored_state.test_phase, phase_name(stored_state.test_phase));
        }

        // Check that the Retention SRAM did its job over Normal Sleep at least;
        // the SRAM should remain powered and clocked so this should not be
        // challenging.
        TRY_CHECK(stored_state.dev_address == ctx->retn_state.dev_address &&
                  stored_state.dev_config == ctx->retn_state.dev_config &&
                  stored_state.test_phase == ctx->retn_state.test_phase);

        dif_pwrmgr_wakeup_reason_t wakeup_reason;
        TRY(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));

        LOG_INFO("wakeup types 0x%x sources 0x%x", wakeup_reason.types,
                 wakeup_reason.request_sources);

        timeout_frames_set(ctx, 1u);
        state_enter(ctx, kSuspendStateNormalWaking);
      }
      break;

    case kSuspendStateNormalWaking:
    case kSuspendStateDeepWaking:
      // We've returned from sleeping; enquire of the USB AON Wake module
      // what happened...
      TRY(dif_usbdev_get_wake_status(ctx->usbdev->dev, &ctx->wake_status));

      // There are three ways that we may exit from Deep Sleep in which
      // the AON/Wake module has been handling the bus:
      // - Disconnecion (loss of VBUS/SENSE)
      // - Bus Reset (from host)
      // - Non-Idle state detected (Resume Signaling; this is inferred by
      //   neither of the other two conditions having occurred.)
      //   Resume signaling shall last at last 20ms, but the AON/Wake
      //   module alerts us long before that time has elapsed.

      LOG_INFO("Awaking: active %u disconnected %u bus_reset %u\n",
               ctx->wake_status.active, ctx->wake_status.disconnected,
               ctx->wake_status.bus_reset);

      // Check the report from the AON/Wakeup module
      if (ctx->wake_status.active) {
        bool got_signal = false;

        switch (ctx->test_phase) {
          case kSuspendPhaseSleepResume:
          case kSuspendPhaseDeepResume:
            got_signal =
                (!ctx->wake_status.bus_reset && !ctx->wake_status.disconnected);
            break;

          case kSuspendPhaseSleepReset:
          case kSuspendPhaseDeepReset:
            got_signal = (ctx->wake_status.bus_reset != 0);
            break;

          default:
            TRY_CHECK(ctx->test_phase == kSuspendPhaseDeepDisconnect);
            // no break
          case kSuspendPhaseSleepDisconnect:
            got_signal = (ctx->wake_status.disconnected != 0);
            break;
        }

        if (got_signal) {
          // TODO: Issue #18562 VBUS Disconnection leaves pull ups asserted
          // by the USB AON Wake module, so disconnect them here before
          // potential confusion results.
          if (ctx->test_phase == kSuspendPhaseSleepDisconnect) {
            bool sense;

            TRY(dif_usbdev_status_get_sense(ctx->usbdev->dev, &sense));
            if (verbose) {
              LOG_INFO("Handling Disconnection when VBUS %sasserted", sense ? "" : "de-");
            }
            // If VBUS/SENSE is not asserted, then the pull up will be removed
            // as soon as the AON Wake module is deactivated, because usbdev
            // qualifies its own pull up assertions with VBUS/SENSE presence.
            if (sense) {
              TRY(dif_usbdev_interface_enable(ctx->usbdev->dev, false));
            }
          }

          // Signal to the AON wakeup module that it should deactivate and
          // relinquish control of the bus
          TRY(dif_usbdev_set_wake_enable(ctx->usbdev->dev, kDifToggleDisabled));

          // Although it operate at 200kHz, it should't take long
          timeout_set(ctx, 1000u);
          state_enter(ctx, kSuspendStateAONWakeup);
        } else {
          LOG_INFO("Unexpected report from USB AON Wake module");
          state_enter(ctx, kSuspendStateFailed);
        }
      } else {
        LOG_INFO("AON/Wake module not active when expected");
        state_enter(ctx, kSuspendStateFailed);
      }
      break;

    case kSuspendStateAONWakeup:
      // Since the AON wakeup module operates on a much lower clock
      // frequency it may take some time for it to stop monitoring and to
      // report becoming inactive...
      TRY(dif_usbdev_get_wake_status(ctx->usbdev->dev, &ctx->wake_status));

      LOG_INFO("AON Wake module active %u disconnected %u bus_reset %u\n",
               ctx->wake_status.active, ctx->wake_status.disconnected,
               ctx->wake_status.bus_reset);

      if (!ctx->wake_status.active) {
        // If we've been awoken by a Disconnection event or by a Bus Reset
        // event rather than by Resume Signaling, then we must advance to
        // the next test phase and expect to be reconfigured.
        //
        // Note: at this point we may assume that we _did_ get the
        // expected wakeup stimulus/report, because it was checked above.
        switch (ctx->test_phase) {
          case kSuspendPhaseSleepDisconnect:
          case kSuspendPhaseDeepDisconnect:
            // TODO: in this case, we just tear down and rebuild the
            // software stack, right?
            state_enter(ctx, kSuspendStateReset);
            break;

          case kSuspendPhaseSleepReset:
            // For a Bus Reset, we can keep the software state and endpoint
            // set up etc. We just need to be sure that the control endpoint
            // has been returned to the 'Default' state.

            // TODO: with a physical host we shall awaken whilst the Reset
            // Signaling is still under way, so the control endpoint will
            // be notified of the link reset and it will return to the Default
            // state.
            // For our much reset

            state_enter(ctx, kSuspendStateNextPhase);
            break;

          case kSuspendPhaseDeepReset:
            state_enter(ctx, kSuspendStateReset);
            break;

          default:
            TRY_CHECK(ctx->test_phase == kSuspendPhaseDeepResume);
            // no break
          case kSuspendPhaseSleepResume:
            timeout_set(ctx, TIMEOUT_WAKEUP_RESUME);
            state_enter(ctx, kSuspendStateWaitResumeTimeout);
            break;
        }
      } else {
        LOG_INFO("AON Wake module not active when expected");
        state_enter(ctx, kSuspendStateFailed);
      }
      break;

      // TODO: do we still want this state?
    case kSuspendStateWaitFinish:
      break;

    // States in which we sit waiting - with a timeout - for something
    // significant to happen...
    default:
      TRY_CHECK(ctx->test_state == kSuspendStateWaitResumeTimeout);
      // no break
    case kSuspendStateWaitSuspend:
    case kSuspendStateWaitResume:
    case kSuspendStateWaitBusReset:
    case kSuspendStateWaitLongSuspend:
    case kSuspendStateWaitSuspendTimeout:
      //          case kSuspendStateWaitResumeTimeout:
      break;
  }

  return OK_STATUS();
}

/**
 * Run a single test phase to completion
 */
static status_t phase_run(usbdev_suspend_ctx_t *ctx) {

  // The DPI model and our callback handler for USB link events do most of the
  // work of walking through the test states until completion
  bool phase_done = false;
  do {
    if (ibex_timeout_check(&ctx->timeout)) {
      TRY(timeout_handle(ctx));
    } else {
      TRY(state_service(ctx));
    }

    switch (ctx->test_state) {
      // These states transition transition to another phase or terminate the
      // test sequence.
      case kSuspendStateComplete:
      case kSuspendStateFailed:
      case kSuspendStateReset:
      case kSuspendStateNextPhase:
        phase_done = true;
        break;

      // Do not poll the USB device or perform traffic in these states.
      case kSuspendStateActivatedAON:
      case kSuspendStateAONWakeup:
      case kSuspendStateDeepSleep:
      case kSuspendStateNormalSleep:
        break;

      default:
        if (ctx->with_traffic) {
          // Servicing streams handles usbdev/testutils events for us.
          CHECK_STATUS_OK(usb_testutils_streams_service(&usbdev_streams));
        } else {
          // No traffic, but we must still poll the usb_testutils layer to handle
          // hardware events and callbacks.
          CHECK_STATUS_OK(usb_testutils_poll(ctx->usbdev));
        }
        break;
    }
  } while (!phase_done);

  // Bus Reset is how we advance to the next test phase if we had to rely
  // upon our own state machine to complete the operation because the host
  // is incapable of providing the necessary stimulus.
  // TODO: or Disconnect?
  switch (ctx->test_state) {
    case kSuspendStateReset:
      // no break
    case kSuspendStateNextPhase:
      // Was this the final phase of the test?
      if (ctx->test_phase == ctx->fin_phase) {
        state_enter(ctx, kSuspendStateComplete);
      } else {
        phase_start(ctx, (usbdev_suspend_phase_t)(ctx->test_phase + 1u));
      }
      break;

    default:
      TRY_CHECK(ctx->test_state == kSuspendStateComplete ||
                ctx->test_state == kSuspendStateFailed);
      break;
  }

  return OK_STATUS();
}

bool usbdev_suspend_test(usbdev_suspend_phase_t init_phase,
                         usbdev_suspend_phase_t fin_phase, bool with_traffic) {
  usbdev_suspend_ctx_t *ctx = &suspend_ctx;

  // Wipe out any memory from the previous test phase, just to be more confident
  // that we really are resuming from Deep Sleep and using only the Retention
  // SRAM contents to resume.
  //
  // This also means that the data we subsequently store in the Retention SRAM
  // has defined values for the unused padding fields.
  memset(ctx, 0, sizeof(*ctx));

  LOG_INFO("Running USBDEV_SUSPEND test");

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Remember the phase in which we are to stop.
  CHECK(fin_phase >= init_phase);
  ctx->fin_phase = fin_phase;

  switch (kDeviceType) {
    case kDeviceSimVerilator:
      // steal the UART output and send it via a faster mechanism
      base_set_stdout(base_stdout);

      // DPI model performs suspend/resume signaling in response to reading our
      // test description.
      host_suspends = true;

      // DPI model can perform traffic and will deliberately avoid performing
      // traffic during the periods when it stops sending the bus frames
      // with_traffic = true;
      break;

    // Do NOT steal the UART output in this case because DVsim has a back door
    // for rapid logging.
    case kDeviceSimDV:
      // DPI model performs suspend/resume signaling in response to reading our
      // test description.
      host_suspends = true;

      // DPI model can perform traffic and will deliberately avoid performing
      // traffic during the periods when it stops sending the bus frames
      // with_traffic = true;

      // TODO: Verbose reporting is okay with DVsim, and we don't have things
      // working yet! :)
      verbose = true;
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
  // ctx->with_traffic = with_traffic;
  ctx->with_traffic = false;

  LOG_INFO("  (seq: %s to %s with%s traffic)", phase_name(init_phase),
           phase_name(ctx->fin_phase), ctx->with_traffic ? "" : "out");

  // Initialize pinmux.
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
  ctx->usbdev = &usbdev;

  if (rst_info == kDifRstmgrResetInfoPor) {
    LOG_INFO("Booting for the first time");
    phase_start(ctx, init_phase);
    state_enter(ctx, kSuspendStateReset);
  } else {
    LOG_INFO("Resuming from power down!");
    // Recover state from the retention RAM
    retention_sram_load(&ctx->retn_state);
    if (verbose) {
      LOG_INFO(" - retained address %u config %u phase %u (%s)",
               ctx->retn_state.dev_address, ctx->retn_state.dev_config,
               ctx->retn_state.test_phase,
               phase_name(ctx->retn_state.test_phase));
    }

    // To have arrived we should be in one of these test phases.
    CHECK(ctx->retn_state.test_phase == kSuspendPhaseDeepResume ||
          ctx->retn_state.test_phase == kSuspendPhaseDeepReset ||
          ctx->retn_state.test_phase == kSuspendPhaseDeepDisconnect);

    // We can - presently - check the other parameters.
    CHECK(ctx->retn_state.dev_config == 1u);
    if (kDeviceType == kDeviceSimDV || kDeviceType == kDeviceSimVerilator) {
      // We happen to know that the DPI model supplies a fixed device address
      // at present.
      CHECK(ctx->retn_state.dev_address == 2u);
    }

    // In The Retention SRAM we stored the phase that we had been performing;
    // Decide upon the next test phase and state
    usbdev_suspend_state_t next_state;
    usbdev_suspend_phase_t next_phase;

    switch (ctx->retn_state.test_phase) {
      case kSuspendPhaseDeepResume:
        next_state = kSuspendStateDeepSleep;
        next_phase = kSuspendPhaseDeepReset;
        break;
      case kSuspendPhaseDeepReset:
        next_state = kSuspendStateReset;
        next_phase = kSuspendPhaseDeepDisconnect;
        break;
      default:
        CHECK(ctx->retn_state.test_phase == kSuspendPhaseDeepDisconnect);
        next_state = kSuspendStateDeepSleep;
        next_phase = kSuspendPhaseShutdown;
        break;
    }
    phase_start(ctx, next_phase);
    state_enter(ctx, next_state);
  }

  do {
    if (verbose) {
      LOG_INFO("PHASE %u (%s)", ctx->test_phase, phase_name(ctx->test_phase));
    }

    // Run this test phase
    CHECK_STATUS_OK(phase_run(ctx));

    // Keep going if we're advancing to the next phase.
    //  (NextPhase means that we advance whilst still active and can thus skip
    //   device setup and configuratinon)
  } while (ctx->test_state == kSuspendStateNextPhase ||
           ctx->test_state == kSuspendStateReset);

  if (verbose) {
    LOG_INFO("Test concluding (%s)", state_name(ctx->test_state));
  }

  return (ctx->test_state == kSuspendStateComplete);
}
