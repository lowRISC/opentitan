// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// USB suspend/resume test
//
// Basic test of suspend/resume signaling and disconnect/reconnect behavior.
// The DPI model sets up the device and reads the test descriptor. Having
// ascertained the specific testing behavior that is required, it proceeds to
// run through the appropriate states, time delays and bus activity as
// illustrated below.
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
// not occur again and we arrive via NextPhase
//
// [PhaseSleepResume]
// [PhaseSleepReset]
// [PhaseSleepDisconnect]
//
//  ... Bus Reset ->
// Power On Reset -> Configuration ->
//           [from prev phase] ... -> DPI drops SOF -> Suspend -> Activate AON
//                -> Normal Sleep -> DPI produces wake stimulus -> Wakeup
//                -> Deactivate AON ... [to next]
//
// [PhaseDeepResume]
// [PhaseDeepReset]
// [PhaseDeepDisconnect]
//
//  ... Bus Reset ->
// Power On Reset -> Configuration ->
//           [from prev phase] ... -> DPI drops SOF -> Suspend -> Activate AON
//                -> Deep Sleep -> DPI produces wake stimulus -> Wakeup
//                -> Deactivate AON .. [to next]
//
// [PhaseShutdown] Test Complete
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

#include "sw/device/tests/usbdev_suspend.h"

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

#define MODULE_ID MAKE_MODULE_ID('u', 'd', 'u')

// Set up the recording of function points for this module
#define USBUTILS_FUNCPT_FILE USBUTILS_FUNCPT_FILE_USBDEV_SUSP_TEST

// Are we using purely Isochronous streams for testing?
#define USE_ISO_STREAMS 0
// Are we using purely Bulk streams for testing?
#define USE_BULK_STREAMS 1
// Otherwise, we'll use a mixture

// The number of streams to be employed if testing with traffic
#if USB_ISO_STREAMS
#define NUM_STREAMS 4U
#else
#define NUM_STREAMS USBUTILS_STREAMS_MAX
#endif

// Are we expecting a full frame interval?
// Note: this must match the setting in the DPI model, but we do not have the
// ability to share header files.
#ifndef USBDPI_FULL_FRAME
// By default we shorten the test duration.
#define USBDPI_FULL_FRAME 0
#endif

// TODO: these are now set appropriately for automated testing on FPGA/ES.
//  We need three sets of parameters:
//  - chip simulation
//  - FPGA/Silicon with automated host code
//  - FPGA/Silicon with manual test stimulus

/**
 * Timeout constants in microseconds;
 */
enum {
  TimeoutResumeMissed = 40U * 1000U,
  TimeoutResetMissed = 60U * 1000U,
  TimeoutWakeupResume = 30000u,
  TimeoutFinishMissed = 2000u,
  TimeoutAonResponse = 5000u,
  TimeoutSleepFailed = 5000u,

  // How long should we wait for configuration to occur if observing physical
  // timings? (Real USB host or physically-accurate timings in simulation.)
  TimeoutPhysConfig = 10U * 1000U * 1000U,

  /**
   * Durations that are specified in terms of bus frames, however long those
   * simulated bus frames happen to be (ie. these intervals are determined by
   * the DPI host behavior rather than the USB protocol specification)
   */
  FramesConfigDelay = 2000u,
  FramesSuspendMissed = 2000u,
  FramesInitiateResume = 2u,

  /**
   * Number of frame delays to wait after device signals Suspend, before we
   * initiate sleeping.
   */
  FramesWaitEnterSleep = 10u,
};

/**
 * Maximum size of the client state stored within the Retention SRAM;
 * we leave the usb_testutils_streams/other code to specify and manage its own
 * state.
 */
#define MAX_CLIENT_STATE 0x400U

/**
 * Test states
 */
typedef enum {
  /**
   * Power On Reset (start of first phase of test sequence).
   */
  kSuspendStatePowerOnReset = 0u,
  /**
   * Bus Reset from DPI/Host has occurred.
   */
  kSuspendStateBusReset,
  /**
   * Waiting for the DPI/Host to suspend the device, for normal Suspend/Resume
   * behavior, not involving AON/Wakeup functionality.
   */
  kSuspendStateWaitSuspend,
  /**
   * Waiting for the DPI/Host to suspend the device, expecting a longer suspend
   * period, during which we put the device into Normal/Deep Sleep using the
   * AON/Wakeup functionality.
   */
  kSuspendStateWaitLongSuspend,
  /**
   * Waiting for the DPI/Host to initiate a Resume from Suspended.
   */
  kSuspendStateWaitResume,
  /**
   * Waiting for the DPI/Host to provide the Bus Reset stimulus.
   */
  kSuspendStateWaitBusReset,
  /**
   * Waiting whilst Suspended, until we decide to enter Normal/Deep Sleep.
   * The DPI/Host is not expected to resume communication during this time.
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
  /**
   * TODO: Resume Signaling still needs completing...
   */
  kSuspendStateWaitResumeTimeout,
  /**
   * Waiting for the DPI/Host to decide that the test phase is complete.
   */
  kSuspendStateWaitFinish,
  /**
   * Transition to next test phase, with the device still connected and
   * operational, ie. Resume Signaling has occurred.
   */
  kSuspendStateNextPhase,
  /**
   * Disconnecting from the bus.
   */
  kSuspendStateWaitDisconnect,
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
  /**
   * Number of remaining test iterations.
   */
  uint32_t num_iters;
  /**
   * Data Toggle bits.
   */
  uint32_t data_toggles;
  /**
   * Used bytes of client state.
   */
  uint32_t client_used;
  /**
   * Client state; allow, for example, the usb_testutils_streams code to specify
   * its own per-stream retention state rather than constraining it here.
   */
  alignas(uint32_t) uint8_t client_state[MAX_CLIENT_STATE];
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
   * Initial test phase (inclusive)
   */
  usbdev_suspend_phase_t init_phase;
  /**
   * Final test phase (inclusive)
   */
  usbdev_suspend_phase_t fin_phase;
  /**
   * Number of iterations remaining (including the present iteration).
   */
  uint32_t num_iters;
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

enum {
  /**
   * Retention SRAM start address
   */
  kRetSramBaseAddr = TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR,
  /**
   * Retention SRAM address at which we may store some state.
   */
  kRetSramOwnerAddr = kRetSramBaseAddr + offsetof(retention_sram_t, owner),
};

// Total length of the configuration descriptor.
#define CFG_DSCR_TOTAL_LEN \
  (USB_CFG_DSCR_LEN +      \
   NUM_STREAMS * (USB_INTERFACE_DSCR_LEN + 2 * USB_EP_DSCR_LEN))

// This Configuration Descriptor must be capable of describing the maximal
// number of interfaces (= number of streams). It is overwritten dynamically
// when streaming with traffic.
static uint8_t config_descriptors[CFG_DSCR_TOTAL_LEN] = {
    // Default configuration, for use if we're not testing with traffic too;
    // we still need configuration for the host to recognize and configure us.
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
 * USB Bus Frame duration, in microseconds; may be reduced when communicating
 * with the USBDPI module to reduce the simulation time.
 */
static uint32_t frame_interval = 1000u;

/**
 * USB device context types.
 */
static usb_testutils_ctx_t usbdev;
static usb_testutils_controlep_ctx_t usbdev_control;
static usb_testutils_streams_ctx_t usbdev_streams;

static const dt_pinmux_t kPinmuxDt = 0;
static_assert(kDtPinmuxCount == 1, "this library expects exactly one pinmux");
static const dt_pwrmgr_t kPwrmgrDt = 0;
static_assert(kDtPwrmgrCount == 1, "this library expects exactly one pwrmgr");
static const dt_rstmgr_t kRstmgrDt = 0;
static_assert(kDtRstmgrCount == 1, "this library expects exactly one rstmgr");
static const dt_rv_plic_t kRvPlicDt = 0;
static_assert(kDtRvPlicCount == 1, "this library expects exactly one rv_plic");

enum {
  kPlicTarget = 0,
};

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
 * Wakeup sources for USB.
 */
static dif_pwrmgr_request_sources_t wakeup_sources;
/**
 * Do we expect this host to put the device into suspend?
 */
static bool host_suspends = true;
/**
 * Do we expect this host to perform Resume Signaling and awaken the device from
 * a Suspended state?
 */
static bool host_resumes = true;
/**
 * Do we expect this host to perform Bus Resets to awaken the device from sleep?
 */
static bool host_resets = true;
/**
 * Do we expect this host to Disconnect the device to awaken it from sleep?
 */
static bool host_disconnects = true;
/**
 * Verbose logging? Mostly useful on FPGA; be warned that it can affect
 * timing in simulation, and in particular will likely break Verilator sims.
 *
 * It can also cause timeouts on the host side with automated regression
 * tests on FPGA/Silicon because the CPU is stalled waiting for UART FIFO
 * space.
 *
 * TODO: perhaps we want a uart_flush() at carefully selected moments, eg.
 *       when setting a timeout?
 */
static bool verbose = true;
/**
 * Verbose logging from the streaming code?
 *
 * Note: this makes the test a lot slower because the CPU is stalled awaiting
 * UART FIFO space.
 */
static bool s_verbose = false;

// Configuration for streaming layer. This specifies the transfer type of each
// of the streams being used and checked if we're testing with traffic enabled.
static const unsigned nstreams = NUM_STREAMS;
#if USE_ISO_STREAMS
static const usb_testutils_transfer_type_t xfr_types[] = {
    kUsbTransferTypeIsochronous, kUsbTransferTypeIsochronous,
    kUsbTransferTypeIsochronous, kUsbTransferTypeIsochronous,
    kUsbTransferTypeIsochronous, kUsbTransferTypeIsochronous,
    kUsbTransferTypeIsochronous, kUsbTransferTypeIsochronous,
    kUsbTransferTypeIsochronous, kUsbTransferTypeIsochronous,
    kUsbTransferTypeIsochronous};
#elif USE_BULK_STREAMS
static const usb_testutils_transfer_type_t xfr_types[] = {
    kUsbTransferTypeBulk, kUsbTransferTypeBulk, kUsbTransferTypeBulk,
    kUsbTransferTypeBulk, kUsbTransferTypeBulk, kUsbTransferTypeBulk,
    kUsbTransferTypeBulk, kUsbTransferTypeBulk, kUsbTransferTypeBulk,
    kUsbTransferTypeBulk, kUsbTransferTypeBulk};
#else
static const usb_testutils_transfer_type_t xfr_types[] = {
    kUsbTransferTypeIsochronous, kUsbTransferTypeInterrupt,
    kUsbTransferTypeBulk,        kUsbTransferTypeBulk,

    kUsbTransferTypeIsochronous, kUsbTransferTypeInterrupt,
    kUsbTransferTypeBulk,        kUsbTransferTypeIsochronous,

    kUsbTransferTypeInterrupt,   kUsbTransferTypeBulk,
    kUsbTransferTypeBulk,
};
#endif

// Full traffic and checking
static const usbdev_stream_flags_t test_flags =
    kUsbdevStreamFlagRetrieve | kUsbdevStreamFlagCheck |
    kUsbdevStreamFlagRetry | kUsbdevStreamFlagSend;
// We don't expect it to complete; data transfer is exercised and checked in
// other tests.
static const uint32_t transfer_bytes = 0x80 << 20;

/**
 * Context information for suspend/resume test
 */
static usbdev_suspend_ctx_t suspend_ctx;

/**
 * Report progress; these messages are obligatory for automated testing in order
 * that the host-side test harness may synchronize with this device-side code.
 */
// Implement as a varargs function if it becomes more complicated.
// static inline void report_progress(const char *msg);
#define report_progress(...) LOG_INFO(__VA_ARGS__)

/**
 * Are we observing physically-accurate timings?
 */
static inline bool physical_timings(void) {
  switch (kDeviceType) {
    case kDeviceFpgaCw310:
    case kDeviceFpgaCw340:
    case kDeviceSilicon:
      break;
    default:
      return false;
  }
  return true;
}

// Return a timeout in microseconds, scaled for the test target; longer timeout
// periods are more appropriate for FPGA tests and decidedly undesirable for
// Verilator top-level simulations
static uint32_t time_frames(unsigned n) {
  uint32_t scale = 1u;
  if (physical_timings()) {
    //    scale = 500u;
  }
  return scale * n * frame_interval;
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
    case kSuspendPhaseShutdown:
      return "Shutdown";
    default:
      return "<Unknown>";
  }
}

// Return the name of a test state
static const char *state_name(usbdev_suspend_state_t state) {
  switch (state) {
    case kSuspendStatePowerOnReset:
      return "PowerOnReset";
    case kSuspendStateBusReset:
      return "BusReset";
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
    case kSuspendStateWaitDisconnect:
      return "WaitDisconnect";
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

// Report any link event(s)
static void events_report(usbdev_suspend_ctx_t *ctx, uint32_t snapshot,
                          dif_usbdev_link_state_t link_state) {
  // Report connection/reset events
  if (snapshot & (1u << kDifUsbdevIrqPowered)) {
    LOG_INFO("VBUS Connected");
  }
  if (snapshot & (1u << kDifUsbdevIrqDisconnected)) {
    LOG_INFO("VBUS Disconnected");
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
}

// Transition to a (new) test state
static inline void state_enter(usbdev_suspend_ctx_t *ctx,
                               usbdev_suspend_state_t state) {
  if (verbose) {
    LOG_INFO("entering state %s", state_name(state));
  }
  ctx->test_state = state;
}

// Set a time out for the current test state, in microseconds
static inline void timeout_set(usbdev_suspend_ctx_t *ctx,
                               uint32_t interval_us) {
  if (verbose) {
    LOG_INFO("timeout_set %uus\n", interval_us);
    if (false) {
      uint64_t now = ibex_mcycle_read();
      uint64_t then = now + interval_us;
      LOG_INFO("  setting timeout to 0x%x%x (at 0x%x%x)",
               (uint32_t)(then >> 32), (uint32_t)then, (uint32_t)(now >> 32),
               (uint32_t)now);
    }
  }
  ctx->timeout = ibex_timeout_init(interval_us);
}

// Set a time out, in frames, for the current test state
static void timeout_frames_set(usbdev_suspend_ctx_t *ctx,
                               uint32_t interval_frames) {
  timeout_set(ctx, time_frames(interval_frames));
}

////////////////////////////////////////////////////////////////////////////////
// Report the state of the phy pins
////////////////////////////////////////////////////////////////////////////////
void sense_report(usbdev_suspend_ctx_t *ctx, uint32_t niters) {
  while (niters-- > 0u) {
    dif_usbdev_phy_pins_sense_t sense;
    CHECK_DIF_OK(dif_usbdev_get_phy_pins_status(ctx->usbdev->dev, &sense));
#if USBUTILS_FUNCTION_POINTS
    uint32_t data = (sense.rx_dp ? 1U : 0) | (sense.rx_dn ? 2U : 0) |
                    (sense.rx_d ? 4U : 0) | (sense.output_enable ? 8U : 0) |
                    (sense.vbus_sense ? 0x100U : 0);
    USBUTILS_FUNCPT(0x515, data);
#endif
    LOG_INFO(
        "sense %u : rx_dp %u rx_dn %u rx_d %u : tx_dp %u tx_dn %u tx_d %u "
        "tx_se0 %u : oe %u",
        sense.vbus_sense, sense.rx_dp, sense.rx_dn, sense.rx_d, sense.tx_dp,
        sense.tx_dn, sense.tx_d, sense.tx_se0, sense.output_enable);
  }
}

/**
 * Report the status information from the AON/Wake module.
 */
void report_wake_status(usbdev_suspend_ctx_t *ctx) {
  LOG_INFO("wake status active %u disconnected %u bus_reset %u",
           ctx->wake_status.active, ctx->wake_status.disconnected,
           ctx->wake_status.bus_reset);
  LOG_INFO(" bus_not_idle %u", ctx->wake_status.bus_not_idle);
  LOG_INFO(" (host_resumes %u host_resets %u host_disconnects %u)",
           host_resumes, host_resets, host_disconnects);
}

/**
 * Collect and optionally report the current 'wake status' reported by the
 * AON/Wake module. This indicates why sleep was interrupted.
 */
status_t collect_wake_status(usbdev_suspend_ctx_t *ctx) {
  TRY(dif_usbdev_get_wake_status(ctx->usbdev->dev, &ctx->wake_status));
  if (verbose) {
    report_wake_status(ctx);
  }
  return OK_STATUS();
}

/**
 * External interrupt handler.
 */
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t irq_id) {
  if (devid != dt_pwrmgr_instance_id(kPwrmgrDt) ||
      irq_id != dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup)) {
    return false;
  }
  CHECK_DIF_OK(dif_pwrmgr_irq_acknowledge(&pwrmgr, kDtPwrmgrIrqWakeup));

  if (false) {
    const bool debug = false;
    usbdev_suspend_ctx_t *ctx = &suspend_ctx;
    if (debug) {
      sense_report(ctx, 2);
      LOG_INFO("Received Wakeup IRQ in sleep");
      if (debug) {
        // Report wake status immediately, to see what ES captured.
        (void)collect_wake_status(ctx);
        sense_report(ctx, 10u);
      }
    } else {
      LOG_INFO("Received Wakeup IRQ in sleep");
    }
  }
  return true;
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

static void phase_set(usbdev_suspend_ctx_t *ctx, usbdev_suspend_phase_t phase) {
  if (verbose) {
    LOG_INFO("phase_set %u (%s)", phase, phase_name(phase));
  }
  /**
   * Test descriptor; indicates to the DPI model that we're interested in
   * testing bus Suspend/Resume signaling, Reset signaling and Remote Wakeup
   * behavior.
   */
  uint8_t test_descriptor[] = {
      USB_TESTUTILS_TEST_DSCR(kUsbTestNumberSuspend,
                              (uint8_t)phase,  // Test phase
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
        LOG_INFO("SOF");
        hb = 0;
      }
    }

    // We are supplied with the SOF interrupts to help inform our decision
    // but these are normally much too frequent to be reporting them
    snapshot &= ~(1u << kDifUsbdevIrqFrame);
    if (!snapshot) {
      // If only a Frame interrupt has called, return without further reporting
      return OK_STATUS();
    }
  }

  if (false) {  // verbose && snapshot) {
                //    LOG_INFO("State %u (%s) - Link events:", ctx->test_state,
                //             state_name(ctx->test_state));
    events_report(ctx, snapshot, link_state);
    //    LOG_INFO(" events: 0x%x link 0x%x", snapshot, link_state);
  }

  // State machine anticipates the behavior of the host/DPI model, checking that
  // the expected events are reported within the expected time intervals, and
  // advances accordingly through the test states.

  switch (ctx->test_state) {
    // We're expecting the host to drop the SOF heartbeat indicating that we
    // should suspend... (STEP_IDLE_)
    case kSuspendStateWaitSuspend:
      if (snapshot & (1u << kDifUsbdevIrqLinkSuspend)) {
        state_enter(ctx, kSuspendStateWaitResume);
        timeout_set(ctx, TimeoutResumeMissed);
      }
      break;

    // After a short delay, the host should resume automatically...
    // (STEP_ACTIVE_)
    case kSuspendStateWaitResume:
      if (snapshot & (1u << kDifUsbdevIrqLinkResume)) {
        state_enter(ctx, kSuspendStateNextPhase);
      }
      break;

    // The first test phase (Suspend/Resume without AON/Wakeup involvement)
    // is terminated by a deliberate Bus Reset, advancing us to the next
    // phase.
    case kSuspendStateWaitBusReset:
      if (snapshot & (1u << kDifUsbdevIrqLinkReset)) {
        state_enter(ctx, kSuspendStateBusReset);
      }
      break;

    // This time we're expecting a much longer Suspend...
    case kSuspendStateWaitLongSuspend:
      if (snapshot & (1u << kDifUsbdevIrqLinkSuspend)) {
        state_enter(ctx, kSuspendStateWaitSuspendTimeout);
        timeout_frames_set(ctx, FramesWaitEnterSleep);
      }
      break;

    // We're _waiting for a timeout_ to occur, so we're not expecting any
    // events at this point...
    case kSuspendStateWaitSuspendTimeout:
      if (snapshot) {
        state_enter(ctx, kSuspendStateFailed);
      }
      break;

    case kSuspendStateWaitDisconnect:
      if (snapshot & (1u << kDifUsbdevIrqDisconnected)) {
        state_enter(ctx, kSuspendStateComplete);
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

    case kSuspendStatePowerOnReset:
    case kSuspendStateBusReset:
    case kSuspendStateNextPhase:
      break;

    case kSuspendStateNormalWaking:
    case kSuspendStateDeepWaking:
      break;

    // Ignore link events if we already have a verdict.
    case kSuspendStateFailed:
    case kSuspendStateComplete:
      break;

    default:
      LOG_INFO("Unknown/invalid test state %u (%s)", ctx->test_state,
               state_name(ctx->test_state));
      state_enter(ctx, kSuspendStateFailed);
      break;
  }

  if (verbose && ctx->test_state == kSuspendStateFailed) {
    LOG_INFO(" -> failed handling snapshot 0x%x with link state 0x%x\n",
             snapshot, link_state);
  }

  return OK_STATUS();
}

// TODO: redirect logging information in Verilator t-l sim because any attempt
// to use the UART will introduce long delays and break the test.
static size_t base_dev_uart(void *data, const char *buf, size_t len) {
  if (kDeviceType == kDeviceSimVerilator) {
    for (size_t i = 0; i < len; ++i) {
      *(uint32_t *)0x411f0084 = ((uint8_t *)buf)[i];
    }
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
  // Timeouts typically indicate failure.
  bool failed = true;

  switch (ctx->test_state) {
    case kSuspendStateWaitSuspend:
      if (!host_suspends) {
        LOG_INFO("auto-suspending (FPGA)");
        state_enter(ctx, kSuspendStateWaitResume);
        timeout_frames_set(ctx, FramesInitiateResume);
        failed = false;
      }
      break;

    case kSuspendStateWaitLongSuspend:
      if (!host_suspends) {
        LOG_INFO("auto-long-suspending (FPGA)");
        state_enter(ctx, kSuspendStateWaitSuspendTimeout);
        timeout_frames_set(ctx, FramesWaitEnterSleep);
        failed = false;
      }
      break;

    // Timeout is required to advance from the longer suspend state
    // because we're not expecting any host activity in this case, but
    // must initiate sleep/powerdown
    case kSuspendStateWaitSuspendTimeout:
      if (verbose) {
        LOG_INFO("set_wake_enable...");
      }
      TRY(dif_usbdev_set_wake_enable(ctx->usbdev->dev, kDifToggleEnabled));

      state_enter(ctx, kSuspendStateActivatedAON);
      timeout_frames_set(ctx, TimeoutAonResponse);
      failed = false;
      break;

    case kSuspendStateWaitResume:
      if (!host_resumes) {
        LOG_INFO("auto-resuming (host does not support Resume Signaling)");
        state_enter(ctx, kSuspendStateWaitBusReset);
        timeout_frames_set(ctx, 10000u);
        failed = false;
      }
      break;

    // Timeout
    case kSuspendStateWaitResumeTimeout:
      // TODO:
      //             timeout_frames_set(ctx, TimeoutFinishMissed);
      state_enter(ctx, kSuspendStateNextPhase);
      failed = false;
      break;

    // Timeout may also be required to advance from Wait(Long)Suspend if
    // the host does not attempt to suspend the device, in which case we
    // shall also need to transition from WaitResume automatically...
    case kSuspendStateWaitBusReset:
      if (!host_resets) {
        LOG_INFO("auto-resetting (host does not support Bus Resets)");
        // Since we don't have an actual Bus Reset we must NOT wait around
        // to be reconfigured.
        state_enter(ctx, kSuspendStateNextPhase);
        failed = false;
      }
      break;

    // Any other timeout implies that we did not receive the expected link
    // event promptly and the test has failed
    default:
      break;
  }

  if (failed) {
    LOG_INFO("Timed out in test state %u (%s)", ctx->test_state,
             state_name(ctx->test_state));
    state_enter(ctx, kSuspendStateFailed);
  }

  return OK_STATUS();
}

////////////////////////////////////////////////////////////////////////////////
// (Re)initialize the software stack
////////////////////////////////////////////////////////////////////////////////

static status_t software_init(usbdev_suspend_ctx_t *ctx) {
  if (verbose) {
    LOG_INFO("Init testutils layer in state %u (%s)", ctx->test_state,
             state_name(ctx->test_state));
  }

  // Initialize the usb_testutils layer
  // Note: when we exit a Deep Sleep via Resume Signaling we are relying
  // upon being able to set up the state of the endpoints and device
  // registers again, rather than retaining the full software state in SRAM
  TRY(usb_testutils_init(ctx->usbdev, /*pinflip=*/false,
                         /*en_diff_rcvr=*/true,
                         /*tx_use_d_se0=*/false));

  // Register our interest in link events
  TRY(usb_testutils_link_callback_register(ctx->usbdev, link_callback, ctx));

  if (ctx->with_traffic) {
    // Supply usb_testutils context to streaming library
    usbdev_streams.usbdev = ctx->usbdev;

#if 0
    // Initialize the state of the streams; do this before resuming.
    TRY(usb_testutils_streams_init(&usbdev_streams, nstreams, xfr_types,
                                   transfer_bytes, test_flags, s_verbose));
#else
    // TODO: we do nothing with this at the moment, but perhaps in time we'll
    // present it to the host via the test descriptor a la the regular
    // streaming tests (usbdev_stream/iso/mixed_test).
    uint32_t dpi_types;

    // Initialize the state of the streams; do this before resuming.
    TRY(usb_testutils_streams_typed_init(&usbdev_streams, config_descriptors,
                                         sizeof(config_descriptors), nstreams,
                                         xfr_types, transfer_bytes, test_flags,
                                         s_verbose, &dpi_types));
#endif
  }

  // Set up Endpoint Zero for Control Transfers, at which point the
  // interface becomes enabled and we must be responsive to USB traffic.
  TRY(usb_testutils_controlep_init(
      &usbdev_control, ctx->usbdev, 0, config_descriptors,
      sizeof(config_descriptors), ctx->test_dscr, sizeof(ctx->test_dscr)));

  return OK_STATUS();
}

////////////////////////////////////////////////////////////////////////////////
// Handle the initial state of a new phase, and the first state after waking
// from Deep Sleep.
////////////////////////////////////////////////////////////////////////////////

static status_t phase_start_resume(usbdev_suspend_ctx_t *ctx) {
  uint32_t timeout = FramesSuspendMissed;

  TRY_CHECK(ctx->test_state == kSuspendStateNextPhase ||
            ctx->test_state == kSuspendStateBusReset ||
            ctx->test_state == kSuspendStatePowerOnReset ||
            ctx->test_state == kSuspendStateDeepSleep);

  // If we can reuse the existing software state and device configuration for
  // this phase then we avoid reinitialization...
  if (ctx->test_state != kSuspendStateNextPhase) {
    TRY(software_init(ctx));
  }

  switch (ctx->test_state) {
    case kSuspendStatePowerOnReset:
    case kSuspendStateBusReset:
      // In this case, since we have no retention RAM, we must wait until the
      // host has reconfigured us; do not wait indefinitely, in case something
      // has gone wrong.
      if (physical_timings()) {
        timeout_set(ctx, TimeoutPhysConfig);
      } else {
        // It should take only a few bus frames even with the older, slower DPI
        // behavior.
        timeout_frames_set(ctx, 8u);
      }

      if (verbose) {
        LOG_INFO("waiting to be configured");
      }

      while (usbdev_control.device_state != kUsbTestutilsDeviceConfigured &&
             !ibex_timeout_check(&ctx->timeout)) {
        TRY(usb_testutils_poll(ctx->usbdev));
      }

      // If we're out of step with the DPI model/host, stop the test.
      TRY_CHECK(usbdev_control.device_state == kUsbTestutilsDeviceConfigured);

      // The DPI model still needs to complete the 'SET_DEVICE_CONFIG' bus frame
      // and then devote another bus frame to reading the test configuration.
      // (GET_TEST_CONFIG), so we must expect to wait longer before seeing the
      // Suspend signaling.
      timeout += FramesConfigDelay;
      break;

    case kSuspendStateNextPhase:
      // Software and device should already be up and running.
      break;

    default:
      TRY_CHECK(ctx->test_state == kSuspendStateDeepSleep);

      if (ctx->with_traffic) {
        // Reinstate the stream information, now that we've set up the basic
        // software structures for streaming.
        TRY_CHECK(ctx->retn_state.client_used <=
                  sizeof(ctx->retn_state.client_state));
        TRY(usb_testutils_streams_resume(&usbdev_streams,
                                         ctx->retn_state.client_state,
                                         ctx->retn_state.client_used));
      }

      // Collect the device address and configuration previously used.
      const uint8_t dev_address = ctx->retn_state.dev_address;
      const uint8_t dev_config = ctx->retn_state.dev_config;

      // NOTE: We have run through the usb_testutils/controlep_init sequence as
      // normal because this sets up our endpoints as they were before, whilst
      // requiring less information to be stored in the retention RAM, but we
      // must still reinstate the Data Toggle bits and the Device Address
#if USBDEV_HAVE_TOGGLE_STATE
      uint16_t out_toggles = (uint16_t)ctx->retn_state.data_toggles;
      uint16_t in_toggles = (uint16_t)(ctx->retn_state.data_toggles >> 16);
      const uint16_t mask = (uint16_t)((1u << USBDEV_NUM_ENDPOINTS) - 1u);
      CHECK_DIF_OK(dif_usbdev_data_toggle_out_write(ctx->usbdev->dev, mask,
                                                    out_toggles));
      CHECK_DIF_OK(
          dif_usbdev_data_toggle_in_write(ctx->usbdev->dev, mask, in_toggles));
#endif
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
      TRY_CHECK(link_state == kDifUsbdevLinkStatePowered ||
                link_state == kDifUsbdevLinkStateDisconnected);

      if (link_state == kDifUsbdevLinkStatePowered) {
        TRY(dif_usbdev_resume_link_to_active(ctx->usbdev->dev));
      }

#if USBDEV_HAVE_TOGGLE_STATE
      if (verbose) {
        LOG_INFO("in_toggles 0x%03x out_toggles 0x%03x", in_toggles,
                 out_toggles);
      }
#else
      if (ctx->with_traffic) {
        LOG_INFO("Warning: Unable to reinstate Data Toggle bits");
      }
#endif
      break;
  }

  // Indication that we've started.
  if (ctx->test_state != kSuspendStateNextPhase) {
    if (ctx->with_traffic) {
      if (ctx->test_state == kSuspendStateDeepSleep) {
        if (verbose) {
          LOG_INFO("Resuming streaming...");
        }
      } else {
        if (verbose) {
          LOG_INFO("Configured; starting streaming...");
        }
      }
    } else {
      if (verbose) {
        LOG_INFO("Configured; not trying to stream...");
      }
    }
  }

  // Enter the appropriate starting state based upon the test phase
  switch (ctx->test_phase) {
    case kSuspendPhaseShutdown:
      // Just disconnect from the bus and await notification via the link
      // callback handler.
      TRY(dif_usbdev_interface_enable(ctx->usbdev->dev, kDifToggleDisabled));
      state_enter(ctx, kSuspendStateWaitDisconnect);
      break;

    case kSuspendPhaseSuspend:
      state_enter(ctx, kSuspendStateWaitSuspend);
      break;

    default:
      CHECK(ctx->test_phase == kSuspendPhaseDeepDisconnect);
      OT_FALLTHROUGH_INTENDED;
    case kSuspendPhaseDeepReset:
    case kSuspendPhaseDeepResume:
      if (ctx->test_state == kSuspendStateDeepSleep) {
        state_enter(ctx, kSuspendStateDeepWaking);
        break;
      }
      // If we're starting one of the Deep phases rather than waking from
      // DeepSleep then it's the same as starting a normal Sleep phase.
      OT_FALLTHROUGH_INTENDED;
    //
    case kSuspendPhaseSleepDisconnect:
    case kSuspendPhaseSleepReset:
    case kSuspendPhaseSleepResume:
      if (host_suspends) {
        // TODO: human intervention required presently
        //        timeout *= 2000;
      }
      state_enter(ctx, kSuspendStateWaitLongSuspend);
      break;
  }
  // Initialize timeout to catch any failure of the host to suspend the bus
  timeout_frames_set(ctx, timeout);

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
  switch (ctx->test_state) {
    case kSuspendStateActivatedAON:
      // Since the AON/Wakeup operates on a low clock frequency, it may
      // take some time for it to become active....await its signal
      TRY(collect_wake_status(ctx));
      if (ctx->wake_status.active) {
        // Retain our state information
        TRY(dif_usbdev_address_get(ctx->usbdev->dev,
                                   &ctx->retn_state.dev_address));
        ctx->retn_state.dev_config = usbdev_control.usb_config;
        ctx->retn_state.test_phase = (uint8_t)ctx->test_phase;
        // Remember the number of remaining iterations.
        ctx->retn_state.num_iters = ctx->num_iters;
#if USBDEV_HAVE_TOGGLE_STATE
        // Capture all current Data Toggle bits
        uint16_t out_toggles, in_toggles;
        TRY(dif_usbdev_data_toggle_out_read(ctx->usbdev->dev, &out_toggles));
        TRY(dif_usbdev_data_toggle_in_read(ctx->usbdev->dev, &in_toggles));
        ctx->retn_state.data_toggles =
            ((uint32_t)in_toggles << 16) | out_toggles;
#else
        ctx->retn_state.data_toggles = 0U;
#endif
        if (verbose) {
          LOG_INFO(" - retaining address %u config %u phase %u (%s)",
                   ctx->retn_state.dev_address, ctx->retn_state.dev_config,
                   ctx->retn_state.test_phase,
                   phase_name(ctx->retn_state.test_phase));
        }

        if (ctx->with_traffic) {
          // Store any state information that is necessary to resume streaming.
          unsigned used;
          TRY(usb_testutils_streams_suspend(
              &usbdev_streams, ctx->retn_state.client_state,
              sizeof(ctx->retn_state.client_state), &used));
          TRY_CHECK(used <= sizeof(ctx->retn_state.client_state));
          ctx->retn_state.client_used = used;
        }

        retention_sram_store(&ctx->retn_state);

        // TODO: migrate this into a subfunction
        // Enter low power mode; note that on some targets we may be unable to
        // produce the appropriate stimuli so we have to skip over the sleep
        // state.
        bool can_awaken = true;
        switch (ctx->test_phase) {
          case kSuspendPhaseSleepReset:
          case kSuspendPhaseDeepReset:
            if (!host_resets) {
              if (verbose) {
                LOG_INFO("auto-skipping WFI (host does not support Bus Resets");
              }
              can_awaken = false;
            }
            break;

          case kSuspendPhaseSleepDisconnect:
          case kSuspendPhaseDeepDisconnect:
            if (!host_disconnects) {
              if (verbose) {
                LOG_INFO(
                    "auto-skipping WFI (host does not support Disconnects");
              }
              can_awaken = false;
            }
            break;

          default:
            TRY_CHECK(ctx->test_phase == kSuspendPhaseSleepResume ||
                      ctx->test_phase == kSuspendPhaseDeepResume);
            if (!host_resumes) {
              if (verbose) {
                LOG_INFO(
                    "auto-skipping WFI (host does not support Resume "
                    "Signaling");
              }
              can_awaken = false;
            }
            break;
        }

        if (can_awaken) {
          if (ctx->test_phase == kSuspendPhaseDeepResume ||
              ctx->test_phase == kSuspendPhaseDeepReset ||
              ctx->test_phase == kSuspendPhaseDeepDisconnect) {
            if (verbose) {
              LOG_INFO("Requesting Deep sleep");
            }

            // Deep sleep.
            //
            // Note: we must keep the 'Active USB clock enable' bit set,
            // because otherwise when we return to the active state, the
            // usbdev clock will not be restored.
            TRY(pwrmgr_testutils_enable_low_power(
                &pwrmgr, wakeup_sources,
                /*domain_config=*/
                kDifPwrmgrDomainOptionUsbClockInActivePower));

            // Record that we've asked to power down; timeout should never
            // occur.
            state_enter(ctx, kSuspendStateDeepSleep);
            timeout_frames_set(ctx, TimeoutSleepFailed);
          } else {
            LOG_INFO("Requesting Normal sleep");

            // Normal sleep.
            TRY(pwrmgr_testutils_enable_low_power(
                &pwrmgr, /*wakeups=*/wakeup_sources,
                /*domain_config=*/
                kDifPwrmgrDomainOptionCoreClockInLowPower |
                    kDifPwrmgrDomainOptionUsbClockInActivePower |
                    kDifPwrmgrDomainOptionMainPowerInLowPower));

            // Record that we've asked to enter lower power mode; timeout
            // should never occur.
            state_enter(ctx, kSuspendStateNormalSleep);
            timeout_frames_set(ctx, TimeoutSleepFailed);
          }

          // With a physical host (FPGA) some manual intervention is required.
          const char *action = "";
          if (physical_timings()) {
            switch (ctx->test_phase) {
              case kSuspendPhaseSleepReset:
              case kSuspendPhaseDeepReset:
                action = "; please Reset the device.";
                break;
              case kSuspendPhaseSleepDisconnect:
              case kSuspendPhaseDeepDisconnect:
                action = "; please disconnect and reconnect the USB cable.";
                break;
              default:
                break;
            }
          }
          // sense_report(ctx, 10);
          if (verbose) {
            LOG_INFO("Issuing WFI to enter sleep%s", action);
          }
          wait_for_interrupt();

          // Check that a DeepSleep request did not somehow run past the
          // WFI...
          TRY_CHECK(ctx->test_state == kSuspendStateNormalSleep);
        }

        //---------------------------------------------------------------
        // After a Normal sleep, we resume execution here; after a Deep
        // sleep we start again as if from a Power On Reset, but the
        // pwrmgr tells us otherwise.
        //---------------------------------------------------------------

        // TODO: check the IRQ source in the event of a Normal Sleep and
        // proceeding past the WFI

        // ... and we should be in one of these test phases.
        TRY_CHECK(ctx->retn_state.test_phase == kSuspendPhaseSleepResume ||
                  ctx->retn_state.test_phase == kSuspendPhaseSleepReset ||
                  ctx->retn_state.test_phase == kSuspendPhaseSleepDisconnect ||
                  (!host_resumes &&
                   ctx->retn_state.test_phase == kSuspendPhaseDeepResume) ||
                  (!host_resets &&
                   ctx->retn_state.test_phase == kSuspendPhaseDeepReset) ||
                  (!host_disconnects &&
                   ctx->retn_state.test_phase == kSuspendPhaseDeepDisconnect));

        // Retrieve it and check; just additional testing.
        usbdev_retn_state_t stored_state;
        retention_sram_load(&stored_state);
        if (verbose) {
          LOG_INFO(" - retained address %u config %u phase %u (%s)",
                   stored_state.dev_address, stored_state.dev_config,
                   stored_state.test_phase,
                   phase_name(stored_state.test_phase));
        }

        // Check that the Retention SRAM did its job over Normal Sleep at least;
        // the SRAM should remain powered and clocked so this should not be
        // challenging.
        TRY_CHECK(stored_state.dev_address == ctx->retn_state.dev_address &&
                  stored_state.dev_config == ctx->retn_state.dev_config &&
                  stored_state.test_phase == ctx->retn_state.test_phase &&
                  stored_state.num_iters == ctx->retn_state.num_iters &&
                  stored_state.data_toggles == ctx->retn_state.data_toggles);

        dif_pwrmgr_wakeup_reason_t wakeup_reason;
        TRY(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));

        if (verbose) {
          LOG_INFO("wakeup types 0x%x sources 0x%x", wakeup_reason.types,
                   wakeup_reason.request_sources);
        }

        state_enter(ctx, kSuspendStateNormalWaking);
        // We just need to previous spurious timeouts at this point.
        timeout_frames_set(ctx, TimeoutSleepFailed);
      }
      break;

    case kSuspendStateNormalWaking:
    case kSuspendStateDeepWaking:
      // We've returned from sleeping; enquire of the USB AON Wake module
      // what happened...
      TRY(collect_wake_status(ctx));

      // There are three ways that we may exit from Deep Sleep in which
      // the AON/Wake module has been handling the bus:
      // - Disconnecion (loss of VBUS/SENSE)
      // - Bus Reset (from host)
      // - Non-Idle state detected (Resume Signaling; this is inferred by
      //   neither of the other two conditions having occurred.)
      //   Resume signaling shall last at last 20ms, but the AON/Wake
      //   module alerts us long before that time has elapsed.

      // Check the report from the AON/Wakeup module
      if (ctx->wake_status.active) {
        bool got_signal = false;

        switch (ctx->test_phase) {
          case kSuspendPhaseSleepResume:
          case kSuspendPhaseDeepResume:
            got_signal = !host_resumes || (ctx->wake_status.bus_not_idle != 0);
            break;

          case kSuspendPhaseSleepReset:
          case kSuspendPhaseDeepReset:
            got_signal = !host_resets || (ctx->wake_status.bus_reset != 0);
            break;

          default:
            TRY_CHECK(ctx->test_phase == kSuspendPhaseDeepDisconnect);
            OT_FALLTHROUGH_INTENDED;
          case kSuspendPhaseSleepDisconnect:
            got_signal =
                !host_disconnects || (ctx->wake_status.disconnected != 0);
            break;
        }

        if (got_signal) {
          // TODO: Issue #18562 VBUS Disconnection leaves pull ups asserted
          // by the USB AON Wake module, so disconnect them here before
          // potential confusion results.
          if (ctx->wake_status.disconnected) {
            bool sense;

            TRY(dif_usbdev_status_get_sense(ctx->usbdev->dev, &sense));
            if (verbose) {
              LOG_INFO("Handling Disconnection when VBUS %sasserted",
                       sense ? "" : "de-");
            }

            // TODO: experimental test code! DO NOT MERGE
            if (false) {
              static uint8_t buf[4096];
              extern void usbutils_gather(dif_usbdev_t * dev, uint8_t * buf,
                                          size_t n);

              while (!sense) {
                TRY(dif_usbdev_status_get_sense(ctx->usbdev->dev, &sense));
              }

              usbutils_gather(ctx->usbdev->dev, buf, sizeof(buf));
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

          // Although it operates at only 200kHz, it should't take long
          state_enter(ctx, kSuspendStateAONWakeup);
          timeout_frames_set(ctx, TimeoutAonResponse);
        } else {
          LOG_INFO("Unexpected report from USB AON Wake module");
          report_wake_status(ctx);
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
      TRY(collect_wake_status(ctx));
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
            state_enter(ctx, host_disconnects ? kSuspendStatePowerOnReset
                                              : kSuspendStateNextPhase);
            break;

          case kSuspendPhaseSleepReset:
          case kSuspendPhaseDeepReset:
            // TODO: Check! Reset Signaling is still ongoing at this point?
            // state_enter(ctx, kSuspendStateWaitBusReset);
            state_enter(ctx, kSuspendStateBusReset);
            break;

          default:
            TRY_CHECK(ctx->test_phase == kSuspendPhaseDeepResume);
            OT_FALLTHROUGH_INTENDED;
          case kSuspendPhaseSleepResume:
            state_enter(ctx, kSuspendStateWaitResumeTimeout);
            timeout_set(ctx, TimeoutWakeupResume);
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

    // Phase-initial/-final states in which we don't need to do anything here.
    case kSuspendStatePowerOnReset:
    case kSuspendStateBusReset:
    case kSuspendStateNextPhase:
    case kSuspendStateComplete:
    case kSuspendStateFailed:
      break;

    // Verdict already decided.

    // States in which we sit waiting - with a timeout - for something
    // significant to happen...
    default:
      TRY_CHECK(ctx->test_state == kSuspendStateWaitResumeTimeout);
      OT_FALLTHROUGH_INTENDED;
    case kSuspendStateWaitSuspend:
    case kSuspendStateWaitResume:
    case kSuspendStateWaitBusReset:
    case kSuspendStateWaitLongSuspend:
    case kSuspendStateWaitSuspendTimeout:
    case kSuspendStateWaitDisconnect:
      break;
  }

  return OK_STATUS();
}

/**
 * Run a single test phase to completion
 */
static status_t phase_run(usbdev_suspend_ctx_t *ctx) {
  bool send_progress = (ctx->test_state != kSuspendStateDeepSleep);
  bool phase_done = false;

  // Handle the phase-initial state or resuming from Deep Sleep and continuing
  // in the present phase.
  TRY(phase_start_resume(ctx));

  if (send_progress) {
    report_progress("Phase awaiting stimulus (%s)",
                    phase_name(ctx->test_phase));
  }

  switch (ctx->test_state) {
    case kSuspendStateBusReset:
    case kSuspendStateNextPhase:
    case kSuspendStatePowerOnReset:
    case kSuspendStateComplete:
    case kSuspendStateFailed:
      LOG_INFO(
          "Phase-initial state %u (%s) should have been handled in "
          "phase_start()",
          ctx->test_state, state_name(ctx->test_state));
      return FAILED_PRECONDITION();
    default:
      break;
  }

  // The DPI model and our callback handler for USB link events do most of the
  // work of walking through the test states until completion
  do {
    if (ibex_timeout_check(&ctx->timeout)) {
      TRY(timeout_handle(ctx));
    } else {
      TRY(state_service(ctx));
    }

    switch (ctx->test_state) {
      // These states terminate the phase, either advancing to the next phase
      // or terminating the test sequence.
      case kSuspendStateBusReset:
      case kSuspendStateNextPhase:
      case kSuspendStatePowerOnReset:
      case kSuspendStateComplete:  // from PhaseShutdown only
      case kSuspendStateFailed:    // from any phase
        phase_done = true;
        break;

      // Do not poll the USB device or perform traffic in these states.
      case kSuspendStateActivatedAON:
      case kSuspendStateAONWakeup:
      case kSuspendStateDeepSleep:
      case kSuspendStateNormalSleep:
        break;

      // TODO:
      case kSuspendStateWaitResume:
        // No traffic, but we must still poll the usb_testutils layer to
        // handle hardware events and callbacks.
        TRY(usb_testutils_poll(ctx->usbdev));
        break;

      default:
        if (ctx->with_traffic) {
          // Servicing streams handles usbdev/testutils events for us.
          //
          // TODO: streaming code has been integrated, but it would probably be
          // quite useful to be able to see the device streaming activity too,
          // not just that of the host side?
          TRY(usb_testutils_streams_service(&usbdev_streams));
        } else {
          // No traffic, but we must still poll the usb_testutils layer to
          // handle hardware events and callbacks.
          TRY(usb_testutils_poll(ctx->usbdev));
        }
        break;
    }
  } while (!phase_done);

  // Advance to next phase, unless we have just completed the final phase or
  // the test has failed.
  switch (ctx->test_state) {
    case kSuspendStatePowerOnReset:
    case kSuspendStateBusReset:
    case kSuspendStateNextPhase: {
      // Was this the final phase of the test?
      usbdev_suspend_phase_t next_phase =
          (usbdev_suspend_phase_t)(ctx->test_phase + 1u);
      bool completed = false;
      if (ctx->test_phase == ctx->fin_phase) {
        if (ctx->num_iters == USBDEV_SUSPEND_ETERNAL || --ctx->num_iters > 0u) {
          LOG_INFO("Rewinding to initial phase");
          if (ctx->num_iters > 0u) {
            LOG_INFO(" - %u iteration(s) remaining", ctx->num_iters);
          }
          next_phase = ctx->init_phase;
        } else {
          completed = true;
        }
      }
      // Have we completed the entire test?
      if (completed) {
        state_enter(ctx, kSuspendStateComplete);
      } else {
        // Advance to the next test phase, or rewind for the next iteration.
        phase_set(ctx, next_phase);
      }
    } break;

    default:
      TRY_CHECK(ctx->test_state == kSuspendStateComplete ||
                ctx->test_state == kSuspendStateFailed);
      break;
  }

  return OK_STATUS();
}

bool usbdev_suspend_test(usbdev_suspend_phase_t init_phase,
                         usbdev_suspend_phase_t fin_phase, uint32_t num_iters,
                         bool with_traffic) {
  usbdev_suspend_ctx_t *ctx = &suspend_ctx;

  // Wipe out any memory from the previous test phase, just to be more confident
  // that we really are resuming from Deep Sleep and using only the Retention
  // SRAM contents to resume.
  //
  // This also means that the data we subsequently store in the Retention SRAM
  // has defined values for the unused padding fields.
  memset(ctx, 0, sizeof(*ctx));

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Remember the phase in which we are to stop.
  CHECK(fin_phase >= init_phase);
  ctx->init_phase = init_phase;
  ctx->fin_phase = fin_phase;

  // Default behavior - for simulation with the DPI - is that all types of
  // signaling can be performed, in response to reading the test description.
  host_suspends = true;
  host_resumes = true;
  host_resets = true;
  host_disconnects = true;

  // DPI model can perform traffic and will deliberately avoid performing
  // traffic during the periods when it stops sending the bus frames

  // Override any of the above switches according to the build target.
  switch (kDeviceType) {
    case kDeviceSimVerilator:
      // steal the UART output and send it via a faster mechanism
      base_set_stdout(base_stdout);
      verbose = true;

#if !USBDPI_FULL_FRAME
      frame_interval = 500u;  // Reduce to 0.5ms to shorten simulation time.
#endif
      break;

    // Do NOT steal the UART output in this case because DVsim has a back door
    // for rapid logging.
    case kDeviceSimDV:
      verbose = true;
      break;

    case kDeviceSilicon:
      // Silicon targets are presently tested with the use of the HyperDebug
      // board for control over the VBUS connection.
      // Suspend, Resume and Reset operations all rely upon control of the
      // parent USB hub.
      host_suspends = true;
      host_resumes = true;
      host_resets = true;
      host_disconnects = true;
      verbose = false;
      break;

    default:
      CHECK(kDeviceType == kDeviceFpgaCw310);
      OT_FALLTHROUGH_INTENDED;
    case kDeviceFpgaCw340:
      // FPGA host can be used to perform Bus Resets and (with hoop-jumping)
      // Suspend and Resume. With physical intervention or perhaps a capable
      // hub it can perform VBUS Disconnects; such hubs are a rare minority,
      // however.
      host_suspends = true;
      host_resumes = true;
      host_resets = true;
      // this must still be exercised manually with FPGA boards.
      host_disconnects = false;

      // Presently, the FPGA build is expected to be observed/monitored by a
      // developer, so verbose reporting is appropriate.
      verbose = false;  // true;
      break;
  }

  ctx->with_traffic = with_traffic;

  // Initialize pinmux.
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));
  pinmux_testutils_init(&pinmux);
  CHECK_DIF_OK(dif_pinmux_input_select(
      &pinmux, kTopEarlgreyPinmuxPeripheralInUsbdevSense,
      kTopEarlgreyPinmuxInselIoc7));

  // Initialize pwrmgr.
  CHECK_DIF_OK(dif_pwrmgr_init_from_dt(kPwrmgrDt, &pwrmgr));

  // Initialize the PLIC.
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &rv_plic));

  // Initialize rstmgr
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kRstmgrDt, &rstmgr));

  // Enable all the AON interrupts used in this test.
  dif_rv_plic_irq_id_t irq_id =
      dt_pwrmgr_irq_to_plic_id(kPwrmgrDt, kDtPwrmgrIrqWakeup);
  rv_plic_testutils_irq_range_enable(&rv_plic, kPlicTarget, irq_id, irq_id);

  // The USB wakeup signal comes from the pinmux.
  CHECK_DIF_OK(dif_pwrmgr_find_request_source(
      &pwrmgr, kDifPwrmgrReqTypeWakeup, dt_pinmux_instance_id(kPinmuxDt),
      kDtPinmuxWakeupUsbWkupReq, &wakeup_sources));

  // Enable pwrmgr interrupt.
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Check if there was a HW reset caused by the wdog bite.
  dif_rstmgr_reset_info_bitfield_t rst_info = rstmgr_testutils_reason_get();
  rstmgr_testutils_reason_clear();

  // Initialize testing context and state machine
  ctx->usbdev = &usbdev;

  if (rst_info == kDifRstmgrResetInfoPor) {
    const char *iters = "eternally";
    static char buf[20];

    report_progress("Running USBDEV_SUSPEND test");

    // Remember the requested iteration count.
    ctx->num_iters = num_iters;

    // Report the iteration count
    if (num_iters != USBDEV_SUSPEND_ETERNAL) {
      base_snprintf(buf, sizeof(buf), "%u times", num_iters);
      iters = buf;
    }
    LOG_INFO("  (seq: %s to %s %s with%s traffic)", phase_name(init_phase),
             phase_name(ctx->fin_phase), iters, ctx->with_traffic ? "" : "out");

    // Power On Reset
    LOG_INFO("Booting for the first time");

    phase_set(ctx, init_phase);
    state_enter(ctx, kSuspendStatePowerOnReset);
  } else {
    if (verbose) {
      // Avoid UART-based logging as much as possible because producing UART
      // traffic will stall the CPU waiting on FIFO space, and that can lead to
      // USB timeouts when attempting to Resume from Deep Sleep.
      LOG_INFO("Resuming from power down!");
    }

    // Recover state from the retention RAM
    retention_sram_load(&ctx->retn_state);
    if (verbose) {
      LOG_INFO(" - retained address %u config %u phase %u (%s)",
               ctx->retn_state.dev_address, ctx->retn_state.dev_config,
               ctx->retn_state.test_phase,
               phase_name(ctx->retn_state.test_phase));
    }

    // To have arrived we should be in one of these test phases and we should
    // have been in kSuspendStateDeepSleep, so we have not retained that.
    CHECK(ctx->retn_state.test_phase == kSuspendPhaseDeepResume ||
          ctx->retn_state.test_phase == kSuspendPhaseDeepReset ||
          ctx->retn_state.test_phase == kSuspendPhaseDeepDisconnect);

    // We can - presently - check the other parameters; revise/remove this code
    // if the configuration becomes more variable.
    CHECK(ctx->retn_state.dev_config == 1u);

    // Reinstate the remaining test iteration count from the retained state.
    ctx->num_iters = ctx->retn_state.num_iters;

    // We must remain in the DeepSleep state in order to reinitialize the
    // software, run through AON Wake deactivation and then check the reason
    // for waking.
    phase_set(ctx, ctx->retn_state.test_phase);
    state_enter(ctx, kSuspendStateDeepSleep);
  }

  do {
    // Run this test phase
    CHECK_STATUS_OK(phase_run(ctx));

    // Keep going if we're advancing to the next phase.
    //  (NextPhase means that we advance whilst still active and can thus skip
    //   device setup and configuratinon)
  } while (ctx->test_state == kSuspendStateNextPhase ||    // from Resume
           ctx->test_state == kSuspendStateBusReset ||     // after Bus Reset
           ctx->test_state == kSuspendStatePowerOnReset);  // after Disconnect

  if (verbose) {
    LOG_INFO("Test concluding (%s)", state_name(ctx->test_state));
  }

  // Wait enough for a SOF (>1ms) and tear down the software stack.
  // Note: there is no finalization code for the streaming at present, because
  // it has no resources to release.
  busy_spin_micros(1000);
  CHECK_STATUS_OK(usb_testutils_fin(ctx->usbdev));

#if USBUTILS_FUNCTION_POINTS && USBUTILS_FUNCPT_USE_BUFFER
  if (false) {
    usbutils_funcpt_report();
  }
#endif

  return (ctx->test_state == kSuspendStateComplete);
}
