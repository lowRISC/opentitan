// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I3C loopback test.
//
// The OpenTitan deployment of the I3C IP block restricts each instance to
// operating _either_ as a Primary Controller or as a Target (offering
// support for up to 2 Virtual Targets).
//
// To perform a loopback test we must therefore employ two instances.

#include <assert.h>

#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/i3c_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#define MODULE_ID MAKE_MODULE_ID('i', '3', 'l')

// Note: this size is presently constrained by the size of the Target Rx Buffer.
#define TEST_BUF_WORDS 0x90u

// Simple LFSR for 32-bit sequences.
// Note: zero is an isolated state that shall be avoided.
#define LFSR_ADVANCE(lfsr) \
  (((lfsr) << 1) |         \
   (((lfsr) ^ ((lfsr) >> 1) ^ ((lfsr) >> 21) ^ ((lfsr) >> 31)) & 1U))

// TODO: We presently do not use interrupts in this test; extend it to permit
// selection between polling and interrupts.
static const dt_i3c_t kI3cCtrlDt = 0;
static const dt_i3c_t kI3cTargDt = 0;
static_assert(kDtI3cCount >= 1, "This test expects at least one I3C block.");

/**
 * Configuration settings for this test.
 */
static const uint8_t static_addr = 0x1bu;
static const dif_i3c_cmd_mode_t mode = kDifI3CCmdMode_HDRDDR;

/**
 * Interrupt access.
 */
// static dif_rv_plic_t rv_plic;

/**
 * Pinmux handle
 */
static dif_pinmux_t pinmux;

// Context for the I3C Controller.
static i3c_testutils_ctx_t ctx_ctrl;
// Context for the I3C Target.
static i3c_testutils_ctx_t ctx_targ;

// Buffer of test data.
// TODO: This is still used for the Target end presently, though we should
// probably switch to on-the-fly checking and generation at the Target too.
static uint32_t buf[TEST_BUF_WORDS];

// Verbose diagnostic/debug logging?
static const bool kLogging = true;

// TODO: These state structures will probably require more info later,
// e.g., access to the `i3c_testutils_ctx_t` structure.
typedef struct {
  uint32_t lfsr;
} src_state_t;

typedef struct {
  uint32_t lfsr;
} sink_state_t;

// Interrupt handler, overriding the stub function in OTTF.
bool ottf_handle_irq(uint32_t *exc_info, dt_instance_id_t devid,
                     dif_rv_plic_irq_id_t plic_id) {
  if (devid == dt_i3c_instance_id(kI3cCtrlDt)) {
    i3c_testutils_isr(&ctx_ctrl);
    return true;
  } else if (devid == dt_i3c_instance_id(kI3cTargDt)) {
    i3c_testutils_isr(&ctx_targ);
    return true;
  }
  return false;
}

OTTF_DEFINE_TEST_CONFIG();

// Generate a sequence of pseudo-random 32-bit DWORDs.
static uint32_t prng_generate(uint32_t *buf, size_t n, uint32_t lfsr) {
  for (unsigned idx = 0u; idx < n; ++idx) {
    buf[idx] = lfsr;
    lfsr = LFSR_ADVANCE(lfsr);
  }
  return lfsr;
}

// Check data against an expected sequence of pseudo-random 32-bit DWORDs.
static status_t prng_check(uint32_t *buf, size_t n, uint32_t *plfsr) {
  uint32_t lfsr = *plfsr;
  for (unsigned idx = 0u; idx < n; ++idx) {
    TRY_CHECK(buf[idx] == lfsr);
    lfsr = LFSR_ADVANCE(lfsr);
  }
  *plfsr = lfsr;
  return OK_STATUS();
}

// Generate a stream of pseudo-random 32-bit DWORDs on-the-fly.
static dif_result_t data_src(void *ws, uint32_t *pd) {
  src_state_t *src = (src_state_t *)ws;
  *pd = src->lfsr;
  src->lfsr = LFSR_ADVANCE(src->lfsr);
  return kDifOk;
}

// On-the-fly checking of 32-bit DWORDs against the pseudo-random expectations.
static dif_result_t data_sink(void *ws, uint32_t d) {
  sink_state_t *sink = (sink_state_t *)ws;
  uint32_t exp = sink->lfsr;
  sink->lfsr = LFSR_ADVANCE(exp);
  if (kLogging && exp != d) {
    LOG_INFO("data_sink mismatch 0x%x 0x%x", exp, d);
  }
  return (exp == d) ? kDifOk : kDifError;
}

bool test_main(void) {
  LOG_INFO("Running i3c_loopback_test");

  switch (kDeviceType) {
    case kDeviceSimDV:
      OT_FALLTHROUGH_INTENDED;
    case kDeviceFpgaCw340:
      break;
    default:
      LOG_FATAL("Supported platforms: DV and CW340");
      return false;
  }

  // Connect the two I3C instances using the pinmux, and wiring in the test bench.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);

  for (dt_i3c_t i3c = 0; i3c < kDtI3cCount; ++i3c) {
    dt_instance_id_t inst_id = dt_i3c_instance_id(i3c);
    dt_i3c_t i3c_dt = dt_i3c_from_instance_id(inst_id);

    // Get peripheral I/O descriptions for SDA Pull-up, SDA and SCL
    dt_periph_io_t sda_pu_periph_io =
        dt_i3c_periph_io(i3c_dt, kDtI3cPeriphIoCtrlSdaPu);
    dt_periph_io_t sda_periph_io = dt_i3c_periph_io(i3c_dt, kDtI3cPeriphIoSda);
    dt_periph_io_t scl_periph_io = dt_i3c_periph_io(i3c_dt, kDtI3cPeriphIoScl);

    // Get the appropriate pads for this I3C instance and platform
    // TODO: This should be sufficient for now but more generally we should be platform-agnostic
    // and able to handle a different instance count.
    dt_pad_t sda_pu_pad, sda_pad, scl_pad;
    switch (i3c) {
      // I3C0 is on IOB11 (SCL) and IOB12 (SDA) only
      case 0:
        sda_pu_pad = kDtPadIob8;  // TODO: May be wildly inappropriate.
        scl_pad = kDtPadIob11;
        sda_pad = kDtPadIob12;
        break;
      // I3C1 can be moved from IOB9/10 to IOB11/12.
      default:
        sda_pu_pad = kDtPadIob7;  // TODO: May be wildly inappropriate.
        scl_pad = kDtPadIob9;
        sda_pad = kDtPadIob10;
        break;
    }

    CHECK_STATUS_OK(pinmux_testutils_connect(&pinmux, scl_periph_io,
                                             kDtPeriphIoDirInout, scl_pad));
    CHECK_STATUS_OK(pinmux_testutils_connect(&pinmux, sda_periph_io,
                                             kDtPeriphIoDirInout, sda_pad));
    CHECK_STATUS_OK(pinmux_testutils_connect(&pinmux, sda_pu_periph_io,
                                             kDtPeriphIoDirOut, sda_pu_pad));

    dif_pinmux_pad_attr_t sda_pad_attrs;
    CHECK_DIF_OK(dif_pinmux_pad_get_attrs_dt(&pinmux, sda_pad, &sda_pad_attrs));
    sda_pad_attrs.drive_strength = 1u;  // `strong` drive strength.
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs_dt(&pinmux, sda_pad, sda_pad_attrs, &sda_pad_attrs));

    // Ensure that Open Drain support is disabled for all pins; remove kDifPinmuxPadAttrOpenDrain.
    pinmux_pad_attributes_t pad_attrs[2];
    pad_attrs[0].pad = scl_pad;
    pad_attrs[0].flags = 0u;
    pad_attrs[1].pad = sda_pad;
    pad_attrs[1].flags = 0u;
    pinmux_testutils_configure_pads(&pinmux, pad_attrs, 2u);
  }

  for (unsigned inst_ctrl = 0u; inst_ctrl < kDtI3cCount; ++inst_ctrl) {
    for (unsigned inst_targ = 0u; inst_targ < kDtI3cCount; ++inst_targ) {
      if (inst_targ == inst_ctrl)
        continue;

      LOG_INFO("Controller: instance %u <-> Target: instance %u", inst_ctrl,
               inst_targ);

      // Configure a single Virtual Target at static address 0x1b.
      ctx_targ.targ_cfg[0].static_addr_valid = true;
      ctx_targ.targ_cfg[0].static_addr = static_addr;

      // Set up the Controller and Target.
      // - these should be separate I3C instances.
      CHECK_STATUS_OK(i3c_testutils_init(&ctx_ctrl, inst_ctrl,
                                         kI3CCtrlMode_Active, 0u, false));
      CHECK_STATUS_OK(i3c_testutils_init(&ctx_targ, inst_targ,
                                         kI3CCtrlMode_Disabled, 1u, false));

      // Describe the target.
      CHECK_STATUS_OK(i3c_testutils_target_add(&ctx_ctrl, static_addr));

      sink_state_t sink_state;
      src_state_t src_state;

      src_state.lfsr = 1u;

      // Maximum length transfer.
      const uint16_t len = TEST_BUF_WORDS * 4;

      // Generate the write data on-the-fly, allowing us to exercise maximum
      // length transfers.
      i3c_testutils_src_t src;
      src.buf = NULL;
      src.cb_fn = data_src;
      src.cb_handle = &src_state;

      CHECK_STATUS_OK(
          i3c_testutils_write(&ctx_ctrl, static_addr, &src, len, mode));

      i3c_testutils_privw_flags_t rx_flags;
      dif_i3c_tti_rx_desc_t rx_desc;
      do {
        // TODO: This API requires that we specify the maximum received data
        // too.
        CHECK_STATUS_OK(i3c_testutils_private_write_collect(&ctx_targ, &rx_desc,
                                                            buf, TEST_BUF_WORDS,
                                                            &rx_flags));
      } while (!(rx_flags & kI3CTestUtilsPrivWFlags_Collected));

      // Check the received data matches.
      if (kLogging) {
        LOG_INFO("rx_desc %x", rx_desc);
      }
      uint32_t lfsr = 1u;
      CHECK_STATUS_OK(prng_check(buf, TEST_BUF_WORDS, &lfsr));

      /*
        uint32_t exp = 1u;
        for (unsigned idx = 0u; idx < TEST_BUF_WORDS; ++idx) {
          LOG_INFO("act %x exp %x --- %c", buf[idx], exp, exp == buf[idx] ? 'Y'
        : 'N'); exp = LFSR_ADVANCE(exp);
        }
      */

      i3c_testutils_sink_t sink;
      sink.buf = NULL;
      sink.cb_fn = data_sink;
      sink.cb_handle = &sink_state;
      sink_state.lfsr = lfsr;

      // Replace the buffer contents with fresh data, by allowing the LFSR to
      // proceed.
      // TODO: We can only send 128 words back because the Target TX buffer is
      // smaller and the software does not stream at present; streaming has
      // been demonstrated in block level simulation.
      const uint16_t ttx_len = 0x80 * 4;
      lfsr = prng_generate(buf, 0x80, lfsr);

      // Set up Tx Descriptor and Data.
      dif_i3c_tti_tx_desc_t tx_desc;
      memset(&tx_desc, 0u,
             sizeof(tx_desc));  // Including `notify`, so it's a Private Read.
      tx_desc.tx.wroc = 1u;
      tx_desc.tx.tid = 0x7u;
      tx_desc.tx.data_length = ttx_len;
      CHECK_STATUS_OK(
          i3c_testutils_private_read_setup(&ctx_targ, 0u, &tx_desc, buf));

      // Perform a Read Transfer, moving data from the Target to the Controller.
      CHECK_STATUS_OK(i3c_testutils_read(&ctx_ctrl, static_addr, &sink, ttx_len,
                                         mode, NULL));

      // Finalize the I3C access and release all resources.
      CHECK_STATUS_OK(i3c_testutils_fin(&ctx_targ));
      CHECK_STATUS_OK(i3c_testutils_fin(&ctx_ctrl));
    }
  }

  return true;
}
