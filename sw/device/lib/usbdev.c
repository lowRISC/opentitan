// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/usbdev.h"


#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "usbdev_regs.h"  // Generated.

#define USBDEV_BASE_ADDR TOP_EARLGREY_USBDEV_BASE_ADDR

#define EXTRACT(n, f) ((n >> USBDEV_##f##_OFFSET) & USBDEV_##f##_MASK)

#define SETBIT(val, bit) (val | 1 << bit)
#define CLRBIT(val, bit) (val & ~(1 << bit))

#define REG32(add) *((volatile uint32_t *)(add))

// Free buffer pool is held on a simple stack
// Initalize to all buffer IDs are free
static void buf_init(usbdev_ctx_t *ctx) {
  for (int i = 0; i < NUM_BUFS; i++) {
    ctx->freebuf[i] = i;
  }
  ctx->nfree = NUM_BUFS;
}

// Allocating a buffer just pops next ID from the stack
usbbufid_t usbdev_buf_allocate_byid(usbdev_ctx_t *ctx) {
  if (ctx->nfree <= 0) {
    return -1;
  }
  return ctx->freebuf[--ctx->nfree];
}

// Freeing a buffer just pushes the ID back on the stack
int usbdev_buf_free_byid(usbdev_ctx_t *ctx, usbbufid_t buf) {
  if ((ctx->nfree >= NUM_BUFS) || (buf >= NUM_BUFS)) {
    return -1;
  }
  ctx->freebuf[ctx->nfree++] = buf;
  return 0;
}

uint32_t *usbdev_buf_idtoaddr(usbdev_ctx_t *ctx, usbbufid_t buf) {
  return (uint32_t *)(USBDEV_BASE_ADDR + USBDEV_BUFFER_REG_OFFSET +
                      (buf * BUF_LENGTH));
}

void usbdev_buf_copyto_byid(usbdev_ctx_t *ctx, usbbufid_t buf, const void *from,
                            size_t len_bytes) {
  int32_t *from_word = (int32_t *)from;
  int len_words;
  volatile uint32_t *bp = usbdev_buf_idtoaddr(ctx, buf);

  if (len_bytes > BUF_LENGTH) {
    len_bytes = BUF_LENGTH;
  }
  // This will round up if len_bytes is not on a multiple of int32_t
  // Always ok to fill the extra bytes since the buffers are aligned
  len_words = (len_bytes + sizeof(int32_t) - 1) / sizeof(int32_t);
  for (int i = 0; i < len_words; i++) {
    bp[i] = from_word[i];
  }
}

// Supply as many buffers to the receive available fifo as possible
inline static void fill_av_fifo(usbdev_ctx_t *ctx) {
  while (!(REG32(USBDEV_BASE_ADDR + USBDEV_USBSTAT_REG_OFFSET) &
           (1 << USBDEV_USBSTAT_AV_FULL_BIT))) {
    usbbufid_t buf = usbdev_buf_allocate_byid(ctx);
    if (buf < 0) {
      // no more free buffers, can't fill AV FIFO
      break;
    }
    REG32(USBDEV_BASE_ADDR + USBDEV_AVBUFFER_REG_OFFSET) = buf;
  }
}

void usbdev_sendbuf_byid(usbdev_ctx_t *ctx, usbbufid_t buf, size_t size,
                         int endpoint) {
  uint32_t configin =
      USBDEV_BASE_ADDR + USBDEV_CONFIGIN_0_REG_OFFSET + (4 * endpoint);

  if ((endpoint >= NUM_ENDPOINTS) || (buf >= NUM_BUFS)) {
    return;
  }

  if (size > BUF_LENGTH) {
    size = BUF_LENGTH;
  }

  REG32(configin) = ((buf << USBDEV_CONFIGIN_0_BUFFER_0_OFFSET) |
                     (size << USBDEV_CONFIGIN_0_SIZE_0_OFFSET) |
                     (1 << USBDEV_CONFIGIN_0_RDY_0_BIT));
}

void usbdev_poll(usbdev_ctx_t *ctx) {
  uint32_t istate = REG32(USBDEV_BASE_ADDR + USBDEV_INTR_STATE_REG_OFFSET);

  // Do this first to keep things going
  fill_av_fifo(ctx);

  // Process IN completions first so we get the fact that send completed
  // before processing a response
  if (istate & (1 << USBDEV_INTR_STATE_PKT_SENT_BIT)) {
    uint32_t sentep = REG32(USBDEV_BASE_ADDR + USBDEV_IN_SENT_REG_OFFSET);
    uint32_t configin = USBDEV_BASE_ADDR + USBDEV_CONFIGIN_0_REG_OFFSET;
    TRC_C('a' + sentep);
    for (int ep = 0; ep < NUM_ENDPOINTS; ep++) {
      if (sentep & (1 << ep)) {
        // Free up the buffer and optionally callback
        int32_t cfgin = REG32(configin + (4 * ep));
        usbdev_buf_free_byid(ctx, EXTRACT(cfgin, CONFIGIN_0_BUFFER_0));
        if (ctx->tx_done_callback[ep]) {
          ctx->tx_done_callback[ep](ctx->ep_ctx[ep]);
        }
      }
    }
    // Write one to clear all the ones we handled
    REG32(USBDEV_BASE_ADDR + USBDEV_IN_SENT_REG_OFFSET) = sentep;
    // Clear the interupt
    REG32(USBDEV_BASE_ADDR + USBDEV_INTR_STATE_REG_OFFSET) =
        (1 << USBDEV_INTR_STATE_PKT_SENT_BIT);
  }

  if (istate & (1 << USBDEV_INTR_STATE_PKT_RECEIVED_BIT)) {
    while (!(REG32(USBDEV_BASE_ADDR + USBDEV_USBSTAT_REG_OFFSET) &
             (1 << USBDEV_USBSTAT_RX_EMPTY_BIT))) {
      uint32_t rxinfo = REG32(USBDEV_BASE_ADDR + USBDEV_RXFIFO_REG_OFFSET);
      usbbufid_t buf = EXTRACT(rxinfo, RXFIFO_BUFFER);
      int size = EXTRACT(rxinfo, RXFIFO_SIZE);
      int endpoint = EXTRACT(rxinfo, RXFIFO_EP);
      int setup = (rxinfo >> USBDEV_RXFIFO_SETUP_BIT) & 1;

      if (ctx->rx_callback[endpoint]) {
        ctx->rx_callback[endpoint](ctx->ep_ctx[endpoint], buf, size, setup);
      } else {
        TRC_S("USB: unexpected RX ");
        TRC_I(rxinfo, 24);
      }
      usbdev_buf_free_byid(ctx, buf);
    }
    // Clear the interupt
    REG32(USBDEV_BASE_ADDR + USBDEV_INTR_STATE_REG_OFFSET) =
        (1 << USBDEV_INTR_STATE_PKT_RECEIVED_BIT);
  }
  if (istate & ~((1 << USBDEV_INTR_STATE_PKT_RECEIVED_BIT) |
                 (1 << USBDEV_INTR_STATE_PKT_SENT_BIT))) {
    TRC_C('I');
    TRC_I(istate, 12);
    TRC_C(' ');
    REG32(USBDEV_BASE_ADDR + USBDEV_INTR_STATE_REG_OFFSET) =
        istate & ~((1 << USBDEV_INTR_STATE_PKT_RECEIVED_BIT) |
                   (1 << USBDEV_INTR_STATE_PKT_SENT_BIT));
    if (istate & (1 << USBDEV_INTR_ENABLE_LINK_RESET_BIT)) {
      // Link reset
      for (int ep = 0; ep < NUM_ENDPOINTS; ep++) {
        if (ctx->reset[ep]) {
          ctx->reset[ep](ctx->ep_ctx[ep]);
        }
      }

      // Clear the interupt
      REG32(USBDEV_BASE_ADDR + USBDEV_INTR_STATE_REG_OFFSET) =
          (1 << USBDEV_INTR_ENABLE_LINK_RESET_BIT);
    }
  }
  // TODO - clean this up
  // Frame ticks every 1ms, use to flush data every 16ms
  // (faster in DPI but this seems to work ok)
  // At reset frame count is 0, compare to 1 so no calls before SOF received
  uint32_t usbframe = EXTRACT(
      REG32(USBDEV_BASE_ADDR + USBDEV_USBSTAT_REG_OFFSET), USBSTAT_FRAME);
  if ((usbframe & 0xf) == 1) {
    if (ctx->flushed == 0) {
      for (int i = 0; i < NUM_ENDPOINTS; i++) {
        if (ctx->flush[i]) {
          ctx->flush[i](ctx->ep_ctx[i]);
        }
      }
      ctx->flushed = 1;
    }
  } else {
    ctx->flushed = 0;
  }
  // TODO Errors? What Errors?
}

unsigned int usbdev_get_status(usbdev_ctx_t *ctx) {
  unsigned int status = REG32(USBDEV_BASE_ADDR + USBDEV_USBSTAT_REG_OFFSET);
  return status;
}

unsigned int usbdev_get_link_state(usbdev_ctx_t *ctx) {
  unsigned int link_state = EXTRACT(
      REG32(USBDEV_BASE_ADDR + USBDEV_USBSTAT_REG_OFFSET), USBSTAT_LINK_STATE);
  return link_state;
}

unsigned int usbdev_get_address(usbdev_ctx_t *ctx) {
  unsigned int addr =
      EXTRACT(REG32(USBDEV_BASE_ADDR + USBDEV_USBCTRL_REG_OFFSET),
              USBCTRL_DEVICE_ADDRESS);
  return addr;
}

void usbdev_set_deviceid(usbdev_ctx_t *ctx, int deviceid) {
  REG32(USBDEV_BASE_ADDR + USBDEV_USBCTRL_REG_OFFSET) =
      (1 << USBDEV_USBCTRL_ENABLE_BIT) |
      (deviceid << USBDEV_USBCTRL_DEVICE_ADDRESS_OFFSET);
}

void usbdev_halt(usbdev_ctx_t *ctx, int endpoint, int enable) {
  uint32_t epbit = 1 << endpoint;
  uint32_t stall = REG32(USBDEV_BASE_ADDR + USBDEV_STALL_REG_OFFSET);
  if (enable) {
    stall |= epbit;
  } else {
    stall &= ~epbit;
  }
  REG32(USBDEV_BASE_ADDR + USBDEV_STALL_REG_OFFSET) = stall;
  ctx->halted = stall;
  // TODO future addition would be to callback the endpoint driver
  // for now it just sees its traffic has stopped
}

void usbdev_set_iso(usbdev_ctx_t *ctx, int endpoint, int enable) {
  if (enable) {
    REG32(USBDEV_BASE_ADDR + USBDEV_ISO_REG_OFFSET) =
        SETBIT(REG32(USBDEV_BASE_ADDR + USBDEV_ISO_REG_OFFSET), endpoint);
  } else {
    REG32(USBDEV_BASE_ADDR + USBDEV_ISO_REG_OFFSET) =
        CLRBIT(REG32(USBDEV_BASE_ADDR + USBDEV_ISO_REG_OFFSET), endpoint);
  }
}

void usbdev_clear_data_toggle(usbdev_ctx_t *ctx, int endpoint) {
  REG32(USBDEV_BASE_ADDR + USBDEV_DATA_TOGGLE_CLEAR_REG_OFFSET) =
      (1 << endpoint);
}

void usbdev_set_ep0_stall(usbdev_ctx_t *ctx, int stall) {
  if (stall) {
    REG32(USBDEV_BASE_ADDR + USBDEV_STALL_REG_OFFSET) =
        REG32(USBDEV_BASE_ADDR + USBDEV_STALL_REG_OFFSET) | 1;
  } else {
    REG32(USBDEV_BASE_ADDR + USBDEV_STALL_REG_OFFSET) =
        REG32(USBDEV_BASE_ADDR + USBDEV_STALL_REG_OFFSET) & ~(1);
  }
}

// TODO got hang with this inline
int usbdev_can_rem_wake(usbdev_ctx_t *ctx) { return ctx->can_wake; }

void usbdev_endpoint_setup(usbdev_ctx_t *ctx, int ep, int enableout,
                           void *ep_ctx, void (*tx_done)(void *),
                           void (*rx)(void *, usbbufid_t, int, int),
                           void (*flush)(void *), void (*reset)(void *)) {
  ctx->ep_ctx[ep] = ep_ctx;
  ctx->tx_done_callback[ep] = tx_done;
  ctx->rx_callback[ep] = rx;
  ctx->flush[ep] = flush;
  ctx->reset[ep] = reset;
  if (enableout) {
    uint32_t rxen = REG32(USBDEV_BASE_ADDR + USBDEV_RXENABLE_OUT_REG_OFFSET);
    rxen |= (1 << (ep + USBDEV_RXENABLE_OUT_OUT_0_BIT));
    REG32(USBDEV_BASE_ADDR + USBDEV_RXENABLE_OUT_REG_OFFSET) = rxen;
  }
}

void usbdev_init(usbdev_ctx_t *ctx, bool pinflip, bool diff_rx, bool diff_tx) {
  // setup context
  for (int i = 0; i < NUM_ENDPOINTS; i++) {
    usbdev_endpoint_setup(ctx, i, 0, NULL, NULL, NULL, NULL, NULL);
  }
  ctx->halted = 0;
  ctx->can_wake = 0;
  buf_init(ctx);

  // All about polling...
  REG32(USBDEV_BASE_ADDR + USBDEV_INTR_ENABLE_REG_OFFSET) = 0;

  // Provide buffers for any reception
  fill_av_fifo(ctx);

  REG32(USBDEV_BASE_ADDR + USBDEV_RXENABLE_SETUP_REG_OFFSET) =
      (1 << USBDEV_RXENABLE_SETUP_SETUP_0_BIT);
  REG32(USBDEV_BASE_ADDR + USBDEV_RXENABLE_OUT_REG_OFFSET) =
      (1 << USBDEV_RXENABLE_OUT_OUT_0_BIT);

  uint32_t phy_config =
      (pinflip << USBDEV_PHY_CONFIG_PINFLIP_BIT) |
      (diff_rx << USBDEV_PHY_CONFIG_RX_DIFFERENTIAL_MODE_BIT) |
      (diff_tx << USBDEV_PHY_CONFIG_TX_DIFFERENTIAL_MODE_BIT) |
      (1 << USBDEV_PHY_CONFIG_EOP_SINGLE_BIT_BIT);
  REG32(USBDEV_BASE_ADDR + USBDEV_PHY_CONFIG_REG_OFFSET) = phy_config;

  REG32(USBDEV_BASE_ADDR + USBDEV_USBCTRL_REG_OFFSET) =
      (1 << USBDEV_USBCTRL_ENABLE_BIT);
}
