// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/i3c_testutils.h"

#include "sw/device/lib/dif/dif_i3c.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "sw/device/lib/dif/autogen/dif_i3c_autogen.h"

#define MODULE_ID MAKE_MODULE_ID('i', '3', 't')

#define I3C0_BASE_ADDR TOP_EARLGREY_I3C0_BASE_ADDR
#define I3C1_BASE_ADDR TOP_EARLGREY_I3C1_BASE_ADDR

// Diagnostic/debugging logging of transfers?
static const bool logging = true;

// Keep the data moving for a Read/Write transfer on the Controller side.
static void ctrl_data_move(i3c_testutils_ctx_t *ctx);
// Retrieve a resposne from the HCI Response Queue if available.
static void ctrl_response_get(i3c_testutils_ctx_t *ctx,
                              i3c_testutils_transfer_t *trans);
// Service any Controller-side activity.
static void ctrl_service(i3c_testutils_ctx_t *ctx);
// Look up an address within the Device Address Table and return its index.
static status_t dat_addr_lookup(i3c_testutils_ctx_t *ctx, uint8_t addr,
                                uint8_t *pidx);
// Utility function that indicates whether a transfer handle is valid.
static bool handle_valid(i3c_testutils_ctx_t *ctx,
                         i3c_testutils_handle_t handle);
// Utility function that calculates the next index within the circular buffer
// of transfers.
static inline unsigned index_inc(unsigned idx) {
  return (++idx >= kI3CTestutils_MaxTrans) ? 0u : idx;
}
// Utility function to map an I3C Response Descriptor to a `status_t` code.
static status_t status_from_rsp(status_t status, const dif_i3c_rsp_desc_t *rsp);
// Service any Target-side activity.
static void targ_service(i3c_testutils_ctx_t *ctx);
// Allocate a new TID that does not collide with those in use.
static status_t tid_allocate(i3c_testutils_ctx_t *ctx, uint8_t *ptid);
// Release a TID when a transfer has completed.
static inline void tid_release(i3c_testutils_ctx_t *ctx, uint8_t pid) {
  ctx->tid_used &= (uint16_t)~(1u << pid);
}

static status_t allocate_ranges(i3c_testutils_ctx_t *ctx,
                                dif_i3c_phys_queue_t id, unsigned n,
                                unsigned en) {
  // Read the current range allocated to the Virtual Targets.
  unsigned range_min = 0u;
  unsigned range_max = 0u;
  TRY(dif_i3c_config_queue_get(&ctx->i3c, id, &range_min, NULL, NULL));
  TRY(dif_i3c_config_queue_get(&ctx->i3c, id + I3C_MAX_VIRT_TARGETS - 1u, NULL,
                               &range_max, NULL));

  LOG_INFO("ID %x range %x %x", id, range_min, range_max);

  unsigned range_each;
  if (!n) {
    // Just pretend that they're all enabled, and share it equally.
    en = (1u << I3C_MAX_VIRT_TARGETS) - 1u;
    n = I3C_MAX_VIRT_TARGETS;
  }
  range_each = (range_max + 1u - range_min) / n;

  unsigned max_addr =
      range_min + range_each - 1u;  // Inclusive maximum address.
  unsigned min_addr = range_min;
  for (unsigned t = 0u; t < I3C_MAX_VIRT_TARGETS; ++t, ++id) {
    // The configuration shall be unused for a Virtual Target that is not
    // enabled, but we reuse the minimum address as the maximum to play a little
    // safer. Use 'range_max' for the last enabled VT to ensure that we don't
    // lose space over time.
    unsigned last_addr =
        (en & 1u) ? ((en == 1u) ? range_max : max_addr) : min_addr;
    LOG_INFO("t %x ID %x range %x %x", id, min_addr, last_addr);
    TRY(dif_i3c_config_queue_set(&ctx->i3c, id, min_addr, last_addr, 0u));
    if (en & 1u) {
      min_addr += range_each;
      max_addr += range_each;
    }
    en >>= 1;
  }

  return OK_STATUS();
}

// Initialize an I3C instance, using the configuration already supplied
// within the context structure:
// - i3c
// - ctrl_cfg
// - targ_cfg
status_t i3c_testutils_init(i3c_testutils_ctx_t *ctx, unsigned instance,
                            dif_i3c_ctrl_mode_t ctrl_mode,
                            unsigned target_enables, bool use_intr) {
  uint32_t base_addr = instance ? I3C1_BASE_ADDR : I3C0_BASE_ADDR;
  TRY(dif_i3c_init(mmio_region_from_addr(base_addr), &ctx->i3c));

  // Multiple contexts may be used simultaneously.
  ctx->instance = instance;

  // Mode of operation; interrupt-driven or polling.
  ctx->use_interrupts = use_intr;

  // Initialise the transfer state.
  ctx->trans_rd = 0u;
  ctx->trans_wr = 0u;
  ctx->trans_curr = 0u;
  ctx->tid_used = 0u;
  ctx->tid_next = 1u;

  // Initialize the state of the tables.
  ctx->dat_unused = 0u;
  ctx->dct_index = 0u;

  // Leaving most of the message buffer configuration intact, we size the
  // Target-side Tx Descriptor Queues and Tx Data Buffers according to the
  // the number of Virtual Target about to be configured.
  if (target_enables) {
    // Count the number of set bits, i.e., enabled Virtual Targets.
    unsigned en = target_enables;
    unsigned n = 0u;
    while (en) {
      en &= ~(en & ~(en - 1));  // Clear a single bit.
      ++n;
    }
    TRY(allocate_ranges(ctx, kDifI3CPhysQTxData0, n, target_enables));
    TRY(allocate_ranges(ctx, kDifI3CPhysQTxDesc0, n, target_enables));
  }

  // Configure the Controller-side logic.
  TRY(dif_i3c_ctrl_configure(&ctx->i3c, &ctx->ctrl_cfg));
  TRY(dif_i3c_ctrl_mode_set(&ctx->i3c, ctrl_mode));

  // Configure the Virtual Targets.
  for (uint8_t idx = 0u; idx < (uint8_t)I3C_NUM_VIRT_TARGETS; ++idx) {
    TRY(dif_i3c_targ_configure(&ctx->i3c, idx, &ctx->targ_cfg[idx]));
  }

  // Enable the Virtual Targets.
  TRY(dif_i3c_targ_enables_set(&ctx->i3c, target_enables));

  // TODO: Presently, when the Target peripheral is enabled there is a 5us
  // delay as it comes out of reset.
  busy_spin_micros(6);

  // Enable Status and Signals.
  // TODO: On the Controller side only for now; see `_isr` function which
  // handles only PIO-related interrupts.
  if (use_intr) {
    dif_i3c_interrupts_t interrupts;
    memset(&interrupts, 0, sizeof(interrupts));
    interrupts.group = kDifI3CIntrGroup_PIO;
    interrupts.pio.tx_thld = 1u;
    interrupts.pio.rx_thld = 1u;
    interrupts.pio.resp_ready = 1u;
    TRY(dif_i3c_intr_status_enable_set(&ctx->i3c, &interrupts));
    TRY(dif_i3c_intr_signal_enable_set(&ctx->i3c, &interrupts));

    if (target_enables & ((1u << I3C_NUM_VIRT_TARGETS) - 1u)) {
      // Enable reception within the Target-side logic if at least one
      // Virtual Target is enabled.
      memset(&interrupts, 0, sizeof(interrupts));
      interrupts.group = kDifI3CIntrGroup_Targ;
      interrupts.targ.rx_desc_ready = 1u;

      // Enable transmission for each enabled Virtual Target.
      uint8_t tx_mask =
          (uint8_t)(target_enables & ((1u << I3C_NUM_VIRT_TARGETS) - 1u));
      interrupts.targ.tx_thld = tx_mask;
      interrupts.targ.tx_desc_ready = tx_mask;
      TRY(dif_i3c_intr_status_enable_set(&ctx->i3c, &interrupts));
      TRY(dif_i3c_intr_signal_enable_set(&ctx->i3c, &interrupts));

      // At this point we can enable interrupts at the top level of the IP
      // block.
      TRY(dif_i3c_irq_set_enabled(&ctx->i3c, kDifI3cIrqTarg,
                                  kDifToggleEnabled));
    }
    // Enable Controller-side interrupts.
    TRY(dif_i3c_irq_set_enabled(&ctx->i3c, kDifI3cIrqHci, kDifToggleEnabled));
  }

  return OK_STATUS();
}

// Finalize this I3C instance and release all resources.
status_t i3c_testutils_fin(i3c_testutils_ctx_t *ctx) {
  if (ctx->use_interrupts) {
    // Disable interrupts at the top level of the IP block.
    TRY(dif_i3c_irq_set_enabled(&ctx->i3c, kDifI3cIrqHci, kDifToggleDisabled));
    TRY(dif_i3c_irq_set_enabled(&ctx->i3c, kDifI3cIrqTarg, kDifToggleDisabled));
    // Clear the status and signal enables within the IP block.
    dif_i3c_interrupts_t interrupts;
    memset(&interrupts, 0, sizeof(interrupts));
    interrupts.group = kDifI3CIntrGroup_PIO;
    TRY(dif_i3c_intr_status_enable_set(&ctx->i3c, &interrupts));
    TRY(dif_i3c_intr_signal_enable_set(&ctx->i3c, &interrupts));
    interrupts.group = kDifI3CIntrGroup_Targ;
    TRY(dif_i3c_intr_status_enable_set(&ctx->i3c, &interrupts));
    TRY(dif_i3c_intr_signal_enable_set(&ctx->i3c, &interrupts));
  }

  TRY(dif_i3c_ctrl_mode_set(&ctx->i3c, kI3CCtrlMode_Disabled));
  TRY(dif_i3c_targ_enables_set(&ctx->i3c, 0u));
  return OK_STATUS();
}

// Add a target to the Controller's Device Address Table.
status_t i3c_testutils_target_add(i3c_testutils_ctx_t *ctx,
                                  uint8_t static_addr) {
  // Determine the DAT entry to be used.
  uint8_t idx = ctx->dat_unused;
  if (idx >= I3C_NUM_DAT_ENTRIES)
    return UNAVAILABLE();
  ctx->dat_unused++;

  dif_i3c_dat_entry_t entry;
  memset(&entry, 0, sizeof(entry));

  entry.static_address = static_addr;
  entry.dynamic_address = static_addr;  // TODO: Temporary, for bring up.

  // Set the DAT entry in the Controller hardware.
  TRY(dif_i3c_dat_entry_set(&ctx->i3c, idx, &entry));
  // Update our local copy.
  ctx->dat[idx] = entry;
  return OK_STATUS();
}

// Queue a command within the Controller, and optionally await the response.
// Multiple commands may be queued but since they must complete in order
// within this single thread, waiting is permissible only if the queue is
// empty.
status_t i3c_testutils_command_queue(
    i3c_testutils_ctx_t *ctx, const dif_i3c_cmd_desc_t *cmd,
    const i3c_testutils_src_t *src, const i3c_testutils_sink_t *sink,
    dif_i3c_rsp_desc_t *rsp, i3c_testutils_handle_t *phandle, bool wait) {
  TRY_CHECK(ctx != NULL && cmd != NULL && rsp != NULL);
  // We must be able to return a handle if not waiting for completion.
  TRY_CHECK(wait || phandle != NULL);
  // Check the size of the initial chunk.
  uint16_t len;
  TRY(dif_i3c_cmd_data_length(cmd, &len));

  LOG_INFO("Command_queue request dev %d rnw %d len %d", cmd->reg.dev_index,
           cmd->reg.rnw, len);

  // Remember the transfer and return a handle identifying the transfer.
  i3c_testutils_transfer_t *trans = &ctx->transfers[ctx->trans_wr];
  trans->cmd = *cmd;

  // TODO: We do not support Combo transfers presently, so this code
  // may seem a bit strange, although not all commands have a data phase.
  trans->rd_phase = false;
  trans->wr_phase = false;
  switch (cmd->reg.cmd_attr) {
    case kDifI3CCmdAttr_Regular:
      trans->rd_phase = cmd->reg.rnw;
      trans->wr_phase = !cmd->reg.rnw;
      break;
    case kDifI3CCmdAttr_Immediate:
      trans->rd_phase = cmd->imm.rnw;
      trans->wr_phase = !cmd->imm.rnw;
      break;
    default:
      /* Do nothing */
      break;
  }

  // Read/write data may involve either a memory or a callback function.
  if (trans->rd_phase) {
    trans->rx_bytes_left = len;
    trans->sink = *sink;
  }
  if (trans->wr_phase) {
    trans->tx_bytes_left = len;
    trans->src = *src;
  }

  // Response status is initially 'transfer pending'; this flag will be
  // cleared when we have a transfer response from the Controller.
  trans->rsp_status = kI3CTestUtilsRspStatus_Pending;

  // Capture the handle, ready for calls to `i3c_testutils_response_collect`.
  i3c_testutils_handle_t handle = ctx->trans_wr;
  ctx->trans_wr = index_inc(ctx->trans_wr);

  // Attempt to supply some initial write data to expedite dispatch.
  if (trans->wr_phase) {
    ctrl_data_move(ctx);
  }

  // Queue/initiate command; all required state must have been set up above,
  // particularly for interrupt-driven operation.
  TRY(dif_i3c_command_write(&ctx->i3c, cmd, 1u));

  status_t status = OK_STATUS();
  if (wait) {
    i3c_testutils_rsp_flags_t flags;
    do {
      i3c_testutils_service(ctx);
      status = i3c_testutils_response_collect(ctx, handle, rsp, &flags);
    } while (status_ok(status) && (flags & kI3CTestUtilsRspFlags_Pending));
  } else {
    // Just return a handle and trust the caller to invoke either '_service()'
    // or '_isr()' to keep the transfer(s) alive, and '_response_collect()'
    // to check on completion status.
    *phandle = handle;
  }

  return status;
}

// Attempt to collect the response to a queued command, returning either
// the result or an indication that the command is stilll pending.
status_t i3c_testutils_response_collect(i3c_testutils_ctx_t *ctx,
                                        i3c_testutils_handle_t handle,
                                        dif_i3c_rsp_desc_t *rsp,
                                        i3c_testutils_rsp_flags_t *flags) {
  // Is the handle valid?
  // Note that a handle becomes invalid once the response is collected.
  if (ctx == NULL || rsp == NULL || !handle_valid(ctx, handle)) {
    return INVALID_ARGUMENT();
  }

  // Is the response available yet?
  i3c_testutils_transfer_t *trans = &ctx->transfers[handle];
  if (trans->rsp_status & kI3CTestUtilsRspStatus_Pending) {
    // This command is still pending; there should be no need to introduce a
    // timeout, since the Controller is required to do that.
    *flags = kI3CTestUtilsRspFlags_Pending;
  } else {
    // The response is available; mark it as collected; the handle is invalid
    // after this point.
    trans->rsp_status |= kI3CTestUtilsRspStatus_Collected;
    *rsp = trans->rsp;
    *flags = 0u;

    // Consume all collected responses, freeing space in the circular buffer.
    while (ctx->trans_rd != ctx->trans_wr &&
           ctx->transfers[ctx->trans_rd].rsp_status &
               kI3CTestUtilsRspStatus_Collected) {
      ctx->trans_rd = index_inc(ctx->trans_rd);
    }
  }

  return OK_STATUS();
}

// Keep the data moving for a Read/Write transfer on the Controller side.
// - invoke from the foreground for polling-driven operation and from the
//   ISR in interrupt-driven mode.
void ctrl_data_move(i3c_testutils_ctx_t *ctx) {
  i3c_testutils_transfer_t *trans = &ctx->transfers[ctx->trans_curr];
  dif_i3c_hci_buffer_levels_t levels;

  // Read the Rx and Tx Buffer state.
  CHECK_DIF_OK(dif_i3c_buffer_levels_read(&ctx->i3c, &levels));

  if (trans->rd_phase) {
    // Determine the amount of data available in the Rx Buffer.
    //
    // Note that there could be Rx data for another transfer already, so
    // limit the transfer length.
    uint8_t rx_dwords = levels.rx_buffer_level;
    uint16_t rx_bytes = trans->rx_bytes_left;
    if (rx_bytes < (rx_dwords << 2)) {
      rx_dwords = (uint8_t)((rx_bytes + 3u) >> 2);
    } else {
      rx_bytes = (uint16_t)(rx_dwords << 2);
    }
    if (logging) {
      LOG_INFO("rx %d byte(s)", rx_bytes);
    }

    if (trans->sink.buf) {
      CHECK_DIF_OK(dif_i3c_xfer_read(&ctx->i3c, trans->sink.buf, rx_bytes));
    } else {
      CHECK_DIF_OK(dif_i3c_queue_pop_cb(&ctx->i3c, kDifI3CQueueXfer,
                                        trans->sink.cb_fn,
                                        trans->sink.cb_handle, rx_dwords));
    }
    trans->rx_bytes_left -= rx_bytes;
  }
  if (trans->wr_phase) {
    // Determine the amount of space available in the Tx Buffer.
    uint8_t tx_dwords = levels.tx_buffer_free;
    uint16_t tx_bytes = trans->tx_bytes_left;
    if (tx_bytes < (tx_dwords << 2)) {
      tx_dwords = (uint8_t)((tx_bytes + 3u) >> 2);
    } else {
      tx_bytes = (uint16_t)(tx_dwords << 2);
    }
    if (logging) {
      LOG_INFO("tx %d byte(s)", tx_bytes);
    }

    if (trans->src.buf) {
      CHECK_DIF_OK(dif_i3c_xfer_write(&ctx->i3c, trans->src.buf, tx_bytes));
    } else {
      CHECK_DIF_OK(dif_i3c_queue_push_cb(&ctx->i3c, kDifI3CQueueXfer,
                                         trans->src.cb_fn, trans->src.cb_handle,
                                         tx_dwords));
    }
    trans->tx_bytes_left -= tx_bytes;
  }
}

// Retrieve a response from the HCI Response Queue if available,
// and update our record of the transfer status.
void ctrl_response_get(i3c_testutils_ctx_t *ctx,
                       i3c_testutils_transfer_t *trans) {
  dif_i3c_hci_queue_levels_t levels;
  CHECK_DIF_OK(dif_i3c_queue_levels_read(&ctx->i3c, &levels));

  // Is there a response available yet?
  if (levels.rsp_buffer_level > 0u) {
    trans->rsp_status =
        trans->rsp_status &
        (i3c_testutils_rsp_status_t)~kI3CTestUtilsRspStatus_Pending;

    // Store the Response Descriptor.
    CHECK_DIF_OK(dif_i3c_response_read(&ctx->i3c, &trans->rsp, 1u));
    tid_release(ctx, trans->rsp.tid);

    // Advance to the next transfer, if any. This has already been pushed
    // into the HCI Command Queue and the Controller hardware will proceed
    // automatically.
    ctx->trans_curr = index_inc(ctx->trans_curr);
  } else {
    // This command is still pending; there should be no need to introduce a
    // timeout, since the Controller is required to do that.
  }
}

// Service any Controller-side activity.
void ctrl_service(i3c_testutils_ctx_t *ctx) {
  // Is the Controller performing a transfer?
  if (ctx->trans_curr != ctx->trans_wr) {
    ctrl_data_move(ctx);

    // Has all of the data for this transfer been moved?
    i3c_testutils_transfer_t *trans = &ctx->transfers[ctx->trans_curr];
    const dif_i3c_cmd_desc_t *cmd = &trans->cmd;
    bool complete = false;

    // TODO: Support the other more obscure command types.
    if (cmd->reg.rnw) {
      complete = !trans->rx_bytes_left;
    } else {
      complete = !trans->tx_bytes_left;
    }
    if (complete) {
      ctrl_response_get(ctx, trans);
    }
  }

  if (false) {
    if (false) {
      // Shuffle IBI data.
    } else {
      // Signal IBI completion.
    }
  }
}

// Service any Target-side activity.
void targ_service(i3c_testutils_ctx_t *ctx) {
  // Service each of the Virtual Targets.
  for (unsigned t = 0u; t < I3C_NUM_VIRT_TARGETS; t++) {
    if (false) {
    }
  }
  if (false) {
    // Collect more write data from the Active Controller if possible.
  }
  // Service transmission of IBIs from Virtual Targets.
  if (false) {
  }

  // Collect and dispatch any Asynchronous Events.
  // - we collect and dispatch all available events as soon as possible.
  while (false) {
  }
}

// Interrupt Service Routine for the I3C IP block.
void i3c_testutils_isr(i3c_testutils_ctx_t *ctx) {
  // Process interrupts relating to the PIO queues.
  dif_i3c_interrupts_t interrupts;
  interrupts.group = kDifI3CIntrGroup_PIO;
  CHECK_DIF_OK(dif_i3c_intr_status_get(&ctx->i3c, &interrupts));

  // Shuffle Controller-side data; note that the TX_THLD and RX_THLD interrupts
  // may not be enough to complete the transfer, so we also respond on the
  // RESP_READY interrupt here.
  if (interrupts.pio.resp_ready | interrupts.pio.rx_thld |
      interrupts.pio.tx_thld) {
    ctrl_data_move(ctx);
  }
  if (interrupts.pio.resp_ready) {
    // Collect the response and signal to the foreground code.
    ctrl_response_get(ctx, &ctx->transfers[ctx->trans_curr]);
  }

  // Clear the processed PIO interrupts.
  CHECK_DIF_OK(dif_i3c_intr_status_clear(&ctx->i3c, &interrupts));

  // TODO: Handle the other interrupts too.
}

// Foreground service routine, primarily for polling-driven operation.
// - service any transfers being performed by the Controller and Virtual
// Targets.
// - for interrupt-driven operation the foreground code is largely idle and this
//   code need not be invoked.
void i3c_testutils_service(i3c_testutils_ctx_t *ctx) {
  if (ctx->use_interrupts) {
    // Interrupts keep the transfers going.
    wait_for_interrupt();
  } else {
    ctrl_service(ctx);
    targ_service(ctx);
  }
}

// Simple, blocking transfer performed by the Controller.
static status_t ctrl_transfer(i3c_testutils_ctx_t *ctx, uint8_t addr,
                              const i3c_testutils_src_t *src,
                              const i3c_testutils_sink_t *sink, uint16_t nbytes,
                              dif_i3c_cmd_mode_t mode, dif_i3c_rsp_desc_t *rsp,
                              bool read) {
  // Is there space for another transfer?
  // Leave a single slot unused to differentiate full from empty.
  if (index_inc(ctx->trans_wr) == ctx->trans_rd) {
    return UNAVAILABLE();
  }

  uint8_t dev_index;
  uint8_t tid;
  status_t res = tid_allocate(ctx, &tid);
  if (status_ok(res)) {
    res = dat_addr_lookup(ctx, addr, &dev_index);
  }
  if (!status_ok(res)) {
    return res;
  }

  dif_i3c_cmd_desc_t cmd;
  memset(&cmd, 0, sizeof(cmd));
  cmd.reg.cmd_attr = kDifI3CCmdAttr_Regular;
  cmd.reg.tid = tid;
  cmd.reg.dev_index = dev_index;
  cmd.reg.mode = mode;
  cmd.reg.rnw = read ? 1u : 0u;
  cmd.reg.wroc = 1u;
  cmd.reg.toc = 1u;
  cmd.reg.data_length = nbytes;

  // Queue the command for processing, await completion and return the
  // response.
  return i3c_testutils_command_queue(ctx, &cmd, src, sink, rsp, NULL, true);
}

// Utility function to map an I3C Response Descriptor to a `status_t` code.
status_t status_from_rsp(status_t status, const dif_i3c_rsp_desc_t *rsp) {
  if (status_ok(status)) {
    switch (rsp->err_status) {
      case kDifI3CErrStatus_OK:
        return OK_STATUS();

      case kDifI3CErrStatus_I3CShortReadErr:
        OT_FALLTHROUGH_INTENDED;
      case kDifI3CErrStatus_HCAborted:
        OT_FALLTHROUGH_INTENDED;
      case kDifI3CErrStatus_AbortedWithCRC:
        OT_FALLTHROUGH_INTENDED;
      case kDifI3CErrStatus_BusAborted:
        return ABORTED();

      case kDifI3CErrStatus_CRC:
        OT_FALLTHROUGH_INTENDED;
      case kDifI3CErrStatus_Parity:
        OT_FALLTHROUGH_INTENDED;
      case kDifI3CErrStatus_Frame:
        return DATA_LOSS();

      case kDifI3CErrStatus_NACK:
        return NOT_FOUND();

      default:
        return UNKNOWN();
    }
  }
  return status;
}

// Perform a Private Read transfer from a Target.
status_t i3c_testutils_read(i3c_testutils_ctx_t *ctx, uint8_t addr,
                            const i3c_testutils_sink_t *sink, uint16_t nbytes,
                            dif_i3c_cmd_mode_t mode, uint16_t *rxlen) {
  i3c_testutils_src_t src;
  memset(&src, 0, sizeof(src));

  dif_i3c_rsp_desc_t rsp;
  status_t status =
      ctrl_transfer(ctx, addr, &src, sink, nbytes, mode, &rsp, true);
  if (rxlen != NULL) {
    *rxlen = rsp.data_length;
  }
  return status_from_rsp(status, &rsp);
}

// Perform a Private Write transfer to one or more Targets.
status_t i3c_testutils_write(i3c_testutils_ctx_t *ctx, uint8_t addr,
                             const i3c_testutils_src_t *src, uint16_t nbytes,
                             dif_i3c_cmd_mode_t mode) {
  i3c_testutils_sink_t sink;
  memset(&sink, 0, sizeof(sink));

  dif_i3c_rsp_desc_t rsp;
  status_t status =
      ctrl_transfer(ctx, addr, src, &sink, nbytes, mode, &rsp, false);
  return status_from_rsp(status, &rsp);
}

// Prepare a Virtual Target for a Private Read operation.
status_t i3c_testutils_private_read_setup(i3c_testutils_ctx_t *ctx, uint8_t idx,
                                          const dif_i3c_tti_tx_desc_t *tx_desc,
                                          const uint32_t *data) {
  // TODO: Need to check the available space.
  TRY(dif_i3c_targ_send(&ctx->i3c, idx, tx_desc, data,
                        tx_desc->tx.data_length));
  return OK_STATUS();
}

// Attempt to collect a Private Write transfer from the Active Controller.
status_t i3c_testutils_private_write_collect(
    i3c_testutils_ctx_t *ctx, dif_i3c_tti_rx_desc_t *rx_desc, uint32_t *buf,
    i3c_testutils_privw_flags_t *flags) {
  dif_i3c_tti_queue_levels_t levels;
  TRY(dif_i3c_targ_queue_levels_read(&ctx->i3c, &levels));

  if (levels.rx_desc_level) {
    // Attempt to collect the Rx Descriptor.
    TRY(dif_i3c_targ_recv(&ctx->i3c, rx_desc, 1u));
    // TODO: Need to check the amount of available data.
    TRY(dif_i3c_targ_data_recv(&ctx->i3c, buf, rx_desc->data_length));
    *flags = kI3CTestUtilsPrivWFlags_Collected;
  } else {
    *flags = 0;
  }
  return OK_STATUS();
}

// Allocate a new TID that does not collide with those in use.
status_t tid_allocate(i3c_testutils_ctx_t *ctx, uint8_t *ptid) {
  uint8_t tid = ctx->tid_next;
  if ((ctx->tid_used >> tid) & 1u) {
    uint16_t used = ctx->tid_used;
    if (used == 0xffffu)
      return UNAVAILABLE();
    tid = 0u;
    while (used & 1u) {
      used >>= 1;
      tid++;
    }
    ctx->tid_next = tid + 1;
  } else {
    // TIDs are normally allocated round-robin.
    ctx->tid_next = (ctx->tid_next + 1) & 0xfu;
  }
  // Record the allocation.
  ctx->tid_used |= (1u << tid);
  *ptid = tid;
  return OK_STATUS();
}

static inline uint8_t dat_entry_addr(i3c_testutils_ctx_t *ctx, uint8_t idx) {
  return ctx->dat[idx].dynamic_address
             ? ctx->dat[idx].dynamic_address
             : 0xffu;  // DAT entry disabled, cannot match.
}

// Look up an address within the Device Address Table and return its index.
status_t dat_addr_lookup(i3c_testutils_ctx_t *ctx, uint8_t addr,
                         uint8_t *pidx) {
  for (uint8_t idx = 0u; idx < I3C_NUM_DAT_ENTRIES; ++idx) {
    if (addr == dat_entry_addr(ctx, idx)) {
      *pidx = idx;
      return OK_STATUS();
    }
  }
  return NOT_FOUND();
}

// Utility function that indicates whether a transfer handle is valid.
bool handle_valid(i3c_testutils_ctx_t *ctx, i3c_testutils_handle_t handle) {
  if (ctx->trans_wr >= ctx->trans_rd) {
    if (handle >= ctx->trans_rd && handle < ctx->trans_wr &&
        !(ctx->transfers[handle].rsp_status &
          kI3CTestUtilsRspStatus_Collected)) {
      return true;
    }
  } else if (((handle >= ctx->trans_rd && handle < kI3CTestutils_MaxTrans) ||
              handle < ctx->trans_wr) &&
             !(ctx->transfers[handle].rsp_status &
               kI3CTestUtilsRspStatus_Collected)) {
    return true;
  }
  return false;
}
