// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_I3C_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_I3C_TESTUTILS_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_i3c.h"
#include "sw/device/lib/testing/test_framework/check.h"

/** TODO

    Other functionality likely to be required in this layer:
    - address assignment
    - target reset
    - error detection and reporting
    - buffer allocation; or perhaps we specify the data rates of the streams
*/

/**
 * Note that this is _not_ intended to be a complete HCI Driver for I3C.
 * Rather, it strives to exercise functionality without becoming too complex.
 * - It has a model of the DAT in order to support Private Read/Write transfers
 *   and exercise different transfer modes and group addressing.
 * -
 */

enum {
  /**
   * Handle passed to `i3c_testutils_response_collect` that means waiting
   * for immediate response to a command just issued.
   */
  kI3CTestutils_HandleWait = -1,
  /**
   * The maximum number of transfers that may be pending, per context.
   */
  kI3CTestutils_MaxTrans = 16u
};

// Data source
typedef struct i3c_testutils_src {
  /**
   * Buffer for data to be transmitted.
   */
  uint32_t *buf;
  /**
   * Callback function to supply data.
   */
  dif_i3c_tx_cb_t cb_fn;
  /**
   * Handle supplied to callback function.
   */
  void *cb_handle;
} i3c_testutils_src_t;

// Data sink
typedef struct i3c_testutils_sink {
  /**
   * Buffer for received data.
   */
  uint32_t *buf;
  /**
   * Callback function to consume data.
   */
  dif_i3c_rx_cb_t cb_fn;
  /**
   * Handle supplied to callback function.
   */
  void *cb_handle;
} i3c_testutils_sink_t;

// Status of a Transfer response.
typedef enum i3c_testutils_rsp_status {
  kI3CTestUtilsRspStatus_Pending = 1u,   // Transfer is still pending.
  kI3CTestUtilsRspStatus_Collected = 2u  // Owner has collected the response.
} i3c_testutils_rsp_status_t;

// Description of a transfer.
typedef struct i3c_testutils_transfer {
  /**
   * The Command Descriptor for this transfer.
   */
  dif_i3c_cmd_desc_t cmd;
  /**
   * Response status of the transfer; indicates whether a response
   * is available and whether the response has been collected by
   * the owner of the transfer.
   */
  i3c_testutils_rsp_status_t rsp_status;
  /**
   * The Response Descriptor for this transfer.
   */
  dif_i3c_rsp_desc_t rsp;
  /**
   * Source of write data; this may be a buffer or a callback function.
   */
  i3c_testutils_src_t src;
  /**
   * Sink for read data; buffer or callback function.
   */
  i3c_testutils_sink_t sink;
  /**
   * Does this transfer have a read phase?
   */
  bool rd_phase;
  /**
   * Does this transfer have a write phase?
   */
  bool wr_phase;
  /**
   * The number of bytes left to write.
   */
  uint16_t tx_bytes_left;
  /**
   * The number of bytes left to read.
   */
  uint16_t rx_bytes_left;
} i3c_testutils_transfer_t;

// Context for a single I3C IP block instance.
typedef struct i3c_testutils_ctx {
  /**
   * I3C block instance.
   */
  unsigned instance;
  /**
   * Interface to I3C block.
   */
  dif_i3c_t i3c;
  /**
   * Controller configuration.
   */
  dif_i3c_ctrl_config_t ctrl_cfg;
  /**
   * Configuration for each of the Virtual Targets.
   */
  dif_i3c_targ_config_t targ_cfg[I3C_NUM_VIRT_TARGETS];
  /**
   * Employ interrupts rather than polling.
   */
  bool use_interrupts;
  /**
   * Write index within the circular buffer of transfers;
   * this is where the next transfer will be recorded.
   */
  unsigned trans_wr;
  /**
   * Read index within the circular buffer of transfers;
   * this is the oldest transfer in the buffer.
   */
  unsigned trans_rd;
  /**
   * Index within the circular buffer of the current transfer;
   * this is the transfer being actioned by the Controller
   * hardware.
   */
  unsigned trans_curr;
  /**
   * Circular buffer of pending transfers.
   */
  i3c_testutils_transfer_t transfers[kI3CTestutils_MaxTrans];
  /**
   * Local copy of Device Address Table (DAT).
   */
  dif_i3c_dat_entry_t dat[I3C_NUM_DAT_ENTRIES];
  /**
   * Index of first unused DAT entry.
   */
  uint8_t dat_unused;
  /**
   * Last known setting of DCT index.
   */
  uint8_t dct_index;
  /**
   * Next available TID.
   */
  uint8_t tid_next;
  /**
   * Bitmap of currently-used TIDs.
   */
  uint16_t tid_used;

} i3c_testutils_ctx_t;

// Handle for a command that has been queued.
// TODO: Is this really useful behaviour, since commands must all
// complete in order...except for fling-and-forget successful writes.
typedef unsigned i3c_testutils_handle_t;

// Result flags for a Command/Response transfer.
typedef enum i3c_testutils_cmd_flags { Dummy = 1u } i3c_testutils_cmd_flags_t;

// Result flags for a request to collect a Response.
typedef enum i3c_testutils_rsp_flags {
  kI3CTestUtilsRspFlags_Pending = 1u
} i3c_testutils_rsp_flags_t;

// Result flags for collecting a Private Write operation.
typedef enum i3c_testutils_privw_flags {
  kI3CTestUtilsPrivWFlags_Collected = 1u
} i3c_testutils_privw_flags_t;

/**
 * Initialize an I3C IP block instance. Caller shall have set up the
 * configuration - for the Controller and all Virtual Targets - within
 * the context before calling this function.
 *
 * @param ctx Context for this I3C instance.
 * @param instance I3C IP block instance number (0,1..)
 * @param ctrl_mode The initial mode of the Controller
 *                  (Disabled, Active, Standby).
 * @param targ_enables The set of Virtual Targets initially enabled.
 * @param use_intr Use interrupts rather than polling.
 * @return Status code indicating the result of this operation.
 */
OT_WARN_UNUSED_RESULT
status_t i3c_testutils_init(i3c_testutils_ctx_t *ctx, unsigned instance,
                            dif_i3c_ctrl_mode_t ctrl_mode,
                            unsigned targ_enables, bool use_intr);

/**
 * Finalize access to this I3C IP block instance.
 *
 * @param ctx Context for this I3C instance.
 * @return Status code indicating the result of this operation.
 */
OT_WARN_UNUSED_RESULT
status_t i3c_testutils_fin(i3c_testutils_ctx_t *ctx);

/**
 * Add a description of a statically-addressed I3C target into the
 * Device Address Table (DAT) of the Controller.
 *
 * @param ctx Context for this I3C instance.
 * @param static_addr Static address of the Target.
 * @return Status code indicating the result of this operation.
 */
OT_WARN_UNUSED_RESULT
status_t i3c_testutils_target_add(i3c_testutils_ctx_t *ctx,
                                  uint8_t static_addr);

/**
 * Queue a command for execution by the Controller.
 *
 * @param ctx Context for this I3C instance.
 * @param cmd Command descriptor.
 * @param src Description of the source of write data.
 * @param sink Description of the sink for read data.
 * @param rsp Receives the response descriptor iff `wait` is true.
 * @param phandle Receives the transfer handle iff `wait` is false.
 * @param wait Indicates whether to await completion before returning.
 * @return Status code indicating the result of this operation.
 */
OT_WARN_UNUSED_RESULT
status_t i3c_testutils_command_queue(
    i3c_testutils_ctx_t *ctx, const dif_i3c_cmd_desc_t *cmd,
    const i3c_testutils_src_t *src, const i3c_testutils_sink_t *sink,
    dif_i3c_rsp_desc_t *rsp, i3c_testutils_handle_t *phandle, bool wait);

/**
 * Check for the availability of a transfer response, and optionally return the
 * responses if available.
 *
 * @param ctx Context for this I3C instance.
 * @param handle The transfer... TODO:
 * @param rsp Receives the command response (NULL == check availability only).
 * @param flags Receives flags indicating whether the response is available.
 * @return Status code indicating the result of this operation.
 */
OT_WARN_UNUSED_RESULT
status_t i3c_testutils_response_collect(i3c_testutils_ctx_t *ctx,
                                        i3c_testutils_handle_t handle,
                                        dif_i3c_rsp_desc_t *rsp,
                                        i3c_testutils_rsp_flags_t *flags);

/**
 * Interrupt Service Routine for the I3C IP block.
 *
 * @param ctx Context for this I3C instance.
 */
void i3c_testutils_isr(i3c_testutils_ctx_t *ctx);

/**
 * Service the Controller and all Virtual Targets, keeping data streaming.
 *
 * @param ctx Context for this I3C instance.
 */
void i3c_testutils_service(i3c_testutils_ctx_t *ctx);

/**
 * Perform a Private Read transfer from a Target.
 *
 * @param ctx Context for this I3C instance.
 * @param addr Target address.
 * @param sink Sink (buffer or callback function) for received data.
 * @param nbytes The number of bytes to be read.
 * @param mode The transfer mode to be used.
 * @param rxlen Receives the number of bytes read.
 * @return Status code indicating the result of this operation.
 */
OT_WARN_UNUSED_RESULT
status_t i3c_testutils_read(i3c_testutils_ctx_t *ctx, uint8_t addr,
                            const i3c_testutils_sink_t *sink, uint16_t nbytes,
                            dif_i3c_cmd_mode_t mode, uint16_t *rxlen);

/**
 * Perform a Private Write transfer to one or more Targets.
 *
 * @param ctx Context for this I3C instance.
 * @param addr Target/Group address.
 * @param src Source (buffer or callback function) of write data.
 * @param data The data to be written.
 * @param nbytes The number of bytes of data to be written.
 * @param mode The transfer mode to be used.
 * @return Status code indicating the result of this operation.
 */
OT_WARN_UNUSED_RESULT
status_t i3c_testutils_write(i3c_testutils_ctx_t *ctx, uint8_t addr,
                             const i3c_testutils_src_t *src, uint16_t nbytes,
                             dif_i3c_cmd_mode_t mode);

/**
 * Prepare a Virtual Target for a Private Read operation.
 *
 * @param ctx Context for this I3C instance.
 * @param idx The index number of the Virtual Target.
 * @param tx TTI transmission descriptor describing the transfer.
 * @param data The data to be transmitted (= read by the Controller).
 * @return Status code indicating the result of this operation.
 */
OT_WARN_UNUSED_RESULT
status_t i3c_testutils_private_read_setup(i3c_testutils_ctx_t *ctx, uint8_t idx,
                                          const dif_i3c_tti_tx_desc_t *tx,
                                          const uint32_t *data);

/**
 * Attempt to collect a Private Write transfer from the Active Controller.
 *
 * @param ctx Context for this I3C instance.
 * @param rx_desc Receives the TTI reception descriptor.
 * @param buf Receives the write data from the Controller.
 * @param flags Flags describing the availability and current state of the
 *              Private Write transfer.
 * @return Status code indicating the result of this operation.
 */
OT_WARN_UNUSED_RESULT
status_t i3c_testutils_private_write_collect(
    i3c_testutils_ctx_t *ctx, dif_i3c_tti_rx_desc_t *rx_desc, uint32_t *buf,
    i3c_testutils_privw_flags_t *flags);

// TODO: Make `unsigned id` and `uint8_t idx` consistent!

#endif
