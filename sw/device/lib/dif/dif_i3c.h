// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I3C_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I3C_H_

/**
 * @file
 * @brief <a href="/book/hw/ip/i3c/">I3C</a> Device Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "hw/top/i3c_regs.h"  // Generated.
#include "sw/device/lib/dif/autogen/dif_i3c_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/* TODO: Others:
   - apportion message buffer
   - set queue thresholds
   - error information
   - target reset generation and detection
   -
  Maybe we want buffer_write and buffer_read in addition to queue_pop/push
  in order to transfer byte-aligned quantities (system RAM-side) and then we
  can drop a number of queue/buffer-specific functions?
 */

/**
 * Hardware constants.
 */
#define I3C_NUM_DAT_ENTRIES 32u
#define I3C_NUM_DCT_ENTRIES 32u
#define I3C_NUM_VIRT_TARGETS 2u
#define I3C_MAX_VIRT_TARGETS 4u
#define I3C_BUFFER_BYTES 0x1000u

/**
 * Command Attribute values (TCRI 7.1.2).
 */
typedef enum dif_i3c_cmd_attr {
  kDifI3CCmdAttr_Regular,
  kDifI3CCmdAttr_Immediate,
  kDifI3CCmdAttr_AddrAssgn,
  kDifI3CCmdAttr_Combo,
  kDifI3CCmdAttr_IntControl = 7
} dif_i3c_cmd_attr_t;

/**
 * Transfer Mode values (TCRI 7.1.2.1).
 */
typedef enum dif_i3c_cmd_mode {
  kDifI3CCmdMode_SDR0,
  kDifI3CCmdMode_SDR1,
  kDifI3CCmdMode_SDR2,
  kDifI3CCmdMode_SDR3,
  kDifI3CCmdMode_SDR4,
  kDifI3CCmdMode_HDRTSx,
  kDifI3CCmdMode_HDRDDR
} dif_i3c_cmd_mode_t;

/**
 * Error Status Codes (TCRI 6.4.1).
 */
typedef enum dif_i3c_err_status {
  kDifI3CErrStatus_OK = 0,
  kDifI3CErrStatus_CRC,
  kDifI3CErrStatus_Parity,
  kDifI3CErrStatus_Frame,
  kDifI3CErrStatus_AddrHeader,
  kDifI3CErrStatus_NACK,
  kDifI3CErrStatus_OVL,
  kDifI3CErrStatus_I3CShortReadErr,
  kDifI3CErrStatus_HCAborted,
  kDifI3CErrStatus_BusAborted = 9,
  kDifI3CErrStatus_NotSupported,
  kDifI3CErrStatus_AbortedWithCRC,

  // The following are Transfer Type Specific (Combo Transfers).
  kDifI3CErrStatus_ComboNACK2nd = 0xC,
  kDifI3CErrStatus_ComboBusAborted2nd
} dif_i3c_err_status_t;

/**
 * Logical queues implemented within the message buffer of the I3C IP block.
 */
typedef enum dif_i3c_queue {
  // Controller queues (HCI).
  kDifI3CQueueCommand,
  kDifI3CQueueResponse,
  kDifI3CQueueXfer,
  kDifI3CQueueIBI,

  // Target queues (TTI).
  kDifI3CQueueTxData0,
  kDifI3CQueueTxData1,
  kDifI3CQueueTxData2,
  kDifI3CQueueTxData3,
  kDifI3CQueueTxDesc0,
  kDifI3CQueueTxDesc1,
  kDifI3CQueueTxDesc2,
  kDifI3CQueueTxDesc3,
  kDifI3CQueueRxData,
  kDifI3CQueueRxDesc,
  kDifI3CQueueIBIData,
  kDifI3CQueueIBIDesc,
  kDifI3CQueueAsyncEvt
} dif_i3c_queue_t;

/**
 * Physical queues implemented within the message buffer of the I3C IP block.
 *
 * The 'XFER' and 'IBI' ports of the HCI are bidirectional, introducing two
 * additional physical queues for configuration/status operations.
 */
typedef enum dif_i3c_phys_queue {
  // Controller queues/buffers (HCI).
  kDifI3CPhysQTxBuf,
  kDifI3CPhysQRxBuf,
  kDifI3CPhysQCommand,
  kDifI3CPhysQResponse,
  kDifI3CPhysQIBI,
  kDifI3CPhysQIBIStat,

  // Target queues/buffers (TTI).
  kDifI3CPhysQTxData0,
  kDifI3CPhysQTxData1,
  kDifI3CPhysQTxData2,
  kDifI3CPhysQTxData3,
  kDifI3CPhysQTxDesc0,
  kDifI3CPhysQTxDesc1,
  kDifI3CPhysQTxDesc2,
  kDifI3CPhysQTxDesc3,
  kDifI3CPhysQRxData,
  kDifI3CPhysQRxDesc,
  kDifI3CPhysQIBIData,
  kDifI3CPhysQIBIDesc,
  kDifI3CPhysQAsyncEvt
} dif_i3c_phys_queue_t;

/**
 * Immediate Data Transfer Command. Format 1 (TCRI 7.1.2.1).
 * - many fields are present in all command types; annotated here.
 */
typedef struct __attribute__((packed)) dif_i3c_cmd_imm_desc {
  unsigned cmd_attr : 3;
  unsigned tid : 4;
  unsigned cmd : 8;
  unsigned cp : 1;
  unsigned dev_index : 5;
  unsigned : 2;
  unsigned dtt : 3;
  unsigned mode : 3;
  unsigned rnw : 1;
  /**
   * Write Response On Completion.
   */
  unsigned wroc : 1;
  /**
   * Terminate On Completion.
   */
  unsigned toc : 1;
  uint8_t data_byte_1;
  uint8_t data_byte_2;
  uint8_t data_byte_3;
  uint8_t data_byte_4;
} dif_i3c_cmd_imm_desc_t;

/**
 * Regular Transfer Command. Format 1 (TCRI 7.1.2.2).
 */
typedef struct __attribute__((packed)) dif_i3c_cmd_reg_desc {
  unsigned cmd_attr : 3;
  unsigned tid : 4;
  unsigned cmd : 8;
  unsigned cp : 1;
  unsigned dev_index : 5;
  unsigned rsvd : 3;
  unsigned sre : 1;
  unsigned dbp : 1;
  unsigned mode : 3;
  unsigned rnw : 1;
  unsigned wroc : 1;
  unsigned toc : 1;
  uint8_t def_byte;
  unsigned : 8;
  uint16_t data_length;
} dif_i3c_cmd_reg_desc_t;

/**
 * Address Assignment Command (HCI 8.4.1).
 */
typedef struct __attribute__((packed)) dif_i3c_cmd_addr_desc {
  unsigned cmd_attr : 3;
  unsigned tid : 4;
  unsigned cmd : 8;
  unsigned reserved : 1;
  unsigned dev_index : 5;
  unsigned reserved1 : 5;
  unsigned dev_count : 4;
  unsigned wroc : 1;
  unsigned toc : 1;
  uint32_t reserved2;
} dif_i3c_cmd_addr_desc_t;

/**
 * Combo Transfer Command. Format 1 (TCRI 7.1.2.3).
 */
typedef struct __attribute__((packed)) dif_i3c_cmd_combo_desc {
  unsigned cmd_attr : 3;
  unsigned tid : 4;
  unsigned cmd : 8;
  unsigned cp : 1;
  unsigned dev_index : 5;
  unsigned : 1;
  unsigned dlp : 2;
  unsigned fpm : 1;
  unsigned b16 : 1;
  unsigned mode : 3;
  unsigned rnw : 1;
  unsigned wroc : 1;
  unsigned toc : 1;
  uint8_t offset;
  unsigned : 8;
  uint16_t data_length;
} dif_i3c_cmd_combo_desc_t;

/**
 * Internal Control Commands (HCI 8.4.2).
 */
typedef struct __attribute__((packed)) dif_i3c_cmd_intn_desc {
  unsigned cmd_attr : 3;
  unsigned tid : 4;
  unsigned vip : 1;
  unsigned mipi_cmd : 4;
  unsigned mipi_rsvd : 20;
  uint32_t vend_info;
} dif_i3c_cmd_intn_desc_t;

/**
 * Command Descriptor.
 * - the specific command descriptor type may be identified by inspecting
 *   `cmd_attr` field within any field.
 */
typedef union dif_i3c_cmd_desc {
  dif_i3c_cmd_imm_desc_t imm;
  dif_i3c_cmd_reg_desc_t reg;
  dif_i3c_cmd_addr_desc_t addr;
  dif_i3c_cmd_combo_desc_t combo;
  dif_i3c_cmd_intn_desc_t intn;
} dif_i3c_cmd_desc_t;

/**
 * Response Descriptor (TCRI 7.1.3).
 */
typedef struct __attribute__((packed)) dif_i3c_rsp_desc {
  uint16_t data_length;
  unsigned : 8;
  unsigned tid : 4;
  unsigned err_status : 4;
} dif_i3c_rsp_desc_t;

/**
 * IBI Status Descriptor (HCI 8.6).
 */
typedef struct __attribute__((packed)) dif_i3c_ibi_stat_desc {
  uint8_t data_length;
  uint8_t ibi_id;
  uint8_t chunks;
  unsigned last_status : 1;
  unsigned ts : 1;
  unsigned : 1;
  unsigned status_type : 3;
  unsigned error : 1;
  unsigned ibi_sts : 1;
} dif_i3c_ibi_stat_desc_t;

/**
 * Device Address Table Entry (HCI 8.1).
 */
typedef struct __attribute__((packed)) dif_i3c_dat_entry {
  unsigned static_address : 7;
  unsigned : 5;
  unsigned ibi_payload : 1;
  unsigned ibi_reject : 1;
  unsigned crr_reject : 1;
  unsigned ts : 1;
  unsigned dynamic_address : 8;
  unsigned : 2;
  unsigned ring_id : 3;
  unsigned dev_nack_retry_cnt : 2;
  unsigned device : 1;
  uint8_t autocmd_mask;
  uint8_t autocmd_value;
  unsigned autocmd_mode : 3;
  unsigned autocmd_hdr_code : 8;
  unsigned : 5;
} dif_i3c_dat_entry_t;

/**
 * Device Characteristics Table (HCI 8.2).
 */
typedef struct __attribute__((packed)) dif_i3c_dct_entry {
  uint32_t pid_hi;
  uint8_t pid_lo;
  unsigned : 16;
  uint8_t dcr;
  uint8_t bcr;
  unsigned : 16;
  uint8_t dynamic_address;
  unsigned : 24;
} dif_i3c_dct_entry_t;

/**
 * Queue Levels (HCI 7.7.7.1).
 */
typedef struct dif_i3c_hci_queue_levels {
  uint8_t cmd_queue_free;
  uint8_t rsp_buffer_level;
  uint8_t ibi_buffer_level;
  uint8_t ibi_status_cnt;
} dif_i3c_hci_queue_levels_t;

/**
 * Buffer Levels (HCI 7.7.7.2).
 */
typedef struct dif_i3c_hci_buffer_levels {
  uint8_t rx_buffer_level;
  uint8_t tx_buffer_free;
} dif_i3c_hci_buffer_levels_t;

/**
 * Queue Thresholds (HCI 7.5.5).
 */
typedef struct dif_i3c_queue_thlds {
  uint8_t cmd_empty_buf_thld;
  uint8_t resp_buf_thld;
  uint8_t ibi_seg_size;
  uint8_t ibi_status_thld;
} dif_i3c_queue_thlds_t;

/**
 * Buffer Thresholds (HCI 7.5.6).
 */
typedef struct dif_i3c_buffer_thlds {
  unsigned tx_buf_thld : 3;
  unsigned rx_buf_thld : 3;
  unsigned tx_start_thld : 3;
  unsigned rx_start_thld : 3;
} dif_i3c_buffer_thlds_t;

typedef struct __attribute__((packed)) dif_i3c_tti_prn {
  /**
   * Additional data bytes, if any.
   */
  uint16_t data;
  /**
   * Transaction ID.
   */
  unsigned tid : 4;
  /**
   * Number of additional data bytes (0-2).
   */
  unsigned len : 2;
  unsigned reserved : 3;
  /**
   * The LSBs of the Pending Read Notification MDB.
   */
  unsigned lsbs : 5;
  /**
   * Write response even on successful completion?
   */
  unsigned wroc : 1;
  /**
   * Must be 1 to indicate Pending Read Notification.
   */
  unsigned notify : 1;
} dif_i3c_tti_prn_t;

typedef struct __attribute__((packed)) dif_i3c_tti_tx {
  /**
   * Number of bytes to be transmitted.
   */
  uint16_t data_length;
  /**
   * Transaction ID.
   */
  unsigned tid : 4;
  unsigned reserved : 10;
  /**
   * Write response even on succesful completion?
   */
  unsigned wroc : 1;
  /**
   * Must be 0 to indicate Read Transfer (Controller perspective).
   */
  unsigned notify : 1;
} dif_i3c_tti_tx_t;

/**
 * TTI Transmission Descriptor.
 */
typedef union dif_i3c_tti_tx_desc {
  dif_i3c_tti_prn_t prn;
  dif_i3c_tti_tx_t tx;
} dif_i3c_tti_tx_desc_t;

/**
 * TTI Reception Descriptor.
 */
typedef struct __attribute__((packed)) dif_i3c_tti_rx_desc {
  /**
   * Number of bytes received.
   */
  unsigned data_length : 14;
  /**
   * Reserved for future use; ignore.
   */
  unsigned reserved : 1;
  /**
   * Address is a Group, rather than a Target?
   */
  unsigned is_group : 1;
  /**
   * I3C Address of the Write Transfer.
   */
  unsigned address : 7;
  /**
   * Which Target(s) matched the address.
   */
  unsigned targets : 4;
  /**
   * Result of the Write Transfer.
   */
  unsigned status : 3;
  /**
   * Write Transfer complete?
   */
  unsigned complete : 1;
  /**
   * SState of a Write Transfer?
   */
  unsigned start : 1;
} dif_i3c_tti_rx_desc_t;

typedef struct __attribute__((packed)) dif_i3c_tti_ibi_status {
  uint8_t data_length;
  unsigned tid : 4;
  unsigned t_c1_preload : 12;
  unsigned targ_id : 1;
  unsigned : 6;
  unsigned wroc : 1;
} dif_i3c_tti_ibi_status_t;

// TODO: This should be a union of multiple packed structures.
typedef struct __attribute__((packed)) dif_i3c_tti_async_evt {
  unsigned code : 4;
  unsigned info : 28;
} dif_i3c_tti_async_evt_t;

/**
 * Target-side (TTI) queue levels.
 */
typedef struct dif_i3c_tti_queue_levels {
  uint8_t async_level;
  uint8_t rx_desc_level;
} dif_i3c_tti_queue_levels_t;

/**
 * Target-side (TTI) data buffer levels.
 */
typedef struct dif_i3c_tti_buf_levels {
  uint16_t rx_buf_level;
  uint8_t ibi_free;
} dif_i3c_tti_buf_levels_t;

/**
 * Virtual Target (TTI) Tx queue levels.
 */
typedef struct dif_i3c_tti_tx_levels {
  uint16_t tx_buf_free;
  uint8_t tx_desc_free;
} dif_i3c_tti_tx_levels_t;

// Controller Configuration.
typedef struct dif_i3c_ctrl_config {
  unsigned dummy;
} dif_i3c_ctrl_config_t;

// Target Configuration.
typedef struct dif_i3c_targ_config {
  bool static_addr_valid;
  uint8_t static_addr;
} dif_i3c_targ_config_t;

// Interrupt groups.
// - the large number of interrupts which the I3C IP block can raise are
//   collected into a number of groups.
typedef enum dif_i3c_intr_group {
  kDifI3CIntrGroup_HCI,
  kDifI3CIntrGroup_PIO,
  kDifI3CIntrGroup_StbyCr,
  kDifI3CIntrGroup_Targ
} dif_i3c_intr_group_t;

// HCI-related interrupts (HCI 7.4.7).
typedef struct __attribute__((packed)) dif_i3c_intr_hci {
  unsigned : 10;
  unsigned hc_internal_err : 1;
  unsigned hc_seq_cancel : 1;
  unsigned hc_warn_cmd_seq_stall : 1;
  unsigned hc_err_cmd_seq_timeout : 1;
  unsigned sched_cmd_missed_tick : 1;
  unsigned : 17;
} dif_i3c_intr_hci_t;

// PIO mode interrupts on the Controller side (HCI 7.5.9).
typedef struct __attribute__((packed)) dif_i3c_intr_pio {
  unsigned tx_thld : 1;
  unsigned rx_thld : 1;
  unsigned ibi_status_thld : 1;
  unsigned cmd_queue_ready : 1;
  unsigned resp_ready : 1;
  unsigned transfer_abort : 1;
  unsigned : 3;
  unsigned transfer_err : 1;
  unsigned : 22;
} dif_i3c_intr_pio_t;

// Standby Controller interrupts (HCI 7.7.11.7).
typedef struct __attribute__((packed)) dif_i3c_intr_stby_cr {
  unsigned acr_handoff_ok_remain : 1;
  unsigned acr_handoff_ok_primed : 1;
  unsigned acr_handoff_err_fail : 1;
  unsigned acr_handoff_err_m3 : 1;
  unsigned : 5;
  unsigned crr_response : 1;
  unsigned stby_cr_dyn_addr : 1;
  unsigned stby_cr_accept_nacked : 1;
  unsigned stby_cr_accept_ok : 1;
  unsigned stby_cr_accept_err : 1;
  unsigned : 1;
  unsigned stby_cr_op_rstact : 1;
  unsigned ccc_param_modified : 1;
  unsigned ccc_unhandled_nack : 1;
  unsigned ccc_fatal_rstdaa_err : 1;
  unsigned : 13;
} dif_i3c_intr_stby_cr_t;

// Target-side (TTI) interrupts.
typedef struct __attribute__((packed)) dif_i3c_intr_targ {
  unsigned rx_desc_ready : 1;
  unsigned ibi_status_thld : 1;
  unsigned async_evt_ready : 1;
  unsigned transfer_abort : 1;
  unsigned transfer_err : 1;
  unsigned rx_buffer_ovl : 1;
  unsigned async_evt_ovl : 1;
  unsigned tx_thld : 4;        // encompasses all Virtual Targets.
  unsigned tx_desc_ready : 4;  // encompasses all Virtual Targets.
  unsigned : 12;
  unsigned te_stat : 1;
} dif_i3c_intr_targ_t;

/**
 * Group of interrupts from the I3C IP block.
 *
 * This struct is a tagged union because there is nothing within the set of
 * interrupt status/status_enables/signal_enables for a group that identifies
 * the group; the `group` field determines which field of the union is
 * relevant.
 */
typedef struct dif_i3c_interrupts {
  /** The interrupt group concerned. */
  dif_i3c_intr_group_t group;
  union {
    uint32_t interrupts;
    dif_i3c_intr_hci_t hci;
    dif_i3c_intr_pio_t pio;
    dif_i3c_intr_stby_cr_t stby_cr;
    dif_i3c_intr_targ_t targ;
  };
} dif_i3c_interrupts_t;

/**
 * Controller operating mode.
 */
typedef enum dif_i3c_ctrl_mode {
  kI3CCtrlMode_Disabled,
  kI3CCtrlMode_Active,
  kI3CCtrlMode_Standby
} dif_i3c_ctrl_mode_t;

/**
 * Enabled/connected state of the Target.
 */
typedef enum dif_i3c_targ_state {
  kI3CTargMode_Disabled,
  kI3CTargMode_Enabled,
  kI3CTargMode_Connected
} dif_i3c_targ_state_t;

/**
 * Callback function for on-the-fly supply of write data.
 */
typedef dif_result_t (*dif_i3c_tx_cb_t)(void *ws, uint32_t *pd);

/**
 * Callback function for on-the-fly consumption of read data.
 */
typedef dif_result_t (*dif_i3c_rx_cb_t)(void *ws, uint32_t d);

/**
 * Return the current message buffer allocation of the given queue.
 *
 * @param i3c An I3C block.
 * @param id The queue being queried.
 * @param min_addr Receives the inclusive minimum address of the buffer
 * allocation.
 * @param max_addr Receives the inclusive maximum address of the buffer
 * allocation.
 * @param size_val Receives the size indicator, for HCI queues, or 0 for TTI.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_config_queue_get(const dif_i3c_t *i3c,
                                      dif_i3c_phys_queue_t id,
                                      unsigned *min_addr, unsigned *max_addr,
                                      unsigned *size_val);

/**
 * Configure the message buffer allocation of the given queue.
 * This is a low-level API and the caller is trusted to ensure that queues do
 * not overlap.
 *
 * @param i3c An I3C block.
 * @param id The queue being configured.
 * @param min_addr The inclusive minimum address of the allocated range.
 * @param max_addr The inclusive maximum address of the allocated range.
 * @param size_val The size indicator, for HCI queues.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_config_queue_set(const dif_i3c_t *i3c,
                                      dif_i3c_phys_queue_t id,
                                      unsigned min_addr, unsigned max_addr,
                                      unsigned size_val);

/**
 * Configure the Controller-side of the I3C block.
 *
 * @param i3c An I3C block.
 * @param cfg Configuration for the Controller.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_ctrl_configure(const dif_i3c_t *i3c,
                                    const dif_i3c_ctrl_config_t *cfg);

/**
 * Configure a Virtual Target within the I3C block.
 *
 * @param i3c An I3C block.
 * @param id The number of the Virtual Target to be configured.
 * @param cfg Configuration for the Virtual Target.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_configure(const dif_i3c_t *i3c, unsigned id,
                                    const dif_i3c_targ_config_t *cfg);

/**
 * Return the current global state of the I3C Target peripheral.
 *
 * @param i3c An I3C block.
 * @param state Receives the current state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_state(const dif_i3c_t *i3c,
                                dif_i3c_targ_state_t *state);

/**
 * Set the Controller mode of operation (Disabled, Active or Standby).
 *
 * @param i3c An I3C block.
 * @param mode Controller operation mode.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_ctrl_mode_set(const dif_i3c_t *i3c,
                                   dif_i3c_ctrl_mode_t mode);

/**
 * Specify which Virtual Targets are enabled.
 *
 * @param i3c An I3C block.
 * @param enables The enabled/disabled state for each of the Virtual Targets
 *                in turn.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_enables_set(const dif_i3c_t *i3c, uint32_t enables);

/**
 * Program an entry within the Device Addresss Table (DAT).
 *
 * @param i3c An I3C block.
 * @param idx The index (0-31) of the DAT entry.
 * @param entry The new content of this entry within the DAT.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_dat_entry_set(const dif_i3c_t *i3c, uint8_t idx,
                                   const dif_i3c_dat_entry_t *entry);

/**
 * Read the current index into the Device Characteristics Table (DCT).
 *
 * @param i3c An I3C block.
 * @param idx Receives the current DCT index.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_dct_index_get(const dif_i3c_t *i3c, uint8_t *idx);

/**
 * Set the current index of the DCT.
 *
 * @param i3c An I3C block.
 * @param idx The new DCT index.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_dct_index_set(const dif_i3c_t *i3c, uint8_t idx);

/**
 * Retrieve an entry from the Device Characteristics Table (DCT).
 *
 * @param i3c An I3C block.
 * @param idx The index (0-31) of the DCT entry.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_dct_entry_get(const dif_i3c_t *i3c, uint8_t idx,
                                   dif_i3c_dct_entry_t *entry);

/**
 * Raw write of data to the XFER_DATA_PORT of the Controller; all 'DWORD'
 * quantities except perhaps the last shall be complete and 4n byte-aligned
 * within the memory.
 *
 * @param i3c An I3C block.
 * @param data The sequence of DWORDs to be programmed into XFER_DATA_PORT
 *             for transmission.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_xfer_write(const dif_i3c_t *i3c, const uint32_t *data,
                                uint16_t nbytes);

/**
 * Raw write of a sequence of Command Descriptors to the COMMAND_QUEUE_PORT
 * of the Controller.
 *
 * @param i3c An I3C block.
 * @param cmd Sequence of Command Descriptors.
 * @param num The number of Command Descriptors to write.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_command_write(const dif_i3c_t *i3c,
                                   const dif_i3c_cmd_desc_t *cmd, uint8_t num);

/**
 * Raw read of a number of Response Descriptors from the RESPONSE_QUEUE_PORT
 * of the Controller.
 *
 * @param i3c An I3C block.
 * @param rsp Receives the next 'num' Response Descriptor(s) from the queue.
 * @param num The number of Response Descriptors to return.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_response_read(const dif_i3c_t *i3c,
                                   dif_i3c_rsp_desc_t *rsp, uint8_t num);

/**
 * Read read of data from the XFER_DATA_PORT of the Controller; all 'DWORD'
 * quantities except perhaps the last shall be complete and 4n byte-aligned
 * within the memory.
 *
 * @param i3c An I3C block.
 * @param buf The buffer via which data bytes shall be returned.
 * @param nbytes The number of bytes to return.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_xfer_read(const dif_i3c_t *i3c, uint32_t *buf,
                               uint16_t nbytes);

/**
 * Read the current levels of data within the queues (Command, Response and
 * IBI) of the Controller.
 *
 * @param i3c An I3C block.
 * @param levels Receives the levels description.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_queue_levels_read(const dif_i3c_t *i3c,
                                       dif_i3c_hci_queue_levels_t *levels);

/**
 * Read the current levels of data within the buffers (Tx and Rx) of the
 * Controller.
 *
 * @param i3c An I3C block.
 * @param levels Receives the levels description.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_buffer_levels_read(const dif_i3c_t *i3c,
                                        dif_i3c_hci_buffer_levels_t *levels);

/**
 * Read the current levels of the Target-side (TTI) queues.
 *
 * @param i3c An I3C block.
 * @param levels Receives the level information.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_queue_levels_read(const dif_i3c_t *i3c,
                                            dif_i3c_tti_queue_levels_t *levels);

/**
 * Read the current levels of the Target-side (TTI) data buffers.
 *
 * @param i3c An I3C block.
 * @param levels Receives the level information.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_buf_levels_read(const dif_i3c_t *i3c,
                                          dif_i3c_tti_buf_levels_t *levels);

/**
 * Read the current levels of the Target-side (TTI) Transmission queues.
 * (per Virtual Target).
 *
 * @param i3c An I3C block.
 * @param id The Virtual Target.
 * @param levels Receives the level information.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_tx_levels_read(const dif_i3c_t *i3c, unsigned id,
                                         dif_i3c_tti_tx_levels_t *levels);

/**
 * Set the Controller Queue thresholds.
 *
 * @param i3c An I3C block.
 * @param thlds The new thresholds to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_queue_thld_set(const dif_i3c_t *i3c,
                                    const dif_i3c_queue_thlds_t *thlds);

/**
 * Return the current Controller Queue thresholds.
 *
 * @param i3c An I3C block.
 * @param thlds Receives the current thresholds.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_queue_thld_get(const dif_i3c_t *i3c,
                                    dif_i3c_queue_thlds_t *thlds);

/**
 * Set the Controller Data Buffer thresholds.
 *
 * @param i3c An I3C block.
 * @param thlds The new thresholds to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_buffer_thld_set(const dif_i3c_t *i3c,
                                     const dif_i3c_buffer_thlds_t *thlds);

/**
 * Return the current Controller Data Buffer thresholds.
 *
 * @param i3c An I3C block.
 * @param thlds Receives the current thresholds.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_buffer_thld_get(const dif_i3c_t *i3c,
                                     dif_i3c_buffer_thlds_t *thlds);

/**
 * Read from the IBI_QUEUE_PORT of the Controller and return it as an IBI
 * Status Descriptor.
 *
 * @param i3c An I3C block.
 * @param desc Receives the IBI Status Descriptor.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_ctrl_desc_ibi_recv(const dif_i3c_t *i3c,
                                        dif_i3c_ibi_stat_desc_t *desc);

/**
 * Read a sequence of bytes from the IBI_QUEUE_PORT of the Controller, as
 * described by the preceding IBI Status Descriptor; all 'DWORD' quantities,
 * except perhaps the last, shall be complete and 4n byte-aligned within the
 * memory.
 *
 * @param i3c An I3C block.
 * @param buf The buffer to received the DWORDs of data.
 * @param nbytes The number of bytes to be received; this must be 4n if there
 *               is more data to be received.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_ctrl_data_ibi_recv(const dif_i3c_t *i3c, uint32_t *buf,
                                        uint16_t nbytes);

/**
 * Supply a TTI Tx Descriptor and associated initial data for Private Read
 * collection; all 'DWORD' quantities except perhaps the last shall be
 * complete and 4n byte-aligned within the memory.
 *
 * @param i3c An I3C block.
 * @param id The Virtual Target.
 * @param desc TTI Tx Descriptor to be programmed.
 * @param data Initial data to be transmitted.
 * @param nbytes Number of bytes of initial data; must be 4n if there is to
 *               be additional data.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_send(const dif_i3c_t *i3c, unsigned id,
                               const dif_i3c_tti_tx_desc_t *desc,
                               const uint32_t *data, uint16_t nbytes);

/**
 * Supply additional data for a Private Read transfer from the specified
 * Virtual Target; all 'DWORD' quantities except perhaps the last shall
 * be complete and 4n byte-aligned within the memory.
 *
 * @param i3c An I3C block.
 * @param id The Virtual Target.
 * @param data The DWORDs to be transmitted.
 * @param nbytes Number of bytes to be transmitted; must be 4n if there is
 *               more to follow.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_data_send(const dif_i3c_t *i3c, unsigned id,
                                    const uint32_t *data, uint16_t nbytes);

/**
 * Collect a TTI Rx Descriptor.
 *
 * @param i3c An I3C block.
 * @param desc Receives the TTI Rx Descriptor(s).
 * @param num The number of descriptors to read.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_recv(const dif_i3c_t *i3c,
                               dif_i3c_tti_rx_desc_t *desc, unsigned num);

/**
 * Retrieve some Rx Data from the specified Virtual Target, as described by
 * a previously-collected TTI Rx Descriptor; all 'DWORD' quantities except
 * perhaps the last shall be complete and 4n byte-aligned within the memory.
 *
 * @param i3c An I3C block.
 * @param buf Buffer to receive the DWORDs.
 * @param nbytes Number of bytes to receive; must be 4n if this is not th
 *               final part of the transfer.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_data_recv(const dif_i3c_t *i3c, uint32_t *buf,
                                    uint16_t nbytes);

/**
 * Present an In-Band Interrupt for collection from the given Virtual Target.
 *
 * @param i3c An I3C block.
 * @param desc The TTI IBI Status Descriptor, including the Virtual Target ID.
 * @param data The initial data to be transmitted.
 * @param nbytes Initial number of bytes to be transmitted; this must be 4n if
 *               there is more data to follow.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_desc_ibi_send(const dif_i3c_t *i3c,
                                        const dif_i3c_tti_ibi_status_t *desc,
                                        const uint32_t *data, uint16_t nbytes);

/**
 * Supply additional IBI data for collection from a Virtual Target.
 *
 * @param i3c An I3C block.
 * @param data The additional data to be transmitted.
 * @param nbytes The number of additional bytes; this must be 4n if there
 *               is more data to follow for this IBI.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_targ_data_ibi_send(const dif_i3c_t *i3c,
                                        const uint8_t *data, uint16_t nbytes);

/**
 * Collect a number of Asynchronous Events from the TTI Queue.
 *
 * @param i3c An I3C block.
 * @param descs Received the Asynchronous Event descriptors.
 * @param num The number of descriptors to collect.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_async_evt_recv(const dif_i3c_t *i3c,
                                    dif_i3c_tti_async_evt_t *descs,
                                    uint8_t num);

/**
 * Push data into the chosen I3C Queue/Buffer. Each queue/buffer is mapped to
 * a single address within the I3C block and accepts a sequence of DWORDs.
 *
 * @param i3c An I3C block.
 * @param id Queue/Buffer ID.
 * @param data The DWORDs to be pushed into the queue/buffer.
 * @param n The number of DWORDs; the queue/buffer accepts only complete
 *          DWORDs and the associated transfer descriptor specifies the
 *          exact transfer length at the byte level.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_queue_push(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                                const uint32_t data[], uint16_t n);

/**
 * Push dynamically-generated data into the chosen I3C Queue/Buffer. This
 * variant avoids the overhead of populating a buffer in system RAM and
 * then copying the data to the I3C block.
 *
 * @param i3c An I3C block.
 * @param id Queue/Buffer ID.
 * @param cb Callback function to generate the next DWORD value.
 * @param ws Workspace pointer for the callback function.
 * @param n The number of DWORDs; the queue/buffer accepts only complete
 *          DWORDs and the associated transfer descriptor specifies the
 *          exact transfer length at the byte level.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_queue_push_cb(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                                   dif_i3c_tx_cb_t cb, void *ws, uint16_t n);

/**
 * Pop data from the chosen I3C Queue/Buffer. Each queue/buffer is mapped to
 * a single address within the I3C block and offers a sequence of DWORDs.
 *
 * @param i3c An I3C block.
 * @param id Queue/Buffer ID.
 * @param buf Receives the DWORDs popped from the queue/buffer.
 * @param n The number of DWORDs; the exact transfer length at the byte level
 *          is specified in the associated transfer descriptor and the queue/
 *          buffer deals only in complete DWORDs.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_queue_pop(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                               uint32_t *buf, uint16_t n);

/**
 * Pop data from the chosen I3C Queue/Buffer, passing each DWORD to the supplied
 * callback function for checking/processing.
 *
 * @param i3c An I3C block.
 * @param id Queue/Buffer ID.
 * @param cb Callback function to check/process each DWORD value.
 * @param ws Workspace pointer for the callback function.
 * @param n The number of DWORDs.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_queue_pop_cb(const dif_i3c_t *i3c, dif_i3c_queue_t id,
                                  dif_i3c_rx_cb_t cb, void *ws, uint16_t n);

/**
 * Retrieve the current status of the interrupts within the group specified
 * via the `status` parameter.
 *
 * @param i3c An I3C block.
 * @param status Receives the status of the interrupts; `group` must already
 *               have been completed by the caller.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_intr_status_get(const dif_i3c_t *i3c,
                                     dif_i3c_interrupts_t *status);

/**
 * Clears a set of interrupts within a specific group. To clear an interrupt
 * its corresponding bit must be set to '1'; those set to '0' will be
 * unaffected.
 *
 * @param i3c An I3C block.
 * @param status Specifies the interrupt group and the interrupts to be
 *               cleared.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_intr_status_clear(const dif_i3c_t *i3c,
                                       const dif_i3c_interrupts_t *clear);

/**
 * Retrieve the current status enables for the interrupts within the group
 * specified via the `enables` parameter.
 *
 * @param i3c An I3C block.
 * @param enables Receives the status enables of the interrupts; `group` must
 *                already have been completed by the caller.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_intr_status_enable_get(const dif_i3c_t *i3c,
                                            dif_i3c_interrupts_t *enables);

/**
 * Sets the status enables for the interrupts within a group.
 *
 * @param i3c An I3C block.
 * @param enables Selects the interrupt group and specifies the new status
 *                enables.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_intr_status_enable_set(
    const dif_i3c_t *i3c, const dif_i3c_interrupts_t *enables);

/**
 * Retrieve the current signal enables for the interrupts within the group
 * specified via the `enables` parameter.
 *
 * @param i3c An I3C block.
 * @param enables Receives the signal enables of the interrupts; `group` must
 *                already have been completed by the caller.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_intr_signal_enable_get(const dif_i3c_t *i3c,
                                            dif_i3c_interrupts_t *enables);

/**
 * Sets the signal enables for the interrupts within a group.
 *
 * @param i3c An I3C block.
 * @param enables Selects the interrupt group and specifies the new signal
 *                enables.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_intr_signal_enable_set(
    const dif_i3c_t *i3c, const dif_i3c_interrupts_t *enables);

/**
 * Read the state of the 'force interrupt' signals for a given interrupt group.
 *
 * @param i3c An I3C block.
 * @param force Selects the interrupt group; `group` must already have been
 *              completed by the caller.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_intr_force_get(const dif_i3c_t *i3c,
                                    dif_i3c_interrupts_t *force);

/**
 * Set the state of the 'force interrupt' signals for a given interrupt group.
 *
 * @param i3c An I3C block.
 * @param force Selects the interrupt group and specifies the new force inputs.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_intr_force_set(const dif_i3c_t *i3c,
                                    const dif_i3c_interrupts_t *force);

/**
 * Determine the number of data bytes associated with a Command Descriptor.
 *
 * @param i3c An I3C block.
 * @param cmd Command Descriptor.
 * @param len Receives the number of data bytes associated with the command.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_i3c_cmd_data_length(const dif_i3c_cmd_desc_t *cmd,
                                     uint16_t *len);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_I3C_H_
