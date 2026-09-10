// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Controller-side CCC definitions.

package i3c_ctrl_ccc_pkg;
  import i3c_consts_pkg::*;
  import i3c_controller_pkg::*;
  import i3c_pkg::*;

  // These are bit indexes within the `CtrlCR_Status` register.
  typedef enum {
    CtrlStat_SendFraming = 0,
    CtrlStat_HasDEFB
  } i3c_ctrl_ccc_flags_e;

  // Width of the registers devoted to Controller CCC handling.
  localparam int unsigned CtrlCRWidth = 'd8;

  // Indexes of the registers available for use within the Controller CCC handling.
  typedef enum logic [2:0] {
    // CCC - this always holds the Common Command Code itself.
    CtrlCR_CCC = 0,
    // Defining Byte, if present
    // - DEFB and CCC are retained from the previous Command Descriptor, to determine whether a new
    //   CCC must be transmitted.
    CtrlCR_DEFB,
    // Flags holding state information about CCC Framing (see `i3c_ctrl_ccc_flags_e` above).
    CtrlCR_Status,
    // Scratch registers.
    CtrlCR_Scratch,
    // Sentinel gives the number of available registers.
    CtrlCR_Count
  } i3c_ctrl_ccc_reg_e;

  // Requests to the Controller CCC handling.
  typedef struct packed {
    // Data byte(s) from the Command Descriptor or the Tx Buffer.
    logic              txd_valid;
    logic              txd_left;
    logic        [1:0] txd_len;
    logic     [DW-1:0] txd_data;
    // DAT entry for the current Target.
    i3c_dat_mem_t      dat_entry;
    // Index number within the current CCC handling.
    // - this is effectively a local state number that the CCC logic may use; it will be reset
    //   and/or incremented according to the previous response from the CCC logic.
    logic        [3:0] idx;
    // The byte(s) of data just received from the Target.
    logic              re;
    logic [Log2DW-3:0] rlen;
    logic     [DW-1:0] rdata;
    // Raw Command Descriptor, should additional information be required.
    logic       [63:0] cmd_raw;
  } i3c_ctrl_ccc_req_t;

  // Responses from the Controller CCC handling.
  typedef struct packed {
    // Completion of this CCC transfer.
    logic                   done;
    // Reset or increment state index upon state transition?
    // - CCC handling may use this to count clock cycles, count states and/or reset the current
    //   state index as desired.
    // - Reset takes precedence over increment.
    logic                   rst_idx;
    logic                   inc_idx;
    // Error status.
    i3c_err_status_e        err_status;
    // Further transmit data required?
    logic                   txd_req;
    // Consume the transmit data?
    logic                   txd_consume;
    // Register access.
    // - all registers are presented directly to the CCC handling at all times; there is no need
    //   for an explicit read operation.
    // - register writes are clocked and the updated register value will be available in the next
    ///  cycle.
    logic                   reg_we;
    // Register number for writing.
    i3c_ctrl_ccc_reg_e      reg_widx;
    // Register write data.
    logic [CtrlCRWidth-1:0] reg_wdata;
    // Data requests to the Controller transceiver logic.
    // TODO: These request fields are a significant subset of the `i3c_ctrl_trx_txd_t` structure,
    // so perhaps this warrants a nested structure, which the FSM logic can propagate wholesale?
    logic                   req_dvalid;
    i3c_ctrl_req_e          req_type;
    logic                   req_rx;
    logic             [1:0] req_len;
    logic          [DW-1:0] req_wdata;
    logic                   req_last;
  } i3c_ctrl_ccc_rsp_t;

endpackage
