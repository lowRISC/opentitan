// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Target-side CCC handling definitions.

package i3c_targ_ccc_pkg;
  import i3c_pkg::*;
  import i3c_consts_pkg::*;

  // Width of the registers devoted to Target CCC handling.
  localparam int unsigned TargCRWidth = 'd8;

  // These are bit indexes within the `TargCR_Status` register.
  typedef enum {
    TargStat_HasDEFB = 0,
    TargStat_IsGroup,
    // TODO: The following is not yet used...
    TargStat_ReadSeg   // Is this a Read Segment rather than Write?
  } i3c_targ_ccc_flags_e;

  // Indexes of the registers available for use within the Target CCC handling.
  typedef enum logic [2:0] {
    // CCC - this always holds the Common Command Code itself.
    TargCR_CCC = 0,
    // Defining Byte, if present.
    // - DEFB and CCC may have been retained from the beginning of this CCC transfer.
    TargCR_DEFB,
    // Flags holding state information about CCC Framing (see `i3c_targ_ccc_flags_e` above).
    TargCR_Status,
    // Set of affected targets.
    TargCR_Targets,
    // Write data registers.
    //
    // Note: DEFTGTS and DEFGRPA will have to stream their data payloads into the Rx + RxDesc
    // buffers. Each could conceivably be hundreds of bytes:
    // - DEFTGTS: 1 + 4 for Active Controller + (4 per Target/Group), no intervening Sr/P.
    // - DEFGRPA: 3 + (1 per Target within Group), with no Sr/P.
    TargCR_WData0,
    TargCR_WData1,
    TargCR_WData2,
    // Sentinel gives the number of available registers.
    TargCR_Count
  } i3c_targ_ccc_reg_e;

  // Reasons for invoking the Target CCC handling.
  typedef enum logic [1:0] {
    TargCRsn_RxD = 0,  // Data received.
    TargCRsn_TxD,      // Data to be transmitted.
    TargCRsn_Sr,       // Repeated start (Sr), during CCC handling.
    TargCRsn_P         // Stop (P), indicating the end of CCC transfer.
  } i3c_targ_ccc_rsn_e;

  // Requests to the Target CCC handling.
  typedef struct packed {
    logic               rnw;  // TODO: Possibly becomes a status flag (`i3c_targ_ccc_flags_e`).
    logic               en;
    i3c_targ_ccc_rsn_e  rsn;
    // Index number within the current CCC handling.
    // - this is effectively a local state number that the CCC logic may use,
    //   it will be incremented.
    logic         [3:0] idx;
    // Which of Repeated start (Sr) or Start (S) was mostly received from the Controller?
    // - this allows the CCC logic to ascertain whether the command still being set up, or whether
    //   the frame has progressed to addressing targets/groups.
    logic               sr;
    // The byte of data just received from the Controller, if any.
    logic               re;
    logic         [7:0] rdata;
    // Addressing information.
    logic               is_group;
    logic [TargIDW-1:0] targ_id;
  } i3c_targ_ccc_req_t;

  // Responses from the Target CCC handling.
  typedef struct packed {
    // Reset or increment state index upon state transition?
    // - CCC handling may use this to count clock cycles, count states and/or reset the current
    //   state index as desired.
    // - Reset takes precedence over increment.
    logic                       rst_idx;
    logic                       inc_idx;
    // Register access.
    // - all registers are presented directly to the CCC handling at all times; there is no need
    //   for an explicit read operation.
    // - register writes are clocked and the updated register value will be available in the next
    ///  cycle.
    logic                       reg_we;
    // Register number for writing.
    i3c_targ_ccc_reg_e          reg_widx;
    // Register write data.
    logic     [TargCRWidth-1:0] reg_wdata;

    // CCC data for transmission by the Target transceiver logic.
    logic                       req_cvalid;
    logic                       req_clast;
    logic [NumTargets-1:0][7:0] req_cdata;
  } i3c_targ_ccc_rsp_t;

endpackage
