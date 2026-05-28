// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// I2C specification (revision 6):
// https://web.archive.org/web/20210813122132/https://www.nxp.com/docs/en/user-guide/UM10204.pdf

package i2c_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_agent_pkg::*;
  import dv_lib_pkg::*;

  import i2c_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Bus/Transaction types for the agent driver
  typedef enum logic [3:0] {
    None, DevAck, DevNack, RdData, WrData,
    HostStart, HostRStart, HostData, HostAck,
    HostNAck, HostStop, HostDataNoWaitForACK,
    HostWait
  } drv_type_e;

  // This enum is used to model the current state of an in-progress i2c transfer
  typedef enum int {
    StNone,
    StStarted,
    StAddrByte,
    StAddrByteRcvd,
    StAddrByteAckRcvd,
    StDataByte,
    StDataByteRcvd,
    StDataByteAckRcvd,
    StStopped,
    StAborted
  } transfer_state_e;

  // register values
  typedef struct {
    // derived parameters
    bit  [31:0]  tSetupStart;
    bit  [31:0]  tHoldStart;
    bit  [31:0]  tClockStart;
    bit  [31:0]  tClockLow;
    bit  [31:0]  tSetupBit;
    bit  [31:0]  tClockPulse;
    bit  [31:0]  tHoldBit;
    bit  [31:0]  tClockStop;
    bit  [31:0]  tSetupStop;
    bit  [31:0]  tHoldStop;
    bit          enbTimeOut;
    bit  [30:0]  tTimeOut;
    uint         tStretchHostClock;

    // sda_unstable interrupt will be asserted if
    // tSdaUnstable is set to a non-zero value, otherwise
    uint         tSdaUnstable;
    // scl_interference interrupt will be asserted if
    // tSclInterference is set to a zero value, otherwise
    uint         tSclInterference;
    // sda_interference interrupt will be asserted if
    // tSdaInterference is set to a zero value, otherwise
    uint         tSdaInterference;
  } timing_cfg_t;

  typedef enum int {
    Addr7BitMode  = 7,
    Addr10BitMode = 10
  } i2c_target_addr_mode_e;

  // forward declare classes to allow typedefs below
  typedef class i2c_item;
  typedef class i2c_agent_cfg;

  typedef uvm_tlm_analysis_fifo #(i2c_item) i2c_analysis_fifo;

  typedef i2c_item i2c_transfer_q[$];
  typedef i2c_transfer_q i2c_transaction;

  // The i2c_driver is controlled by providing it a queue of sequence items, each of which
  // specifies the driving behaviour with the following fields:
  // - drv_type
  // - wdata
  // - rdata
  // This function converts an i2c_item targeted at the transfer-level to a queue of items that
  // control the driver to create an equivalent bus state.
  //
  // This behaviour isn't ideal, as we are re-using the i2c_item to do something completely
  // different from how it is used elsewhere. In fact, the i2c_item type would be better renamed
  // to a i2c_transfer_item, as really this is the level of abstraction it operates at.
  // The 3 fields above are not used, except for controlling the i2c_driver.
  // #TODO Move to agent sequence ideally. (also see #14825)
  function automatic void convert_i2c_txn_to_drv_q(i2c_transaction txn, ref i2c_item drv_q[$]);

    // Loop over each transfer, determine what to drive based on the control flags
    foreach (txn[transfer_i]) begin
      i2c_item xfer = txn[transfer_i];

      // The transfer must begin with a 'START' or 'RSTART' condition
      if (xfer.start) begin
        // 'START' condition begins the transfer (and transaction)
        i2c_item start_txn;
        `uvm_create_obj(i2c_item, start_txn)
        start_txn.drv_type = HostStart;
        drv_q.push_back(start_txn);
      end else if (xfer.rstart_front) begin
        // 'RSTART' condition begins the transfer (which is only possible if the previous
        // transfer ends with an RSTART).
        // Sending duplicate messages with .drv_type = HostRStart would cause the driver to
        // produce invalid traffic, so simply omit sending it here.
        `uvm_info($sformatf("%m"),
                  "Omitting .drv_type = HostRStart item from driver queue.",
                  UVM_FULL)
      end else begin
        `uvm_fatal($sformatf("%m"),
                   "Can't create a transfer that doesn't start with either START or RSTART!")
      end

      // Add the address+direction byte
      begin
        i2c_item addr_txn;
        `uvm_create_obj(i2c_item, addr_txn)
        addr_txn.drv_type = HostData;
        addr_txn.wdata[7:1] = xfer.addr[6:0];
        addr_txn.wdata[0] = xfer.dir;
        drv_q.push_back(addr_txn);
      end

      // Add items for all the data bytes
      foreach (xfer.data_q[i]) begin
        case (xfer.bus_op)
          BusOpWrite: begin
            // For write bytes, we drive the data using 'HostData'
            i2c_item data_txn;
            `uvm_create_obj(i2c_item, data_txn)
            data_txn.drv_type = HostData;
            data_txn.wdata = xfer.data_q[i];
            drv_q.push_back(data_txn);
          end
          BusOpRead: begin
            // For read bytes, we wait 8 bit-periods then ack or nack (The driver behaviour
            // for both 'HostAck' and 'HostNAck' include this 8-bit wait)
            i2c_item acknack_txn;
            `uvm_create_obj(i2c_item, acknack_txn)
            acknack_txn.drv_type = (xfer.data_ack_q[i] == i2c_pkg::ACK) ? HostAck : HostNAck;
            drv_q.push_back(acknack_txn);
          end
          default:;
        endcase
      end

      // Add the 'STOP' or 'RSTART' condition to end the transfer
      if (xfer.stop) begin
        // 'STOP' condition ends the transfer (and transaction)
        i2c_item stop_txn;
        `uvm_create_obj(i2c_item, stop_txn)
        stop_txn.drv_type = HostStop;
        drv_q.push_back(stop_txn);
      end else if (xfer.rstart_back) begin
        // 'RSTART' condition ends the transfer
        i2c_item rstart_txn;
        `uvm_create_obj(i2c_item, rstart_txn)
        rstart_txn.drv_type = HostRStart;
        drv_q.push_back(rstart_txn);
      end else begin
        `uvm_fatal($sformatf("%m"),
                   "Can't create a transfer that doesn't end with either STOP or RSTART!")
      end
    end

  endfunction : convert_i2c_txn_to_drv_q

  // package sources
  `include "i2c_fdata_item.sv"
  `include "i2c_acqdata_item.sv"
  `include "i2c_item.sv"
  `include "i2c_agent_cfg.sv"
  `include "i2c_agent_cov.sv"
  `include "i2c_monitor.sv"
  `include "i2c_driver.sv"
  `include "i2c_sequencer.sv"
  `include "i2c_agent.sv"
  `include "seq_lib/i2c_seq_list.sv"

endpackage: i2c_agent_pkg
