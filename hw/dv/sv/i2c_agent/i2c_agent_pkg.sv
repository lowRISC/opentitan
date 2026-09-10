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

  // Assign drv_type and wdata to within each I2C transfer for i2c_driver so that it can generate
  // the appropriate bus traffic.
  function automatic i2c_item assign_drv_type_and_data(drv_type_e drv_type, bit [7:0] data);
    i2c_item item = i2c_item::type_id::create("item");
    item.drv_type = drv_type;
    item.wdata = data;
    return item;
  endfunction

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
      if (xfer.start)
        // 'START' condition begins the transfer (and transaction)
        drv_q.push_back(assign_drv_type_and_data(HostStart, '0));
      else if (xfer.rstart_front)
        // If we are here then the last transfer ended with a rstart_back which should have been
        // assigned with .drv_type = HostRStart, so omit assigning it here.
        `uvm_info($sformatf("%m"),
                  "Omitting .drv_type = HostRStart item from driver queue.",
                  UVM_FULL)
      else
        `uvm_fatal($sformatf("%m"),
                   "Can't create a transfer that doesn't start with either START or RSTART!")

      // Add the address+direction byte
      drv_q.push_back(assign_drv_type_and_data(HostData, (xfer.addr[6:0] << 1) | xfer.dir));

      // Push data bytes and responses based on the bus operation
      for (int i = 0; i < xfer.num_data; i++) begin
        case (xfer.bus_op)
          BusOpWrite:
            drv_q.push_back(assign_drv_type_and_data(HostData, xfer.data_q[i]));
          BusOpRead: begin
            drv_type_e ack_nack = (xfer.data_ack_q[i] == i2c_pkg::ACK) ? HostAck : HostNAck;
            drv_q.push_back(assign_drv_type_and_data(ack_nack, '0));
          end
          default:;
        endcase
      end

      // Add the 'STOP' or 'RSTART' condition to end the transaction / transfer
      if (xfer.stop)
        // 'STOP' condition ends the transfer (and transaction)
        drv_q.push_back(assign_drv_type_and_data(HostStop, '0));
      else if (xfer.rstart_back)
        // 'RSTART' condition ends the transfer
        drv_q.push_back(assign_drv_type_and_data(HostRStart, '0));
      else
        `uvm_fatal($sformatf("%m"),
                   "Can't create a transfer that doesn't end with either STOP or RSTART!")
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
