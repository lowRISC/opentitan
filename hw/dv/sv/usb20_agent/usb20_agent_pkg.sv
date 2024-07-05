// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package usb20_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // USB 2.0 Bus Symbols
  typedef enum {
    USB20Sym_SE0,     // EOP, Bus Reset.
    USB20Sym_J,       // Idle.
    USB20Sym_K,       // SOP, Resume Signaling.
    USB20Sym_Invalid  // Not Used.
  } usb_symbol_e;

  // TODO: rename this enumeration type; not all usb20_item instances are packets any longer.
  //
  // Item Types
  typedef enum bit [2:0] {
      // Packet items.
      PktTypeSoF,
      PktTypeToken,
      PktTypeData,
      PktTypeHandshake,
      PktTypeSpecial,
      // Non-packet items.
      PktTypeEvent} pkt_type_e;

  // USB-level events; the DP/DN wires are used for transmitting packet data but also held for
  // extended intervals to signal specific bus-level events.
  typedef enum bit [2:0] {
      EvBusReset,   // DP low, DN low.
      EvSuspend,    // Idle for > 3ms.
      EvResume,     // DP low, DN high.
      EvDisconnect, // VBUS low when disconnected.
      EvConnect,    // VBUS high after connection.
      EvPacket} ev_type_e;

  // Packet IDentifiers; the 4 LSBs identify the Packet type, and are reflected in inverted
  //   form as the 4 MSBs to provide some internal error checking.
  typedef enum bit [7:0] {
      // Token PIDs
      PidTypeOutToken = 8'b1110_0001, PidTypeInToken    = 8'b0110_1001,
      PidTypeSofToken = 8'b1010_0101, PidTypeSetupToken = 8'b0010_1101,
      // Data PIDs
      PidTypeData0 = 8'b1100_0011, PidTypeData1 = 8'b0100_1011,
      PidTypeData2 = 8'b1000_0111, PidTypeMData = 8'b0000_1111,
      // Handshake PIDs
      PidTypeAck   = 8'b1101_0010, PidTypeNak  = 8'b0101_1010,
      PidTypeStall = 8'b0001_1110, PidTypeNyet = 8'b1001_0110,
      // Special PIDs
      PidTypePre   = 8'b0011_1100, PidTypeSplit = 8'b0111_1000,
      PidTypePing  = 8'b1011_0100} pid_type_e;

  typedef enum byte {bmRequestType0 = 8'b0_00_00000, bmRequestType1 = 8'b0_00_00001,
      bmRequestType2 = 8'b0_00_00010, bmRequestType3 = 8'b1_00_00000,
      bmRequestType4 = 8'b1_00_00001, bmRequestType5 = 8'b1_00_00010} bmrequesttype_e;

  typedef enum byte {bRequestGET_STATUS = 8'h00, bRequestCLEAR_FEATURE = 8'h01,
      bRequestSET_FEATURE = 8'h03, bRequestSET_ADDRESS = 8'h05, bRequestGET_DESCRIPTOR = 8'h06,
      bRequestSET_DESCRIPTOR = 8'h07, bRequestGET_CONFIGURATION = 8'h08,
      bRequestSET_CONFIGURATION = 8'h09, bRequestGET_INTERFACE = 8'h0A,
      bRequestSET_INTERFACE = 8'h0B, bRequestSYNCH_FRAME = 8'h0C} brequest_e;
  typedef enum bit [2:0] {CtrlTrans, IsoTrans, IntrptTrans, BulkTrans} usb_transfer_e;
  // local types
  // forward declare classes to allow typedefs below
  typedef class usb20_item;
  typedef class usb20_agent_cfg;

  // reuse dv_base_seqeuencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T     (usb20_item),
    .CFG_T      (usb20_agent_cfg)) usb20_sequencer;

  // functions

  // package sources
  `include "usb20_item.sv"
  `include "usb20_agent_cfg.sv"
  `include "usb20_agent_cov.sv"
  `include "usb20_driver.sv"
  `include "usb20_monitor.sv"
  `include "usb20_agent.sv"
  `include "usb20_seq_list.sv"

endpackage: usb20_agent_pkg
