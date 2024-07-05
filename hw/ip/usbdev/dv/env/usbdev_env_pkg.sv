// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package usbdev_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import usb20_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import usbdev_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // Number of Endpoints (in each direction) supported by the USB device
  parameter uint NEndpoints       = usbdev_reg_pkg::NEndpoints;
  // Maximum supported packet size, in bytes.
  parameter uint MaxPktSizeByte   = 64;
  // Number of packet buffers available within the USB device
  parameter uint NumBuffers       = 32;
  // FIFO Depths; number of entries
  parameter uint AvOutFIFODepth   = 8;
  parameter uint AvSetupFIFODepth = 4;
  parameter uint RxFIFODepth      = 8;

  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  // types
  typedef enum {
    IntrPktReceived = 0,
    IntrPktSent = 1,
    IntrDisconnected = 2,
    IntrHostLost = 3,
    IntrLinkReset = 4,
    IntrLinkSuspend = 5,
    IntrLinkResume = 6,
    IntrAvOutEmpty = 7,
    IntrRxFull = 8,
    IntrAvOverflow = 9,
    IntrLinkInErr = 10,
    IntrRxCrcErr = 11,
    IntrRxPidErr = 12,
    IntrRxBitstuffErr = 13,
    IntrFrame = 14,
    IntrPowered = 15,
    IntrLinkOutErr = 16,
    IntrAvSetupEmpty = 17,
    NumUsbdevInterrupts
  } usbdev_intr_e;

  typedef enum bit [1:0] {
    ACK = 0,
    NAK = 1,
    STALL = 2
  } usbdev_handshake_pkt_e;

  // The two LSBs of the PID identify the PID Type
  typedef enum bit [1:0] {
    TOKEN_PKT = 2'b01,
    DATA_PKT = 2'b11,
    HANDSHAKE_PKT = 2'b10
  } usbdev_pkt_type_e;

  // Link State
  // TODO: make this available in a DUT package file and import here.
  typedef enum logic [2:0] {
    // No power and/or no pull-up connected state
    LinkDisconnected = 0,
    // Powered / connected states
    LinkPowered = 1,
    LinkPoweredSuspended = 2,
    // Active states
    LinkActiveNoSOF = 5,
    LinkActive = 3,
    LinkSuspended = 4,
    LinkResuming = 6
  } usbdev_link_state_e;

  // functions

  // package sources
  `include "usbdev_env_cfg.sv"
  `include "usbdev_env_cov.sv"
  `include "usbdev_virtual_sequencer.sv"
  `include "usbdev_packetiser.sv"
  `include "usbdev_packet_classifier.sv"
  `include "usbdev_data_integrity.sv"
  `include "usbdev_pkt_manager.sv"
  `include "usbdev_TransactionManager.sv"
  `include "usbdev_bfm.sv"
  `include "timed_reg.sv"
  `include "usbdev_timed_regs.sv"
  `include "usbdev_scoreboard.sv"
  `include "usbdev_env.sv"
  `include "usbdev_vseq_list.sv"

endpackage
