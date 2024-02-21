// Copyright lowRISC contributors.
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

  typedef enum bit [1:0] {
    TOKEN_PKT = 2'b10,
    DATA_PKT = 2'b00,
    HANDSHAKE_PKT = 2'b01
  } usbdev_pkt_type_e;

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
  `include "usbdev_scoreboard.sv"
  `include "usbdev_env.sv"
  `include "usbdev_vseq_list.sv"

endpackage
