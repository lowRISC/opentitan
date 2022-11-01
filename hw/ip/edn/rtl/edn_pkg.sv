// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//


package edn_pkg;
  ///////////////////////////
  // Peripheral Interfaces //
  ///////////////////////////

  parameter int unsigned   ENDPOINT_BUS_WIDTH = 32;
  parameter int unsigned   FIPS_ENDPOINT_BUS_WIDTH = entropy_src_pkg::FIPS_BUS_WIDTH +
                           ENDPOINT_BUS_WIDTH;

  // EDN request interface
  typedef struct packed {
    logic                                 edn_req;
  } edn_req_t;
  typedef struct packed {
    logic                                 edn_ack;
    logic                                 edn_fips;
    logic [ENDPOINT_BUS_WIDTH-1:0]        edn_bus;
  } edn_rsp_t;

  parameter edn_req_t EDN_REQ_DEFAULT = '0;
  parameter edn_rsp_t EDN_RSP_DEFAULT = '0;

  typedef enum logic [8:0] {
    Idle              = 9'b110000101, // idle
    BootLoadIns       = 9'b110110111, // boot: load the instantiate command
    BootLoadGen       = 9'b000000011, // boot: load the generate command
    BootInsAckWait    = 9'b011010010, // boot: wait for instantiate command ack
    BootCaptGenCnt    = 9'b010111010, // boot: capture the gen fifo count
    BootSendGenCmd    = 9'b011100100, // boot: send the generate command
    BootGenAckWait    = 9'b101101100, // boot: wait for generate command ack
    BootPulse         = 9'b100001010, // boot: signal a done pulse
    BootDone          = 9'b011011111, // boot: stay in done state until reset
    AutoLoadIns       = 9'b001110000, // auto: load the instantiate command
    AutoFirstAckWait  = 9'b001001101, // auto: wait for first instantiate command ack
    AutoAckWait       = 9'b101100011, // auto: wait for instantiate command ack
    AutoDispatch      = 9'b110101110, // auto: determine next command to be sent
    AutoCaptGenCnt    = 9'b000110101, // auto: capture the gen fifo count
    AutoSendGenCmd    = 9'b111111000, // auto: send the generate command
    AutoCaptReseedCnt = 9'b000100110, // auto: capture the reseed fifo count
    AutoSendReseedCmd = 9'b101010110, // auto: send the reseed command
    SWPortMode        = 9'b100111001, // swport: no hw request mode
    Error             = 9'b010010001  // illegal state reached and hang
  } state_e;

endpackage : edn_pkg
