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

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 21 -n 9 \
  //     -s 2596398066 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||| (20.00%)
  //  4: |||||||||||||||||||| (31.43%)
  //  5: ||||||||||||||| (23.81%)
  //  6: ||||||||| (14.76%)
  //  7: |||| (7.62%)
  //  8: | (2.38%)
  //  9: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 8
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 7
  //
  typedef enum logic [8:0] {
    Idle              = 9'b011000001, // idle
    BootLoadIns       = 9'b111000111, // boot: load the instantiate command
    BootLoadGen       = 9'b001111001, // boot: load the generate command
    BootInsAckWait    = 9'b000000011, // boot: wait for instantiate command ack
    BootCaptGenCnt    = 9'b001110111, // boot: capture the gen fifo count
    BootSendGenCmd    = 9'b010101001, // boot: send the generate command
    BootGenAckWait    = 9'b011110000, // boot: wait for generate command ack
    BootPulse         = 9'b100110101, // boot: signal a done pulse
    BootDone          = 9'b000101100, // boot: stay in done state until reset
    BootLoadUni       = 9'b110111100, // boot: load the uninstantiate command
    BootUniAckWait    = 9'b110100011, // boot: wait for uninstantiate command ack
    AutoLoadIns       = 9'b010010010, // auto: load the instantiate command
    AutoFirstAckWait  = 9'b101100001, // auto: wait for first instantiate command ack
    AutoAckWait       = 9'b100001110, // auto: wait for instantiate command ack
    AutoDispatch      = 9'b111011101, // auto: determine next command to be sent
    AutoCaptGenCnt    = 9'b010111111, // auto: capture the gen fifo count
    AutoSendGenCmd    = 9'b001101010, // auto: send the generate command
    AutoCaptReseedCnt = 9'b010010101, // auto: capture the reseed fifo count
    AutoSendReseedCmd = 9'b000011000, // auto: send the reseed command
    SWPortMode        = 9'b101111110, // swport: no hw request mode
    Error             = 9'b001000100  // illegal state reached and hang
  } state_e;

endpackage : edn_pkg
