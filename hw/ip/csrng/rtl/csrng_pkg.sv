// Copyright lowRISC contributors.
// Licensed under the Apache License; Version 2.0; see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//


package csrng_pkg;

  //-------------------------
  // Application Interfaces
  //-------------------------

  // instantiation interface
  typedef struct packed {
    logic         csrng_req_vld;
    logic [31:0]  csrng_req_bus;
    logic         genbits_rdy;
  } csrng_req_t;

  // default value of csrng_req_t (for dangling ports)
  parameter csrng_req_t CSRNG_REQ_DEFAULT = '{
    csrng_req_vld: 1'b0,
    csrng_req_bus:   '0,
    genbits_rdy:   1'b0 
  };


  typedef struct packed {
    logic         csrng_req_rdy;
    logic         csrng_rsp_ack;
    logic [1:0]   csrng_rsp_sts;
    logic         genbits_vld;
    logic [127:0] genbits_bus;
  } csrng_rsp_t;

  // default value of csrng_rsp_t (for dangling ports)
  parameter csrng_rsp_t CSRNG_RSP_DEFAULT = '{
    csrng_req_rdy: 1'b0,
    csrng_rsp_ack: 1'b0,
    csrng_rsp_sts: 2'b0,
    genbits_vld:   1'b0,
    genbits_bus:     '0 
  };



  // general command form
  //
  // 31          24          15            7             0
  // +-----------+-----------+------+------+------+------+
  // +     count_request     | flgs | xcnt | shid | acmd |
  // +-----------+-----------+------+------+------+------+

  // field description
  // acmd: application command
  //   bits 2-0: 0x0 - instantiate
  //             0x1 - reseed
  //             0x2 - generate
  //             0x3 - update
  //             0x4 - uninstantiate
  //   bit    3: reserved
  //
  //
  // shid: state handle identifier
  //   bits 7-4: supports up to 16 instances (1 sw, 1-15 hw)
  //   determined by the csrng module parameter
  //
  //
  // xcnt: transfer count
  //   bits 11-8: holds the number of 32 bit words to transfer that
  //              immediately follow the command. A value of zero
  //              indicates a command only.
  //
  //
  // flgs: general flags
  //   bits 15-12: flags that are unique per command.
  //
  //
  //
  // count_request: generate request count value
  //   bits 31-16: holds the number of 128 bit words to be returned
  //               on the genbits bus for this command.
  //
  //
  // example commands
  //   instantiate:
  //   acmd: 0x0 (encoded command)
  //   shid: 0x3 (choose one of 16 states)
  //   xcnt: 0xc (12 words of seed)
  //   flgs: 0x1 (bit 12 set is full deterministic mode)
  //   full_deterministic_mode: if set, use only app seed, otherwise
  //   use entropy and app seed as personalization string
  //
  //   reseed:
  //   acmd: 0x1 (encoded command)
  //   shid: 0x3 (choose one of 16 states)
  //   xcnt: 0x0 (no following words)
  //   flgs: 0x0 (no special flags)
  //
  //   generate:
  //   acmd: 0x2 (encoded command)
  //   shid: 0x3 (choose one of 16 states)
  //   xcnt: 0x0 (no following words)
  //   flgs: 0x1 (bit 12 set is prediction resistance flag)
  //
  //   update:
  //   acmd: 0x3 (encoded command)
  //   shid: 0x3 (choose one of 16 states)
  //   xcnt: 0x4 (4 words of additional data)
  //   flgs: 0x0 (no special flags)
  //
  //   uninstantiate:
  //   acmd: 0x4 (encoded command)
  //   shid: 0x3 (choose one of 16 states)
  //   xcnt: 0x0 (no following words)
  //   flgs: 0x0 (no special flags)


  // ack status definition
  // 0b00 - request is pending
  // 0b01 - request final status and ok
  // 0b10 - request intermediary status and ok
  // 0b11 - request has an error detected


  // example waveform

  //{signal: [
  //   {name: 'clk'            , wave: 'p.............|............'},
  //   {name: 'csrng_req_vld'  , wave: '010...........|.10|........'},
  //   {name: 'csrng_req_rdy'  , wave: '1.............|...|........'},
  //   {name: 'csrng_req_bus'  , wave: 'x53..........x|.5x|........',
  // data: ['ins','seed 0-11','gen','es3','es4','es5','es6','es7']},
  //   {name: 'csrng_rsp_ack'  , wave: '0.............|10.|.1......'},
  //   {name: 'csrng_rsp_sts'  , wave: 'x.............|5x.|.5555555',
  //  data: ['sts','sts','sts','sts','sts','sts','sts','sts']},
  //   {name: 'genbits_vld'    , wave: '0.............|...|.1......'},
  //   {name: 'genbits_bus'    , wave: 'x.............|...|.4444444',
  //  data: ['bits','bits','bits','bits','bits','bits','bits','bits']},
  // {},
  //]}



endpackage : csrng_pkg