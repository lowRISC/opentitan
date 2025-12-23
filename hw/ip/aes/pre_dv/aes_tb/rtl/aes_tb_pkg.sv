// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aes_tb_pkg;

  import tlul_pkg::*;
  import aes_pkg::*;
  import aes_reg_pkg::*;

  // AES register fields offsets.
  parameter int AES_CTRL_OPERATION_OFFSET        = 0;
  parameter int AES_CTRL_MODE_OFFSET             = 2;
  parameter int AES_CTRL_KEY_LEN_OFFSET          = 8;
  parameter int AES_CTRL_SIDELOAD_OFFSET         = 11;
  parameter int AES_CTRL_PRNG_RESEED_RATE_OFFSET = 12;
  parameter int AES_CTRL_MANUAL_OPERATION_OFFSET = 15;

  parameter int AES_CTRL_GCM_PHASE_OFFSET           = 0;
  parameter int AES_CTRL_GCM_NUM_VALID_BYTES_OFFSET = 6;

  parameter int AES_STATUS_IDLE_OFFSET         = 0;
  parameter int AES_STATUS_STALL_OFFSET        = 1;
  parameter int AES_STATUS_OUTPUT_LOST_OFFSET  = 2;
  parameter int AES_STATUS_OUTPUT_VALID_OFFSET = 3;
  parameter int AES_STATUS_INPUT_READY_OFFSET  = 4;

  parameter int AES_TRIGGER_START_OFFSET                = 0;
  parameter int AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_OFFSET = 1;
  parameter int AES_TRIGGER_DATA_OUT_CLEAR_OFFSET       = 2;
  parameter int AES_TRIGGER_PRNG_RESEED_OFFSET          = 3;

  // Caliptra register offsets
  parameter logic [11:0] CALIPTRA_NAME_0_OFFSET    = 12'h100;
  parameter logic [11:0] CALIPTRA_NAME_1_OFFSET    = 12'h104;
  parameter logic [11:0] CALIPTRA_VERSION_0_OFFSET = 12'h108;
  parameter logic [11:0] CALIPTRA_VERSION_1_OFFSET = 12'h10c;

  `include `REQUESTS_FILE

  // Grouping of all signals required for a `c_dpi` API call.
  typedef struct packed {
    aes_op_e operation;
    aes_mode_e mode;
    key_len_e key_length;

    logic [255:0] key;
    logic [127:0] iv;
    // Unfortunately, Verilator v4.210 does not allow unpacked arrays in structs, hence both AD and
    // data need to be unpacked later.
    logic [max(1, `AD_LENGTH)-1:0][7:0] ad;
    logic [max(1, `DATA_LENGTH)-1:0][7:0] data;
    logic [127:0] tag; // Only used in the GCM decryption case.
   } c_dpi_input_t;

  // Grouping of all signals required for a TLUL/shim read/write request and to instrument the
  // `c_dpi` API.
  typedef struct packed {
    logic write;
    logic [top_pkg::TL_AW-1:0] addr;
    logic [top_pkg::TL_DW-1:0] wdata;

    // Internal signal: The request is a `c_dpi` invocation instead of a TLUL/shim request.
    logic c_dpi_load;

    // Internal signal: To mask read request responses, e.g., to check whether a certain bit is set.
    logic [top_pkg::TL_DW-1:0] mask;

    // Internal signal: AD and PT inputs to the `c_dpi` model.
    c_dpi_input_t c_dpi_input;
  } bus_request_t;

  // write_request returns a filled out `bus_request_t` struct for a TLUL/shim write request.
  function automatic bus_request_t write_request (logic [7:0] addr,
                                                  logic [top_pkg::TL_DW-1:0] wdata);
    bus_request_t req = '{
      c_dpi_load: 1'b0,
      write: 1'b1,
      addr: {24'b0, addr},
      wdata: wdata,
      mask: '0,
      c_dpi_input: '0
    };
    return req;
  endfunction

  // read_request returns a filled out `bus_request_t` struct for a TLUL/shim read request.
  function automatic bus_request_t read_request (logic [7:0] addr,
                                                 logic [top_pkg::TL_DW-1:0] mask = '0);
    bus_request_t req = '{
      c_dpi_load: 1'b0,
      write: 1'b0,
      addr: {24'b0, addr},
      wdata: '0,
      mask: mask,
      c_dpi_input: '0
    };
    return req;
  endfunction

  // read_caliptra returns a filled out `bus_request_t` struct for an internal Caliptra register.
  // This is only useful if a TLUL-to-Shim adapter is configured otherwise the request will result
  // in a zero-value being returned by the register file.
  function automatic bus_request_t read_caliptra (logic [11:0] addr);
    bus_request_t req = '{
      c_dpi_load: 1'b0,
      write: 1'b0,
      addr: {20'b0, addr},
      wdata: '0,
      mask: '0,
      c_dpi_input: '0
    };
    return req;
  endfunction

  // c_dpi_load assigns a `c_dpi_input_t` to an empty `bus_request_t` struct. This type of
  // request is used to instrument the `c_dpi` API at the beginning of a test.
  function automatic bus_request_t c_dpi_load (c_dpi_input_t c_dpi_input);
    bus_request_t req = '{
      c_dpi_load: 1'b1,
      c_dpi_input: c_dpi_input,
      default: '0
    };
    return req;
  endfunction

  // Convenience helper function.
  function automatic int unsigned max (int unsigned a, int unsigned b);
    return (a > b) ? a : b;
  endfunction

  `REQUESTS

endpackage
