// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V Compliance Test helper module (simulation only)
 *
 * This module lets the RISC-V compliance test software interact with the
 * "outside world".
 *
 * It consists of a bus device and a bus host.
 *
 * Through the bus device, the software can interact with the outside world and
 * configure this module. The following registers are supported:
 * 0x0: read the signature and halt the execution
 * 0x4: set the signature start address
 * 0x8: set the signature end address
 *
 * When register 0x0 is written with an arbitrary value, the test signature is
 * read through the bus device, and written to STDOUT, prefixed with
 * "SIGNATURE: ".
 */
module riscv_testutil (
  input               clk_i,
  input               rst_ni,

  // bus device (slave) interface
  input               dev_req_i,
  input               dev_we_i,
  input        [31:0] dev_addr_i,
  input        [31:0] dev_wdata_i,
  input        [ 3:0] dev_be_i,

  output logic        dev_rvalid_o,
  output logic [31:0] dev_rdata_o,
  output logic        dev_err_o,

  // bus host (master) interface
  output logic        host_req_o,
  input               host_gnt_i,
  input               host_rvalid_i,
  output logic [31:0] host_addr_o,
  input        [31:0] host_rdata_i
);
  // ======= Bus device for interaction with software ======= //

  localparam ADDR_HALT = 0;
  localparam ADDR_SET_BEGIN_SIGNATURE = 4;
  localparam ADDR_SET_END_SIGNATURE = 8;

  // 1 kB address space for this peripheral
  logic [21:0] unused_addr;
  assign unused_addr = dev_addr_i[31:10];

  logic [31:0] begin_signature_addr_d, begin_signature_addr_q;
  logic [31:0] end_signature_addr_d, end_signature_addr_q;

  logic read_signature_and_terminate;
  always_comb begin
    read_signature_and_terminate = 1'b0;
    begin_signature_addr_d = begin_signature_addr_q;
    end_signature_addr_d = end_signature_addr_q;

    if (dev_we_i && dev_req_i) begin
      case (dev_addr_i[9:0])
        ADDR_HALT: begin
          read_signature_and_terminate = 1'b1;
        end
        ADDR_SET_BEGIN_SIGNATURE: begin
          begin_signature_addr_d = dev_wdata_i;
        end
        ADDR_SET_END_SIGNATURE: begin
          end_signature_addr_d = dev_wdata_i;
        end
        default: ;
      endcase
    end
  end

  always_ff @(posedge clk_i) begin
    begin_signature_addr_q <= begin_signature_addr_d;
    end_signature_addr_q <= end_signature_addr_d;
  end

  // all responses are in the next cycle
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dev_rvalid_o <= 1'b0;
    end else begin
      dev_rvalid_o <= dev_req_i;
    end
  end

  // The interface is write-only, and only supports 32-bit writes. If
  // either of these checks fails, raise dev_err_o on the next cycle.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      dev_err_o <= 1'b0;
    end else begin
      dev_err_o <= (~dev_we_i | dev_be_i != 4'hf) & dev_req_i;
    end
  end

  // Since the interface is write-only, tie rdata to 0.
  assign dev_rdata_o = 32'h0;


  // ======= FSM: Read signature from memory and dump it to STDOUT ======= //

  typedef enum logic [1:0] {
    WAIT, READ, READ_FINISH, TERMINATE
  } readsig_state_e;

  readsig_state_e state_q, state_d;

  logic [31:0] read_addr_d, read_addr_q;
  always_comb begin
    state_d = state_q;
    read_addr_d = read_addr_q;
    unique case (state_q)
      WAIT: begin
        if (read_signature_and_terminate) begin
          $display("Reading signature from 0x%x to 0x%x",
              begin_signature_addr_q, end_signature_addr_q);
          state_d = READ;
          read_addr_d = begin_signature_addr_q;
        end
      end

      READ: begin
        if (host_gnt_i) begin
          read_addr_d = read_addr_q + 4;
          if (read_addr_d == end_signature_addr_q) begin
            state_d = READ_FINISH;
          end
        end
      end

      READ_FINISH: begin
        if (host_rvalid_i) begin
          state_d = TERMINATE;
        end
      end

      TERMINATE: begin
        $display("Terminating simulation by software request.");
        $finish;
      end

      default: ;
    endcase
  end

  // These are the address and read request bits, respectively of the
  // TestUtilHost master port.
  assign host_addr_o = read_addr_q;
  assign host_req_o = (state_q == READ);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      state_q <= WAIT;
      read_addr_q <= 0;
    end else begin
      state_q <= state_d;
      read_addr_q <= read_addr_d;

      if (host_rvalid_i) begin
        $display("SIGNATURE: 0x%x", host_rdata_i);
      end
    end
  end
endmodule
