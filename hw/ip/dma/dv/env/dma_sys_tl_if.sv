// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "dv_macros.svh"
`include "prim_assert.sv"

interface dma_sys_tl_if
  import dma_pkg::*;
  import tlul_pkg::*;
#(
  // Number of address bits used by the TL-UL agent.
  parameter int unsigned TLAddrWidth = 32
)
(
  input   clk_i,
  input   rst_ni
);
  // Base address of TL-UL agent (4GiB aligned for TLAddrWidth == 32; bottom 32 bits are unused.)
  logic [SYS_ADDR_WIDTH-1:0] base_addr;

  // Compute 'a_size' value for single word read/write on TL-UL.
  localparam int unsigned WordSize = $clog2(SYS_DATA_BYTEWIDTH);

  // Set the base address of the window mapping the TL-UL agent into the 64-bit address space.
  // Presently the agent is restricted to 32-bit addressing, so we map it to a 4GiB-aligned base
  // address, and check the upper 32 bits on each read/write access.
  function static void set_base_addr(logic [SYS_ADDR_WIDTH-1:0] base);
    // Note that when the adapter is not expected to be encountering traffic, the base address is
    // invalidated using all Xs.
    `DV_CHECK_FATAL(base === {SYS_ADDR_WIDTH{1'bX}} || base[31:0] === 0,
                    "Valid TL Agent base address must be 32-bit aligned", "dma_sys_tl_if");
    base_addr = base;
  endfunction

  // SoC System Bus host connection
  sys_req_t sys_h2d;
  sys_rsp_t sys_d2h;

  // TL-UL device connection
  tl_h2d_t tl_h2d;
  tl_d2h_t tl_d2h;

  // Arbitration of write and read requests
  tl_a_op_e                   h2d_opcode;
  logic [63:0]                h2d_address;
  logic [top_pkg::TL_DBW-1:0] h2d_mask;
  always_comb begin
    h2d_opcode  = Get;
    h2d_address = 'b0;
    h2d_mask    = 'b0;

    // Writes take predecence over reads.
    //
    // Not expected to handle simultaneous write and read requests with the current DMA
    // implementation and the behavior in this case has not been publicly specified.
    if (sys_h2d.vld_vec[SysCmdWrite]) begin
      // Write request
      h2d_opcode  = &sys_h2d.write_be ? PutFullData : PutPartialData;
      h2d_address = sys_h2d.iova_vec[SysCmdWrite];
      h2d_mask    = sys_h2d.write_be;
    end else if (sys_h2d.vld_vec[SysCmdRead]) begin
      // Read request
      h2d_address = sys_h2d.iova_vec[SysCmdRead];
      h2d_mask    = {SYS_DATA_BYTEWIDTH{1'b1}};
    end
  end

  // Check that the upper address bits (not visibile to the TL-UL agent) are driven to the correct
  // values by the host.
  // Address mismatches are reported immediately to the host and the request is not forwarded to
  // the TL-UL agent.
  wire addr_matches = (h2d_address >> TLAddrWidth) === (base_addr >> TLAddrWidth);
  wire h2d_a_valid  = addr_matches & |sys_h2d.vld_vec;
  // Writes take predecence over reads.
  wire write_mismatch =  sys_h2d.vld_vec[SysCmdWrite] & !addr_matches;
  wire read_mismatch  = !sys_h2d.vld_vec[SysCmdWrite] & sys_h2d.vld_vec[SysCmdRead] &
                        !addr_matches;

  assign tl_h2d = '{
    // Host->device address channel
    a_valid:   h2d_a_valid,
    a_opcode:  h2d_opcode,
    a_param:   3'b0,
    a_size:    top_pkg::TL_SZW'(WordSize),
    a_mask:    h2d_mask,
    a_source:  'b0,
    a_address: h2d_address[TLAddrWidth-1:0],
    // Host->device write data
    a_data:    sys_h2d.write_data,
    a_user:    'b0,
    // Ready to receive read data
    d_ready:   1'b1
  };

  always_comb begin
    sys_d2h = 'b0;
    // Read granted immediately, but host must wait for read response.
    sys_d2h.grant_vec[SysCmdRead]  = 1'b1;
    // Write does not receive a response; grant write only when TL-UL agent responds.
    sys_d2h.grant_vec[SysCmdWrite] = tl_d2h.d_valid & (tl_d2h.d_opcode == AccessAck)
                                   | write_mismatch;
    // Read response
    // Note: read errors are signaled by the simultaneous assertion of `read_data_vld` and
    //       `error_vld.`
    sys_d2h.read_data_vld          = (tl_d2h.d_valid & (tl_d2h.d_opcode == AccessAckData))
                                   | read_mismatch;
    sys_d2h.read_data              = tl_d2h.d_data;
    sys_d2h.error_vld              = (tl_d2h.d_valid & (tl_d2h.d_opcode == AccessAckData) &
                                      tl_d2h.d_error)
                                   | read_mismatch;
  end

`ifdef INC_ASSERT
  // Not expected to handle simultaneous write and read requests with the current DMA implementation
  // and the behavior in this case has not been publicly specified.
  `ASSERT_NEVER(DisjointReadAndWrite_A, sys_h2d.vld_vec[SysCmdWrite] & sys_h2d.vld_vec[SysCmdRead]);
`else
  // Not currently required; combinational logic only
  logic unused_clk = clk_i;
  logic unused_rst_n = rst_ni;
`endif
endinterface
