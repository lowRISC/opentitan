// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "dv_macros.svh"
`include "prim_assert.sv"

// Since there is no proper model of the SoC System Bus and attached devices presently, this
// interface permits them to be connected to the existing TL-UL components within the OpenTitan
// project.
//
// A further complication is that they are presently restricted to 32-bit addressing, but the
// SoC System Bus has a 64-bit address space. We resolve this by presenting a 4GiB addressing
// window on the SoC System Bus and programming a base address from the DV environment.
// Since the DUT itself only supports transfers of less than 4GiB this provides completes testing.
//
// For additional verification we permit the TL-UL memory model to be mapped at different
// base addresses for the Read and Write sides of the DUT.

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
  // Base address of TL-UL agent (4B aligned for TLAddrWidth == 32; bottom 2 bits are unused),
  // for each of the command types in turn.
  logic [SYS_ADDR_WIDTH-1:0] base_addr[SYS_NUM_REQ_CH];
  // Last valid word-aligned address within the window; derived from the base address.
  logic [SYS_ADDR_WIDTH-1:0] end_addr[SYS_NUM_REQ_CH];

  // Compute 'a_size' value for single word read/write on TL-UL.
  localparam int unsigned WordSize = $clog2(SYS_DATA_BYTEWIDTH);

  // Set the base address of the window mapping the TL-UL agent into the 64-bit address space.
  // Presently the agent is restricted to 32-bit addressing, so we map it to a 4GiB-aligned base
  // address, and check the upper 32 bits on each read/write access.
  function static void set_base_addr(sys_cmd_type_e cmd, logic [SYS_ADDR_WIDTH-1:0] base);
    // Note that when the adapter is not expected to be encountering traffic, the base address is
    // invalidated using all Xs.
    `DV_CHECK_FATAL(base === {SYS_ADDR_WIDTH{1'bX}} || base[1:0] === 0,
                    "Valid TL Agent base address must be 32-bit aligned", "dma_sys_tl_if");
    // Check that we have space for a full 4GiB address window.
    `DV_CHECK_FATAL(base === {SYS_ADDR_WIDTH{1'bX}} ||
                    {SYS_ADDR_WIDTH{1'b1}} - 32'hFFFF_FFFF >= base,
                    "Base address is too high", "dma_sys_tl_if");
    base_addr[cmd] = base;
    end_addr[cmd] = base + SYS_ADDR_WIDTH'(32'hFFFF_FFFC);  // inclusive, word-aligned.
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
  sys_cmd_type_e              h2d_cmd;
  always_comb begin
    h2d_opcode  = Get;
    h2d_address = 'b0;
    h2d_mask    = 'b0;
    // Default to selecting the read addresses; they will not be used unless `vld_vec` asserted.
    h2d_cmd     = SysCmdRead;

    // Writes take precedence over reads.
    //
    // Not expected to handle simultaneous write and read requests with the current DMA
    // implementation and the behavior in this case has not been publicly specified.
    if (sys_h2d.vld_vec[SysCmdWrite]) begin
      // Write request
      h2d_opcode  = &sys_h2d.write_be ? PutFullData : PutPartialData;
      h2d_address = sys_h2d.iova_vec[SysCmdWrite];
      h2d_mask    = sys_h2d.write_be;
      h2d_cmd     = SysCmdWrite;
    end else if (sys_h2d.vld_vec[SysCmdRead]) begin
      // Read request
      h2d_address = sys_h2d.iova_vec[SysCmdRead];
      h2d_mask    = {SYS_DATA_BYTEWIDTH{1'b1}};
    end
  end

  // Check that the upper address bits (not visible to the TL-UL agent) are driven to the correct
  // values by the host.
  // Address mismatches are reported immediately to the host and the request is not forwarded to
  // the TL-UL agent.
  wire addr_matches = (h2d_address >= base_addr[h2d_cmd] && h2d_address <= end_addr[h2d_cmd]);
  wire h2d_a_valid  = addr_matches & |sys_h2d.vld_vec;
  // Writes take precedence over reads.
  wire write_mismatch =  sys_h2d.vld_vec[SysCmdWrite] & !addr_matches;
  wire read_mismatch  = !sys_h2d.vld_vec[SysCmdWrite] & sys_h2d.vld_vec[SysCmdRead] &
                        !addr_matches;

  // Calculate the TL-UL address by performing an arbitrary subtraction; this just makes the
  // verification a bit more thorough than a bitfield-base approach like BAT.
  wire [TLAddrWidth-1:0] tlul_address = (h2d_address - base_addr[h2d_cmd]);

  assign tl_h2d = '{
    // Host->device address channel
    a_valid:   h2d_a_valid,
    a_opcode:  h2d_opcode,
    a_param:   3'b0,
    a_size:    top_pkg::TL_SZW'(WordSize),
    a_mask:    h2d_mask,
    a_source:  'b0,
    a_address: tlul_address,
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
    sys_d2h.error_vld              = (tl_d2h.d_valid & tl_d2h.d_error) | read_mismatch;
  end

`ifdef INC_ASSERT
  // Not expected to handle simultaneous write and read requests with the current DMA implementation
  // and the behavior in this case has not been publicly specified.
  `ASSERT_NEVER(DisjointReadAndWrite_A, sys_h2d.vld_vec[SysCmdWrite] & sys_h2d.vld_vec[SysCmdRead])
`else
  // Not currently required; combinational logic only
  logic unused_clk = clk_i;
  logic unused_rst_n = rst_ni;
`endif
endinterface
