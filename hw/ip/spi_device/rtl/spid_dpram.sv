// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SPI Device dual-port RAM emulation
//
// This module implements the SPI device "dual-port" RAM's interface using 1r1w
// memories. The memory selection for requests depends on the incoming address.
// The sys port read data always completes, so bad addresses don't prevent
// transaction completion. However, the sys port writes do check addresses.
//
// SPI ports don't check addresses, as the behavior is fixed in hardware.

module spid_dpram
  import prim_ram_2p_pkg::*;
  import spi_device_pkg::*;
#(
  parameter  sram_type_e SramType     = DefaultSramType,
  parameter  bit EnableECC            = 0,
  parameter  bit EnableParity         = 0,
  parameter  bit EnableInputPipeline  = 0,
  parameter  bit EnableOutputPipeline = 0  // Adds an output register (read latency +1)
) (
  input                      clk_sys_i,
  input                      rst_sys_ni,

  input                      clk_spi_i,
  input                      rst_spi_ni,

  input                      sys_req_i,
  input                      sys_write_i,
  input        [SramAw-1:0]  sys_addr_i,
  input        [SramDw-1:0]  sys_wdata_i,
  input        [SramDw-1:0]  sys_wmask_i,
  output logic               sys_rvalid_o,
  output logic [SramDw-1:0]  sys_rdata_o,
  output logic [1:0]         sys_rerror_o,

  input                      spi_req_i,
  input                      spi_write_i,
  input        [SramAw-1:0]  spi_addr_i,
  input        [SramDw-1:0]  spi_wdata_i,
  input        [SramDw-1:0]  spi_wmask_i,
  output logic               spi_rvalid_o,
  output logic [SramDw-1:0]  spi_rdata_o,
  output logic [1:0]         spi_rerror_o,

  // When using a dual port RAM primitive only this RAM config port is used
  input  ram_2p_cfg_t        cfg_sys2spi_i,
  output ram_2p_cfg_rsp_t    cfg_rsp_sys2spi_o,
  // When using a 1R1W RAM primitive, both RAM config ports are used
  input  ram_2p_cfg_t        cfg_spi2sys_i,
  output ram_2p_cfg_rsp_t    cfg_rsp_spi2sys_o
);

  // SYS Wr, SPI Rd is for eFlash, Mailbox, and SFDP
  localparam sram_addr_t     Sys2SpiOffset   = SramEgressIdx;
  localparam int unsigned    Sys2SpiMinDepth = SramMsgDepth + SramMailboxDepth
                                               + SramSfdpDepth + SramTpmRdFifoDepth;
  localparam int unsigned    Sys2SpiAw       = $clog2(Sys2SpiMinDepth);
  localparam int unsigned    Sys2SpiDepth    = 1 << Sys2SpiAw;
  localparam sram_addr_t     Sys2SpiEnd      = SramReadBufferIdx + sram_addr_t'(Sys2SpiMinDepth);

  // SYS writes only the Sys2Spi memory.
  // Only allow software to write to the write-only locations. Filter by
  // address.
  logic sys2spi_wr_req;
  sram_addr_t sys2spi_wr_addr;
  assign sys2spi_wr_req = (sys_addr_i < Sys2SpiEnd) & sys_req_i & sys_write_i;
  assign sys2spi_wr_addr = sys_addr_i - Sys2SpiOffset;

  // SPI reads from only the Sys2Spi memory.
  logic sys2spi_rd_req;
  sram_addr_t sys2spi_rd_addr;
  assign sys2spi_rd_req = spi_req_i & !spi_write_i;
  assign sys2spi_rd_addr = spi_addr_i - Sys2SpiOffset;

  // SPI Wr, SYS Rd is for payload upload
  localparam sram_addr_t  Spi2SysOffset   = SramIngressIdx;
  localparam int unsigned Spi2SysMinDepth = SramPayloadDepth + SramCmdFifoDepth
                                            + SramAddrFifoDepth + SramTpmWrFifoDepth;
  localparam int unsigned Spi2SysAw       = $clog2(Spi2SysMinDepth);
  localparam int unsigned Spi2SysDepth    = 1 << Spi2SysAw;

  // SPI writes to only the Spi2Sys memory.
  logic spi2sys_wr_req;
  sram_addr_t spi2sys_wr_addr;
  assign spi2sys_wr_req = spi_req_i & spi_write_i;
  assign spi2sys_wr_addr = spi_addr_i - Spi2SysOffset;

  // SYS reads only read from the Spi2Sys memory.
  // Allow all reads to complete, so the bus always gets a response, even if
  // software chooses to read from write-only addresses.
  logic spi2sys_rd_req;
  sram_addr_t spi2sys_rd_addr;
  assign spi2sys_rd_req = sys_req_i & !sys_write_i;
  assign spi2sys_rd_addr = sys_addr_i - Spi2SysOffset;

  // The SPI -> core buffer for the payload uses parity and SW has no way of initializing it since
  // the write port is in the SPI domain. Since the SPI side writes the payload byte by byte,
  // we need to guard against partially initialized 32bit words, because these could cause TL-UL
  // bus errors upon readout. Unfortunately, an initialization circuit that initializes the entire
  // SRAM on the SPI clock domain is infeasible since that clock is only intermittently available.
  // Hence, we keep track of uninitialized words using a valid bit array, and upon the first write
  // to a word, uninitialized bytes are set to zero if the write operation is a sub-word write op.
  logic [SramDw-1:0] spi_wdata, spi_wmask;
  logic [Spi2SysDepth-1:0] initialized_words_d, initialized_words_q;
  always_comb begin initialized_words_d = initialized_words_q;
    // By default, we just loop through the data and wmask.
    spi_wdata = spi_wdata_i;
    spi_wmask = spi_wmask_i;
    // If the word has not been initialized yet we modify the data and wmask to initialize all bits.
    if (spi2sys_wr_req && !initialized_words_q[Spi2SysAw'(spi2sys_wr_addr)]) begin
      // Mask data at this point already and set all masked bits to 0.
      spi_wdata = spi_wdata_i & spi_wmask_i;
      spi_wmask = {SramDw{1'b1}};
      // Mark this word as initialized
      initialized_words_d[Spi2SysAw'(spi2sys_wr_addr)] = 1'b1;
    end
  end

  always_ff @(posedge clk_spi_i or negedge rst_spi_ni) begin : p_spi_regs
    if (!rst_spi_ni) begin
      initialized_words_q <= '0;
    end else begin
      initialized_words_q <= initialized_words_d;
    end
  end

  if (SramType == SramType2p) begin : gen_ram2p
    prim_ram_2p_async_adv #(
      .Depth (SramDepth),
      .Width (SramDw),    // 32 x 512 --> 2kB
      .DataBitsPerMask (8),

      .EnableECC           (0),
      .EnableParity        (1),
      .EnableInputPipeline (0),
      .EnableOutputPipeline(0)
    ) u_memory_2p (
      .clk_a_i    (clk_sys_i),
      .rst_a_ni   (rst_sys_ni),

      .clk_b_i    (clk_spi_i),
      .rst_b_ni   (rst_spi_ni),

      .a_req_i    (sys_req_i),
      .a_write_i  (sys_write_i),
      .a_addr_i   (sys_addr_i),
      .a_wdata_i  (sys_wdata_i),
      .a_wmask_i  (sys_wmask_i),
      .a_rvalid_o (sys_rvalid_o),
      .a_rdata_o  (sys_rdata_o),
      .a_rerror_o (sys_rerror_o),

      .b_req_i    (spi_req_i),
      .b_write_i  (spi_write_i),
      .b_addr_i   (spi_addr_i),
      // Use modified wdata and wmask
      .b_wdata_i  (spi_wdata),
      .b_wmask_i  (spi_wmask),
      .b_rvalid_o (spi_rvalid_o),
      .b_rdata_o  (spi_rdata_o),
      .b_rerror_o (spi_rerror_o),

      .cfg_i      (cfg_sys2spi_i),
      .cfg_rsp_o  (cfg_rsp_sys2spi_o)
    );

    logic sys2spi_unused;
    assign sys2spi_unused = ^{
      sys2spi_wr_req,
      sys2spi_wr_addr,
      sys2spi_rd_req,
      sys2spi_rd_addr
    };

    logic spi2sys_unused;
    assign spi2sys_unused = ^{
      spi2sys_wr_req,
      spi2sys_wr_addr,
      spi2sys_rd_req,
      spi2sys_rd_addr,
      cfg_spi2sys_i
    };
    assign cfg_rsp_spi2sys_o = '0;
  end else if (SramType == SramType1r1w) begin : gen_ram1r1w
    prim_ram_1r1w_async_adv #(
      .Depth                     (Sys2SpiDepth),
      .Width                     (SramDw),
      .DataBitsPerMask           (8),

      .EnableECC                 (EnableECC),
      .EnableParity              (EnableParity),
      .EnableInputPipeline       (EnableInputPipeline),
      .EnableOutputPipeline      (EnableOutputPipeline)
    ) u_sys2spi_mem (
      .clk_a_i                   (clk_sys_i),
      .clk_b_i                   (clk_spi_i),
      .rst_a_ni                  (rst_sys_ni),
      .rst_b_ni                  (rst_spi_ni),
      .a_req_i                   (sys2spi_wr_req),
      .a_addr_i                  (Sys2SpiAw'(sys2spi_wr_addr)),
      .a_wdata_i                 (sys_wdata_i),
      .a_wmask_i                 (sys_wmask_i),

      .b_req_i                   (sys2spi_rd_req),
      .b_addr_i                  (Sys2SpiAw'(sys2spi_rd_addr)),
      .b_rdata_o                 (spi_rdata_o),
      .b_rvalid_o                (spi_rvalid_o),
      .b_rerror_o                (spi_rerror_o),

      .cfg_i                     (cfg_sys2spi_i),
      .cfg_rsp_o                 (cfg_rsp_sys2spi_o)
    );

    prim_ram_1r1w_async_adv #(
      .Depth                     (Spi2SysDepth),
      .Width                     (SramDw),
      .DataBitsPerMask           (8),

      .EnableECC                 (EnableECC),
      .EnableParity              (EnableParity),
      .EnableInputPipeline       (EnableInputPipeline),
      .EnableOutputPipeline      (EnableOutputPipeline)
    ) u_spi2sys_mem (
      .clk_a_i                   (clk_spi_i),
      .clk_b_i                   (clk_sys_i),
      .rst_a_ni                  (rst_spi_ni),
      .rst_b_ni                  (rst_sys_ni),
      .a_req_i                   (spi2sys_wr_req),
      .a_addr_i                  (Spi2SysAw'(spi2sys_wr_addr)),
      // Use modified wdata and mask.
      .a_wdata_i                 (spi_wdata),
      .a_wmask_i                 (spi_wmask),

      .b_req_i                   (spi2sys_rd_req),
      .b_addr_i                  (Spi2SysAw'(spi2sys_rd_addr)),
      .b_rdata_o                 (sys_rdata_o),
      .b_rvalid_o                (sys_rvalid_o),
      .b_rerror_o                (sys_rerror_o),

      .cfg_i                     (cfg_spi2sys_i),
      .cfg_rsp_o                 (cfg_rsp_spi2sys_o)
    );
  end

endmodule  // spid_dpram
