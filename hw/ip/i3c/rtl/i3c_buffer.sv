// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// I3C buffer
//
// - This buffer implements a number of independent FIFOs as circular buffers
//   within a single shared memory.
// - Each FIFO is written by either (i) the processor, or (ii) the IP block hardware,
//   and read by the other party.
// - The size of each FIFO may be configured by software at start up, to adapt to
//   different use cases and traffic expectations.
// - Arbitration occurs amongst those requests, with accesses performed by the IP block hardware
//   being treated as higher priority than processor accesses, oweing to the hard real-time nature
//   of the I3C traffic.
// - The direction of each FIFO is specified, so that hardware access may be prioritized.

module i3c_buffer
  import i3c_pkg::*;
  import i3c_fifo_pkg::*;
  import prim_ram_1p_pkg::*;
#(
  parameter int unsigned BufAddrW = 9,
  parameter int unsigned DataWidth = 32,
  parameter int unsigned NumFifos = 7,
  // Indicates, for each FIFO in turn, whether the FIFO is used to transmit data over the I3C.
  // - Tx FIFOs shall prioritize read prefetching over software writes into the FIFO.
  parameter bit [NumFifos-1:0] DirTx = 0
) (
  input                     clk_i,
  input                     rst_ni,
  // Synchronous FIFO resets.
  input                     sw_reset_i[NumFifos],
  // FIFO configuration.
  input  fifo_config_t      cfg_i[NumFifos],
  // FIFO input signals.
  input  fifo_in_t          in_i[NumFifos],
  // FIFO output signals.
  output fifo_out_t         out_o[NumFifos],
  // Current FIFO state.
  output fifo_state_t       state_o[NumFifos],

  // Direct software interface to buffer.
  input                     sw_buf_req_i,
  output                    sw_buf_gnt_o,
  input                     sw_buf_we_i,
  input      [BufAddrW-1:0] sw_buf_addr_i,
  input     [DataWidth-1:0] sw_buf_wdata_i,
  output                    sw_buf_rvalid_o,
  output              [1:0] sw_buf_rerror_o,
  output    [DataWidth-1:0] sw_buf_rdata_o,

  // DFT-related signals.
  input  ram_1p_cfg_t       ram_cfg_i,
  output ram_1p_cfg_rsp_t   ram_cfg_rsp_o
);

  // Use the arbiter to steer the appropriate inputs.
  typedef struct packed {
    logic                 write;
    logic  [BufAddrW-1:0] addr;
    logic [DataWidth-1:0] wdata;
    // FIFO configuration used in address updating.
    logic  [BufAddrW-1:0] min;
    logic  [BufAddrW-1:0] max;
  } arb_data_t;
  localparam int unsigned ArbDataWidth = $bits(arb_data_t);

  // Arbitration and granting also includes the `sw_buf` direct access at the MSB (lowest priority).
  localparam int unsigned N = 1 + NumFifos;
  localparam int unsigned IdxW = $clog2(N);

  // Arbiter request inputs and grant outputs.
  logic [NumFifos:0] req, gnt;
  // Arbiter input data.
  arb_data_t arb[N];

  // Memory outputs.
  logic                 mem_rvalid;
  logic      [IdxW-1:0] mem_ridx;
  logic           [1:0] mem_rerror;
  logic [DataWidth-1:0] mem_rdata;

  // Direct software access to the entire message buffer.
  // - this may be useful diagnostically or for supporting a lower-level protocol; the parent
  //   logic may strip out this access path by tying the inputs low.
  always_comb begin
    req[NumFifos]       = sw_buf_req_i;
    arb[NumFifos].write = sw_buf_we_i;
    arb[NumFifos].min   = '0;
    arb[NumFifos].max   = '1;
    arb[NumFifos].addr  = sw_buf_addr_i;
    arb[NumFifos].wdata = sw_buf_wdata_i;
  end
  assign sw_buf_gnt_o    = gnt[NumFifos];
  assign sw_buf_rvalid_o = mem_rvalid & (IdxW'(NumFifos) == mem_ridx);
  assign sw_buf_rdata_o  = mem_rdata;
  assign sw_buf_rerror_o = mem_rerror;

  // A single read/write request may be performed to the message buffer per clock cycle; a single
  // incrementer and multiplexer are required to update FIFO state.
  logic [BufAddrW-1:0] next_addr;

  for (genvar f = 0; f < NumFifos; f++) begin : gen_fifos
    // Prefetched read data; a single word of read data may be held here, without removing it from
    // the FIFO yet. The FIFO status is unaffected by whether or not data has been prefetched.
    logic                 pre_rvalid;
    logic [DataWidth-1:0] pre_rdata;

    // Current state of the FIFO.
    logic [BufAddrW-1:0] wptr;  // Write pointer.
    logic [BufAddrW-1:0] pptr;  // Prefetching pointer.
    logic [BufAddrW-1:0] rptr;  // Read pointer; lags prefetching pointer by one word, at times.
    logic full, empty;
    logic wreq, preq, wgnt, pgnt;
    logic we, pe;
    assign empty = (wptr == rptr) & !full;

    // Calculate the number of used entries and the number of entries still available.
    // - there are 3 pointers into the message buffer for each FIFO implementation:
    //   - write pointer indicates where the next write shall occur.
    //   - prefetch pointer indicates the next word to be prefetched from the buffer.
    //   - read pointer indicates the next word to be consumed by the _external_ logic.
    // - the external interface (`used`, `avail`, `free` and `empty) are in terms of the
    //   read and write pointers, thus hiding the fact that prefetching may have occurred.
    //   This ensures that the `used` and `avail` values remain within the expected dimensions
    //   of the logical FIFO and avoid confusion. Even though - physically - it would be possible
    //   to store 'depth + 1' words of data now, this would not conform to the HCI specification.
    wire [BufAddrW:0] ptr_diff = wptr - rptr;
    wire [BufAddrW:0] neg_diff = ~ptr_diff + 'b1;
    wire [BufAddrW:0] left     = cfg_i[f].size + (ptr_diff[BufAddrW] ? ptr_diff : neg_diff);
    wire [BufAddrW:0] used     = (ptr_diff[BufAddrW] | full) ? left : ptr_diff;
    wire [BufAddrW:0] avail    = (ptr_diff[BufAddrW] | full) ? neg_diff : left;

    // Generate status information for all clients at all times, and then when a request is received
    // we arbitrate amongst those which actually CAN proceed.
    wire prefetching = mem_rvalid & (IdxW'(f) == mem_ridx);
    always_comb begin
      // Response to FIFO write requests.
      out_o[f].wready = wgnt;
      // Response to FIFO read requests; read data comes from one of two sources:
      // - we may already have the data prefetched (`pre_rvalid` and `pre_rdata`).
      // - the memory may be returning it right now, in which case we may forward rather than
      //   capture data.
      out_o[f].rvalid = pre_rvalid | prefetching;
      out_o[f].rdata  = pre_rvalid ? pre_rdata : mem_rdata;

      // FIFO state for use by clients, reporting via the HCI registers, and interrupt generation.
      state_o[f].full   = full;
      state_o[f].empty  = empty;
      state_o[f].used   = used;
      state_o[f].avail  = avail;

      // Internal state of the FIFO; it reflects the fact that we may have read a word from the
      // FIFO by prefetching. It is presented only diagnostically in the register interface.
      state_o[f].wptr = wptr;
      state_o[f].rptr = rptr;
      state_o[f].pre  = pre_rvalid;
    end

    // Prefetched read data, presenting a FIFO interface where the assertion of `rready` consumes
    // the data rather than starting a read operation.
    wire consume_rdata = out_o[f].rvalid & in_i[f].rready;
    wire capt_rdata = &{mem_rvalid, (IdxW'(f) == mem_ridx), !in_i[f].rready};
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        pre_rvalid  <= 1'b0;
        pre_rdata   <= '0;
      end else if (sw_reset_i[f]) begin
        pre_rvalid <= 1'b0;
        // Reads by software from an empty queue/buffer cannot be prevented; just make the returned
        // data predictable.
        pre_rdata  <= '0;
      end else begin
        if (consume_rdata | capt_rdata) pre_rvalid <= capt_rdata;
        // Capture the read data returned by the memory.
        if (capt_rdata) pre_rdata <= mem_rdata;
      end
    end

    // Read pointer advancement.
    logic [BufAddrW-1:0] next_rptr;
    assign next_rptr = (rptr == cfg_i[f].max) ? cfg_i[f].min : (rptr + 'b1);

    // FIFO state.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        wptr <= '0;
        pptr <= '0;
        rptr <= '0;
        full <= 1'b0;
      end else if (sw_reset_i[f]) begin
        // Empty the FIFO.
        wptr <= cfg_i[f].min;
        pptr <= cfg_i[f].min;
        rptr <= cfg_i[f].min;
        full <= 1'b0;
      end else begin
        // Updating of write pointer and prefetching pointer.
        if (wgnt) wptr <= next_addr;
        if (pgnt) pptr <= next_addr;
        // Updating of read pointer, and `FIFO full` indicator.
        if (consume_rdata) rptr <= next_rptr;
        if (wgnt | consume_rdata) full <= wreq & (next_addr == rptr);
      end
    end

    // Is FIFO empty as far as prefetching is concerned?
    wire pre_empty = (pptr == rptr) ? empty : (pptr == wptr);

    always_comb begin
      // Should this FIFO be performing a read and/or a write?
      // - prefetching is initiated here.
      pe = ((!pre_rvalid & !prefetching) | in_i[f].rready) & !pre_empty;
      we = in_i[f].wvalid & !full;
      // Whether read or write has priority over the other depends upon the direction of the FIFO.
      preq = pe & (!we |  DirTx[f]);
      wreq = we & (!pe | !DirTx[f]);
      // Request to memory.
      req[f]       = we | pe;
      arb[f].write = wreq;
      arb[f].min   = cfg_i[f].min;
      arb[f].max   = cfg_i[f].max;
      arb[f].addr  = wreq ? wptr : pptr;
      arb[f].wdata = in_i[f].wdata;
    end
    // Only one operation may be granted per clock cycle.
    assign wgnt = gnt[f] & wreq;
    assign pgnt = gnt[f] & preq;
  end

  // After arbitration.
  logic      mem_req;
  arb_data_t mem_data;

  // Absolute priority arbiter; index 0 has the highest priority.
  // - for each FIFO we have already arbitrated above between a read request and a write request
  //   in the event that they occur simultaneously.
  logic [IdxW-1:0] idx;
  prim_arbiter_fixed #(
    .N    (N),
    .DW   (ArbDataWidth)
  ) u_arbiter (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),

    .req_i      (req),
    .data_i     (arb),
    .gnt_o      (gnt),
    .idx_o      (idx),

    .valid_o    (mem_req),
    .data_o     (mem_data),
    .ready_i    (1'b1)
  );

  // Address advancement.
  // - these two addresses are valid during the cycle in which the memory read/write is initiated.
  assign next_addr = (mem_data.addr == mem_data.max) ? mem_data.min : (mem_data.addr + 'b1);

  // Return the read data.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mem_ridx    <= '0;
    end else begin
      if (mem_req & ~mem_data.write) mem_ridx <= idx;  // Assumes single-cycle latency to read data.
    end
  end

  // SRAM Wrapper
  prim_ram_1p_adv #(
    .Depth                (BufWords),
    .Width                (DataWidth),
    .DataBitsPerMask      (DataWidth),
    .EnableECC            (0), // No Protection
    .EnableParity         (0),
    .EnableInputPipeline  (0),
    .EnableOutputPipeline (0)
  ) u_buf (
    .clk_i,
    .rst_ni,

    .req_i    (mem_req),
    .write_i  (mem_data.write),
    .addr_i   (mem_data.addr),
    .wdata_i  (mem_data.wdata),
    .wmask_i  ('1),
    .rdata_o  (mem_rdata),
    .rvalid_o (mem_rvalid),
    .rerror_o (mem_rerror),
    .cfg_i    (ram_cfg_i),
    .cfg_rsp_o(ram_cfg_rsp_o),
    .alert_o  ()
  );

endmodule
