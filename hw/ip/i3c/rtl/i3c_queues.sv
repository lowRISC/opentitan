// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A single SRAM-style interface implements multiple logical queues at successive word addresses.
// - HCI queues: Command Queue, Response Queue, Data Transfer Buffer, IBI Queue.
// - TTI queues: TxN buffer, Rx buffer, TxN Desc Queue, Rx Desc Queue, IBI Buffer and Desc Queue,
//               Async Event Queue.

module i3c_queues
#(
  // The number of logical queues implemented by this SRAM interface.
  parameter int unsigned NumQueues = 4,
  // Data width, in bits.
  parameter int unsigned DataWidth = 32,
  // Indicates, for each queue in turn, whether writing by software is supported.
  parameter bit [NumQueues-1:0] SupportTx = '1,
  // Indicates, for each queue in turn, whether reading by software is supported.
  // - most of the queues in both the HCI and the TTI are unidirectional, with the exception
  //   being `TL_XferBuf` for example, which maps to both the Tx Data buffer and the Rx Data Buffer.
  parameter bit [NumQueues-1:0] SupportRx = '1,

  // Derived parameters.
  localparam int unsigned AddrWidth = $clog2(NumQueues)  // The number of address bits.
) (
  // Clock and reset.
  input                         clk_i,
  input                         rst_ni,

  // Single SRAM interface (e.g. `tlul_adapter_sram`).
  input                         req_i,
  output logic                  gnt_o,
  input                         we_i,
  input         [AddrWidth-1:0] addr_i,
  input         [DataWidth-1:0] wdata_i,
  output logic                  rvalid_o,
  output logic  [DataWidth-1:0] rdata_o,

  // Writes to logical queues.
  input                         buf_wready_i[NumQueues],
  input                         buf_full_i[NumQueues],
  output logic                  buf_wvalid_o[NumQueues],
  output logic  [DataWidth-1:0] buf_wdata_o,

  // Reads from logical queues.
  input                         buf_rvalid_i[NumQueues],
  input         [DataWidth-1:0] buf_rdata_i[NumQueues],
  input                         buf_empty_i[NumQueues],
  output logic                  buf_rready_o[NumQueues],

  // Diagnostic error indicator.
  output                        err_o
);

  // A read from an empty queue will be more apparent if we return all '1's rather than zeros.
  // localparam logic [DataWidth-1:0] NoRData = '1;
  // TODO: This is a development aid; replace with the above at some point.
  localparam logic [DataWidth-1:0] NoRData = 32'hdece_a5ed;

  // Read operations from logical queues.
  logic [NumQueues-1:0] gnt_rd;
  logic [NumQueues-1:0] re;
  logic rd_empty_error;
  always_comb begin : reads
    rd_empty_error = 1'b0;
    for (int unsigned q = 0; q < NumQueues; q++) begin
      re[q] = req_i & (addr_i == q) & !we_i;
      // Assert read request iff the queue is not empty, and block until arbitration is won
      // and read data is available. Normally there will be prefetched data already available.
      buf_rready_o[q] = re[q] & !buf_empty_i[q] & SupportRx[q];
      // Can the read proceed?
      // - reads also proceed by returning data when the queue is empty or reading is unsupported.
      gnt_rd[q] = re[q] & (buf_rvalid_i[q] | buf_empty_i[q] | !SupportRx[q]);
      // Report `read when empty` condition.
      rd_empty_error |= re[q] & (buf_empty_i[q] | !SupportRx[q]);
    end
  end

  // Write operations into logical queues.
  logic [NumQueues-1:0] gnt_wr;
  logic [NumQueues-1:0] we;
  logic wr_full_error;
  always_comb begin : writes
    wr_full_error = 1'b0;
    for (int unsigned q = 0; q < NumQueues; q++) begin
      we[q] = req_i & (addr_i == q) & we_i;
      // Assert write request iff the queue is not full, and block until arbitration is won
      // and the write data is accepted.
      buf_wvalid_o[q] = we[q] & !buf_full_i[q] & SupportTx[q];
      // Can the write proceed?
      // - writes proceed with no effect when the queue is full or writes are unsupported.
      gnt_wr[q] = we[q] & (buf_wready_i[q] | buf_full_i[q] | !SupportTx[q]);
      // Report `write when full` condition.
      wr_full_error |= we[q] & (buf_full_i[q] | !SupportTx[q]);
    end
    // Write data is just forwarded to all write paths.
    buf_wdata_o = wdata_i;
  end

  // Granting of requests.
  assign gnt_o = |{gnt_rd, gnt_wr};

  // Read data from logical queues.
  wire rvalid = |gnt_rd;
  wire rdata_valid = &{addr_i < NumQueues, buf_rvalid_i[addr_i], SupportRx[addr_i]};
  wire [DataWidth-1:0] rdata = rdata_valid ? buf_rdata_i[addr_i] : NoRData;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid_o  <= 1'b0;
      rdata_o   <= '0;
    end else begin
      rvalid_o  <= rvalid;
      if (rvalid) rdata_o <= rdata;
    end
  end

  // Error output for diagnostic use, in the event of software error.
  assign err_o = wr_full_error | rd_empty_error;

endmodule
