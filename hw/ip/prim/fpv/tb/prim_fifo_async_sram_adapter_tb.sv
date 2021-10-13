// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_fifo_sram_async

module prim_fifo_async_sram_adapter_tb #(
  parameter int unsigned Width = 32,
  parameter int unsigned Depth = 16,

  parameter int unsigned FpgaSram = 0 // Use FF based
) (
  input clk_wr_i,
  input clk_rd_i,

  input rst_ni,

  input                    wvalid_i,
  output logic             wready_o,
  input        [Width-1:0] wdata_i,

  output logic             rvalid_o,
  input                    rready_i,
  output logic [Width-1:0] rdata_o
);

  localparam int unsigned       SramAw = 7;
  localparam int unsigned       SramDw = 32;
  localparam logic [SramAw-1:0] SramBaseAddr = 'h 30;

  logic              w_sram_req;
  logic              w_sram_gnt;
  logic              w_sram_write;
  logic [SramAw-1:0] w_sram_addr;
  logic [SramDw-1:0] w_sram_wdata;
  logic [SramDw-1:0] w_sram_wmask;
  logic              w_sram_rvalid; // not used
  logic [SramDw-1:0] w_sram_rdata;  // not used
  logic [1:0]        w_sram_rerror; // not used

  logic              r_sram_req;
  logic              r_sram_gnt;
  logic              r_sram_write;
  logic [SramAw-1:0] r_sram_addr;
  logic [SramDw-1:0] r_sram_wdata; // not used
  logic [SramDw-1:0] r_sram_wmask; // not used
  logic              r_sram_rvalid;
  logic [SramDw-1:0] r_sram_rdata;
  logic [1:0]        r_sram_rerror;

  prim_fifo_async_sram_adapter #(
    .Width (Width),
    .Depth (Depth),

    .SramAw (SramAw), // TODO: random with constraint
    .SramDw (SramDw), // TODO: random with constraint

    .SramBaseAddr(SramBaseAddr) // TODO: random?
  ) dut (
    .clk_wr_i,
    .rst_wr_ni (rst_ni),
    .clk_rd_i,
    .rst_rd_ni (rst_ni),

    .wvalid_i,
    .wready_o,
    .wdata_i,

    .wdepth_o (),

    .rvalid_o,
    .rready_i,
    .rdata_o,

    .rdepth_o (),

    // Sram Interface
    .w_sram_req_o   (w_sram_req   ),
    .w_sram_gnt_i   (w_sram_gnt   ),
    .w_sram_write_o (w_sram_write ),
    .w_sram_addr_o  (w_sram_addr  ),
    .w_sram_wdata_o (w_sram_wdata ),
    .w_sram_wmask_o (w_sram_wmask ),
    .w_sram_rvalid_i(w_sram_rvalid), // not used
    .w_sram_rdata_i (w_sram_rdata ),  // not used
    .w_sram_rerror_i(w_sram_rerror), // not used

     // Read SRAM port
    .r_sram_req_o   (r_sram_req   ),
    .r_sram_gnt_i   (r_sram_gnt   ),
    .r_sram_write_o (r_sram_write ),
    .r_sram_addr_o  (r_sram_addr  ),
    .r_sram_wdata_o (r_sram_wdata ), // not used
    .r_sram_wmask_o (r_sram_wmask ), // not used
    .r_sram_rvalid_i(r_sram_rvalid),
    .r_sram_rdata_i (r_sram_rdata ),
    .r_sram_rerror_i(r_sram_rerror),

    .r_full_o(),

    .r_notempty_o(),

    .w_full_o()
  );

if (FpgaSram == 1) begin : g_sram_fpga
  // FPV looks like does not like the style of ram_2p.
  prim_ram_2p #(
    .Depth           (2**SramAw),
    .Width           (SramDw),
    .DataBitsPerMask (1)
  ) u_sram (
    .clk_a_i  (clk_wr_i),
    .clk_b_i  (clk_rd_i),

    .a_req_i   (w_sram_req   ),
    .a_write_i (w_sram_write ),
    .a_addr_i  (w_sram_addr  ),
    .a_wdata_i (w_sram_wdata ),
    .a_wmask_i (w_sram_wmask ),
    .a_rdata_o (w_sram_rdata ),

    .b_req_i   (r_sram_req   ),
    .b_write_i (r_sram_write ),
    .b_addr_i  (r_sram_addr  ),
    .b_wdata_i (r_sram_wdata ),
    .b_wmask_i (r_sram_wmask ),
    .b_rdata_o (r_sram_rdata ),

    .cfg_i ('0)
  );
end else begin : g_sram_ff
  logic [SramDw-1:0] mem [2**SramAw];

  always_ff @(posedge clk_wr_i) begin
    if (w_sram_req && w_sram_write) begin
      for (int unsigned i = 0; i < SramDw ; i++) begin
        if (w_sram_wmask[i]) mem[w_sram_addr][i] <= w_sram_wdata[i];
      end // for
    end // if
  end

  always_ff @(posedge clk_rd_i) begin
    if (r_sram_req && !r_sram_write) begin
      r_sram_rdata <= mem[r_sram_addr];
    end
  end
end // !FpgaSram

  assign w_sram_gnt = w_sram_req;

  always_ff @(posedge clk_wr_i) begin
    w_sram_rvalid <= w_sram_req && !w_sram_write;
  end

  assign w_sram_rerror = '0;

  assign r_sram_gnt = r_sram_req;

  always_ff @(posedge clk_rd_i) begin
    r_sram_rvalid <= r_sram_req && !r_sram_write;
  end

  assign r_sram_rerror = '0;

  `ASSUME_FPV(WdataBins_M,
              wvalid_i |-> wdata_i inside {
                32'h DEAD_BEEF, 32'h5A5A_A5A5, 32'h 1234_5678
                },
              clk_wr_i, !rst_ni)

`ifdef FPV_ON
  logic [Width-1:0] storage [Depth];
  logic [Width-1:0] rdata;
  logic [$clog2(Depth)-1:0] wptr, rptr;
  logic wack, rack;

  assign wack = wvalid_i && wready_o;
  assign rack = rvalid_o && rready_i;

  always_ff @(posedge clk_wr_i or negedge rst_ni) begin
    if (!rst_ni) wptr <= '0;
    else if (wack) wptr <= wptr+1;
  end
  always_ff @(posedge clk_rd_i or negedge rst_ni) begin
    if (!rst_ni) rptr <= '0;
    else if (rack) rptr <= rptr+1;
  end

  always_ff @(posedge clk_wr_i or negedge rst_ni) begin
    if (!rst_ni) storage <= '{default:'0};
    else if (wack) begin
      storage[wptr] <= wdata_i;
    end
  end

  assign rdata = storage[rptr];

  `ASSERT(DataIntegrityCheck_A,
          rack |-> rdata_o == rdata,
          clk_rd_i, !rst_ni)
`endif // FPV_ON

endmodule : prim_fifo_async_sram_adapter_tb
