// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// prim flash module - Emulated using memory
//

module prim_generic_flash #(
  parameter int PagesPerBank = 256, // pages per bank
  parameter int WordsPerPage = 256, // words per page
  parameter int DataWidth   = 32,   // bits per word
  parameter bit SkipInit = 1,       // this is an option to reset flash to all F's at reset

  // Derived parameters
  localparam int PageW = $clog2(PagesPerBank),
  localparam int WordW = $clog2(WordsPerPage),
  localparam int AddrW = PageW + WordW
) (
  input                        clk_i,
  input                        rst_ni,
  input                        req_i,
  input                        host_req_i,
  input [AddrW-1:0]            host_addr_i,
  input                        rd_i,
  input                        prog_i,
  input                        pg_erase_i,
  input                        bk_erase_i,
  input [AddrW-1:0]            addr_i,
  input [DataWidth-1:0]        prog_data_i,
  output logic                 host_req_rdy_o,
  output logic                 host_req_done_o,
  output logic                 rd_done_o,
  output logic                 prog_done_o,
  output logic                 erase_done_o,
  output logic [DataWidth-1:0] rd_data_o,
  output logic                 init_busy_o
);

  // Emulated flash macro values
  localparam int ReadCycles = 1;
  localparam int ProgCycles = 50;
  localparam int PgEraseCycles = 200;
  localparam int BkEraseCycles = 2000;

  // Locally derived values
  localparam int WordsPerBank  = PagesPerBank * WordsPerPage;

  typedef enum logic [2:0] {
    StReset    = 'h0,
    StInit     = 'h1,
    StIdle     = 'h2,
    StHostRead = 'h3,
    StRead     = 'h4,
    StProg     = 'h5,
    StErase    = 'h6
  } state_e;

  state_e st_next, st;

  logic [31:0]              time_cnt;
  logic [31:0]              index_cnt;
  logic                     time_cnt_inc ,time_cnt_clr, time_cnt_set1;
  logic                     index_cnt_inc, index_cnt_clr;
  logic [31:0]              index_limit, index_limit_next;
  logic [31:0]              time_limit, time_limit_next;
  logic                     prog_pend, prog_pend_next;
  logic                     mem_req;
  logic                     mem_wr;
  logic [AddrW-1:0]         mem_addr;
  logic [DataWidth-1:0]     held_data;
  logic [DataWidth-1:0]     mem_wdata;
  logic                     hold_rd_cmd;
  logic [AddrW-1:0]         held_rd_addr;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st <= StReset;
    else st <= st_next;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) held_rd_addr <= '0;
    else if (hold_rd_cmd) held_rd_addr <= host_addr_i;
  end

  // prog_pend is necessary to emulate flash behavior that a bit written to 0 cannot be written
  // back to 1 without an erase
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      time_cnt <= 32'h0;
      index_cnt <= 32'h0;
      time_limit <= 32'h0;
      index_limit <= 32'h0;
      held_data <= 'h0;
      prog_pend <= 1'h0;
    end else begin

      time_limit <= time_limit_next;
      index_limit <= index_limit_next;
      prog_pend <= prog_pend_next;

      if (time_cnt_inc) time_cnt <= time_cnt + 1'b1;
      else if (time_cnt_set1) time_cnt <= 32'h1;
      else if (time_cnt_clr) time_cnt <= 32'h0;

      if (index_cnt_inc) index_cnt <= index_cnt + 1'b1;
      else if (index_cnt_clr) index_cnt <= 32'h0;

      if (prog_pend) held_data <= rd_data_o;

    end
  end


  always_comb begin
    st_next          = st;
    index_limit_next = index_limit;
    time_limit_next  = time_limit;
    prog_pend_next   = prog_pend;
    mem_req          = 'h0;
    mem_wr           = 'h0;
    mem_addr         = 'h0;
    mem_wdata        = 'h0;
    time_cnt_inc     = 1'h0;
    time_cnt_clr     = 1'h0;
    time_cnt_set1    = 1'h0;
    index_cnt_inc    = 1'h0;
    index_cnt_clr    = 1'h0;
    rd_done_o        = 1'h0;
    prog_done_o      = 1'h0;
    erase_done_o     = 1'h0;
    init_busy_o      = 1'h0;
    host_req_rdy_o   = 1'h1;
    host_req_done_o  = 1'h0;
    hold_rd_cmd      = 1'h0;

    unique case (st)
      StReset: begin
        host_req_rdy_o = 1'b0;
        init_busy_o = 1'h1;
        st_next = StInit;
      end
      // Emulate flash power up to all 1's
      // This implies this flash will not survive a reset
      // Might need a different RESET for FPGA purposes
      StInit: begin
        host_req_rdy_o = 1'b0;
        init_busy_o = 1'h1;
        if (index_cnt < WordsPerBank && !SkipInit) begin
          st_next = StInit;
          index_cnt_inc = 1'b1;
          mem_req = 1'h0;
          mem_wr  = 1'h0;
          mem_addr = index_cnt[AddrW-1:0];
          mem_wdata = {DataWidth{1'b1}};
        end else begin
          st_next = StIdle;
          index_cnt_clr = 1'b1;
        end
      end
      StIdle: begin
        // host reads will always take priority over controller operations.  However ongoing
        // controller operations will not be interrupted
        if (host_req_i) begin
          // reads begin immediately
          hold_rd_cmd = 1'b1;
          mem_addr = host_addr_i;
          mem_req = 1'b1;
          time_cnt_inc = 1'b1;
          st_next = StHostRead;
        end else if (req_i && rd_i) begin
          st_next = StRead;
        end else if (req_i && prog_i) begin
          st_next = StRead;
          prog_pend_next = 1'b1;
        end else if (req_i && pg_erase_i) begin
          st_next = StErase;
          index_limit_next = WordsPerPage;
          time_limit_next = PgEraseCycles;
        end else if (req_i && bk_erase_i) begin
          st_next = StErase;
          index_limit_next = WordsPerBank;
          time_limit_next = BkEraseCycles;
        end
      end
      StHostRead: begin
        mem_addr = held_rd_addr;
        if (time_cnt < ReadCycles) begin
          mem_req = 1'b1;
          time_cnt_inc = 1'b1;
          host_req_rdy_o = 1'b0;
        end else begin
          host_req_done_o = 1'b1; //finish up transaction

          // if another request already pending
          if (host_req_i) begin
            hold_rd_cmd = 1'b1;
            mem_addr = host_addr_i;
            mem_req = 1'b1;
            time_cnt_set1 = 1'b1;
            st_next = StHostRead;
          end else begin
            time_cnt_clr = 1'b1;
            st_next = StIdle;
          end
        end
      end
      StRead: begin
        host_req_rdy_o = 1'b0;
        mem_addr = addr_i;
        if (time_cnt < ReadCycles) begin
          mem_req = 1'b1;
          time_cnt_inc = 1'b1;
        end else begin
          prog_pend_next = 1'b0;
          rd_done_o  = 1'b1;
          time_cnt_clr = 1'b1;
          st_next = prog_pend ? StProg : StIdle;
        end
      end
      StProg: begin
        host_req_rdy_o = 1'b0;
        mem_addr = addr_i;

        // if data is already 0, cannot program to 1 without erase
        mem_wdata = prog_data_i & held_data;
        if (time_cnt < ProgCycles) begin
          mem_req = 1'b1;
          mem_wr = 1'b1;
          time_cnt_inc = 1'b1;
        end else begin
          st_next = StIdle;
          prog_done_o  = 1'b1;
          time_cnt_clr = 1'b1;
        end
      end
      StErase: begin
        host_req_rdy_o = 1'b0;

        // Actual erasing of the page
        if (index_cnt < index_limit || time_cnt < time_limit) begin
          mem_req = 1'b1;
          mem_wr = 1'b1;
          mem_wdata = {DataWidth{1'b1}};

          mem_addr = addr_i + index_cnt[AddrW-1:0];
          time_cnt_inc = (time_cnt < time_limit);
          index_cnt_inc = (index_cnt < index_limit);
        end else begin
          st_next = StIdle;
          erase_done_o = 1'b1;
          time_cnt_clr = 1'b1;
          index_cnt_clr = 1'b1;
        end
      end
      default: begin
        host_req_rdy_o = 1'b0;
        st_next = StIdle;
      end
    endcase // unique case (st)
  end // always_comb

  prim_ram_1p #(
    .Width(DataWidth),
    .Depth(WordsPerBank),
    .DataBitsPerMask(DataWidth)
  ) u_mem (
    .clk_i,
    .rst_ni,
    .req_i    (mem_req),
    .write_i  (mem_wr),
    .addr_i   (mem_addr),
    .wdata_i  (mem_wdata),
    .wmask_i  ({DataWidth{1'b1}}),
    .rvalid_o (),
    .rdata_o  (rd_data_o)
  );



endmodule // prim_generic_flash
