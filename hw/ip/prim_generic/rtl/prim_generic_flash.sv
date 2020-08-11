// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// prim flash module - Emulated using memory
//

module prim_generic_flash #(
    parameter int InfosPerBank = 1,  // info pages per bank
    parameter int PagesPerBank = 256,  // data pages per bank
    parameter int WordsPerPage = 256,  // words per page
    parameter int DataWidth = 32,  // bits per word
    parameter bit SkipInit = 1,  // this is an option to reset flash to all F's at reset

    // Derived parameters
    localparam int PageW = $clog2 (PagesPerBank),
    localparam int WordW = $clog2 (WordsPerPage),
    localparam int AddrW = PageW + WordW
) (
    input                                               clk_i,
    input                                               rst_ni,
    input                                               rd_i,
    input                                               prog_i,
    input                                               pg_erase_i,
    input                                               bk_erase_i,
    input                               [    AddrW-1:0] addr_i,
    input  flash_ctrl_pkg::flash_part_e                 part_i,
    input                               [DataWidth-1:0] prog_data_i,
    output logic                                        ack_o,
    output logic                        [DataWidth-1:0] rd_data_o,
    output logic                                        init_busy_o,
    input                                               tck_i,
    input                                               tdi_i,
    input                                               tms_i,
    output logic                                        tdo_o,
    input                                               scanmode_i,
    input                                               scan_reset_ni,
    input                                               flash_power_ready_hi,
    input                                               flash_power_down_hi,
    inout                               [          3:0] flash_test_mode_ai,
    inout                                               flash_test_voltage_hi
);

  // Emulated flash macro values
  localparam int ReadCycles = 1;
  localparam int ProgCycles = 50;
  localparam int PgEraseCycles = 200;
  localparam int BkEraseCycles = 2000;

  // Locally derived values
  localparam int WordsPerBank = PagesPerBank * WordsPerPage;
  localparam int WordsPerInfoBank = InfosPerBank * WordsPerPage;
  localparam int InfoAddrW = $clog2(WordsPerInfoBank);

  typedef enum logic [2:0] {
    StReset = 'h0,
    StInit = 'h1,
    StIdle = 'h2,
    StRead = 'h3,
    StProg = 'h4,
    StErase = 'h5
  } state_e;

  state_e st_q, st_d;

  logic [31:0] time_cnt;
  logic [31:0] index_cnt;
  logic time_cnt_inc, time_cnt_clr, time_cnt_set1;
  logic index_cnt_inc, index_cnt_clr;
  logic [31:0] index_limit_q, index_limit_d;
  logic [31:0] time_limit_q, time_limit_d;
  logic prog_pend_q, prog_pend_d;
  logic mem_req;
  logic mem_wr;
  logic [AddrW-1:0] mem_addr;
  flash_ctrl_pkg::flash_part_e mem_part;
  logic [DataWidth-1:0] held_rdata;
  logic [DataWidth-1:0] held_wdata;
  logic [DataWidth-1:0] mem_wdata;
  logic hold_cmd;
  logic [AddrW-1:0] held_addr;
  flash_ctrl_pkg::flash_part_e held_part;

  // insert a fifo here to break the large fanout from inputs to memories on reads
  logic rd_q;
  logic [AddrW-1:0] addr_q;
  flash_ctrl_pkg::flash_part_e part_q;

  prim_fifo_sync #(
      .Width(AddrW + $bits(flash_ctrl_pkg::flash_part_e)),
      .Pass(0),
      .Depth(2)
  ) i_slice (
      .clk_i,
      .rst_ni,
      .clr_i   (1'b0),
      .wvalid_i(rd_i),
      .wready_o(),
      .wdata_i ({part_i, addr_i}),
      .depth_o (),
      .rvalid_o(rd_q),
      .rready_i(hold_cmd),  //whenver command is held, pop
      .rdata_o ({part_q, addr_q})
  );


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st_q <= StReset;
    else st_q <= st_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      held_addr <= '0;
      held_part <= flash_ctrl_pkg::FlashPartData;
      held_wdata <= '0;
    end else if (hold_cmd) begin
      held_addr <= rd_q ? addr_q : addr_i;
      held_part <= rd_q ? part_q : part_i;
      held_wdata <= prog_data_i;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      time_limit_q <= 32'h0;
      index_limit_q <= 32'h0;
      prog_pend_q <= 1'h0;
    end else begin
      time_limit_q <= time_limit_d;
      index_limit_q <= index_limit_d;
      prog_pend_q <= prog_pend_d;
    end
  end

  // prog_pend_q is necessary to emulate flash behavior that a bit written to 0 cannot be written
  // back to 1 without an erase
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      time_cnt <= 32'h0;
      index_cnt <= 32'h0;
      held_rdata <= 'h0;
    end else begin
      if (time_cnt_inc) time_cnt <= time_cnt + 1'b1;
      else if (time_cnt_set1) time_cnt <= 32'h1;
      else if (time_cnt_clr) time_cnt <= 32'h0;

      if (index_cnt_inc) index_cnt <= index_cnt + 1'b1;
      else if (index_cnt_clr) index_cnt <= 32'h0;

      if (prog_pend_q) held_rdata <= rd_data_o;

    end
  end


  always_comb begin
    // state
    st_d = st_q;

    // internally consumed signals
    index_limit_d = index_limit_q;
    time_limit_d = time_limit_q;
    prog_pend_d = prog_pend_q;
    mem_req = 'h0;
    mem_wr = 'h0;
    mem_addr = 'h0;
    mem_part = flash_ctrl_pkg::FlashPartData;
    mem_wdata = 'h0;
    time_cnt_inc = 1'h0;
    time_cnt_clr = 1'h0;
    time_cnt_set1 = 1'h0;
    index_cnt_inc = 1'h0;
    index_cnt_clr = 1'h0;
    hold_cmd = 1'h0;

    // i/o
    init_busy_o = 1'h0;
    ack_o = 1'h0;

    unique case (st_q)
      StReset: begin
        init_busy_o = 1'h1;
        st_d = StInit;
      end
      // Emulate flash power up to all 1's
      // This implies this flash will not survive a reset
      // Might need a different RESET for FPGA purposes
      StInit: begin
        init_busy_o = 1'h1;
        if (index_cnt < WordsPerBank && !SkipInit) begin
          st_d = StInit;
          index_cnt_inc = 1'b1;
          mem_req = 1'h0;
          mem_wr = 1'h0;
          mem_addr = index_cnt[AddrW - 1:0];
          mem_wdata = {DataWidth{1'b1}};
        end else begin
          st_d = StIdle;
          index_cnt_clr = 1'b1;
        end
      end
      StIdle: begin
        if (rd_q) begin
          // reads begin immediately
          hold_cmd = 1'b1;
          mem_addr = addr_q;
          mem_part = part_q;
          mem_req = 1'b1;
          time_cnt_inc = 1'b1;
          st_d = StRead;
        end else if (prog_i) begin
          hold_cmd = 1'b1;
          st_d = StRead;
          prog_pend_d = 1'b1;
        end else if (pg_erase_i) begin
          hold_cmd = 1'b1;
          st_d = StErase;
          index_limit_d = WordsPerPage;
          time_limit_d = PgEraseCycles;
        end else if (bk_erase_i) begin
          hold_cmd = 1'b1;
          st_d = StErase;
          index_limit_d = WordsPerBank;
          time_limit_d = BkEraseCycles;
        end
      end
      StRead: begin
        mem_addr = held_addr;
        mem_part = held_part;
        if (time_cnt < ReadCycles) begin
          mem_req = 1'b1;
          time_cnt_inc = 1'b1;
        end else if (!prog_pend_q) begin
          ack_o = 1'b1;  //finish up transaction

          // if another request already pending
          if (rd_q) begin
            hold_cmd = 1'b1;
            mem_addr = addr_q;
            mem_part = part_q;
            mem_req = 1'b1;
            time_cnt_set1 = 1'b1;
            st_d = StRead;
          end else begin
            time_cnt_clr = 1'b1;
            st_d = StIdle;
          end
        end else if (prog_pend_q) begin
          // this is the read performed before a program operation
          prog_pend_d = 1'b0;
          time_cnt_clr = 1'b1;
          st_d = StProg;
        end
      end
      StProg: begin
        mem_addr = held_addr;
        mem_part = held_part;

        // if data is already 0, cannot program to 1 without erase
        mem_wdata = held_wdata & held_rdata;
        if (time_cnt < ProgCycles) begin
          mem_req = 1'b1;
          mem_wr = 1'b1;
          time_cnt_inc = 1'b1;
        end else begin
          st_d = StIdle;
          ack_o = 1'b1;
          time_cnt_clr = 1'b1;
        end
      end
      StErase: begin
        // Actual erasing of the page
        if (index_cnt < index_limit_q || time_cnt < time_limit_q) begin
          mem_req = 1'b1;
          mem_wr = 1'b1;
          mem_wdata = {DataWidth{1'b1}};

          mem_addr = held_addr + index_cnt[AddrW - 1:0];
          mem_part = held_part;
          time_cnt_inc = (time_cnt < time_limit_q);
          index_cnt_inc = (index_cnt < index_limit_q);
        end else begin
          st_d = StIdle;
          ack_o = 1'b1;
          time_cnt_clr = 1'b1;
          index_cnt_clr = 1'b1;
        end
      end
      default: begin
        st_d = StIdle;
      end
    endcase  // unique case (st_q)
  end  // always_comb

  logic [DataWidth-1:0] rd_data_main, rd_data_info;

  prim_ram_1p #(
      .Width(DataWidth),
      .Depth(WordsPerBank),
      .DataBitsPerMask(DataWidth)
  ) u_mem (
      .clk_i,
      .req_i  (mem_req & (mem_part == flash_ctrl_pkg::FlashPartData)),
      .write_i(mem_wr),
      .addr_i (mem_addr),
      .wdata_i(mem_wdata),
      .wmask_i({DataWidth{1'b1}}),
      .rdata_o(rd_data_main)
  );

  prim_ram_1p #(
      .Width(DataWidth),
      .Depth(WordsPerInfoBank),
      .DataBitsPerMask(DataWidth)
  ) u_info_mem (
      .clk_i,
      .req_i  (mem_req & (mem_part == flash_ctrl_pkg::FlashPartInfo)),
      .write_i(mem_wr),
      .addr_i (mem_addr[0 +: InfoAddrW]),
      .wdata_i(mem_wdata),
      .wmask_i({DataWidth{1'b1}}),
      .rdata_o(rd_data_info)
  );

  assign rd_data_o = held_part == flash_ctrl_pkg::FlashPartData ? rd_data_main : rd_data_info;

  // hard-wire assignment for now
  assign tdo_o = 1'b0;

endmodule  // prim_generic_flash
