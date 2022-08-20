// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Emulate a single generic flash bank
//

module prim_generic_flash_bank #(
  parameter int InfosPerBank   = 1,   // info pages per bank
  parameter int InfoTypes      = 1,   // different info types
  parameter int InfoTypesWidth = 1,   // different info types
  parameter int PagesPerBank   = 256, // data pages per bank
  parameter int WordsPerPage   = 256, // words per page
  parameter int DataWidth      = 32,  // bits per word

  // Derived parameters
  localparam int PageW = $clog2(PagesPerBank),
  localparam int WordW = $clog2(WordsPerPage),
  localparam int AddrW = PageW + WordW
) (
  input                              clk_i,
  input                              rst_ni,
  input                              rd_i,
  input                              prog_i,
  input                              prog_last_i,
  // the generic model does not make use of program types
  input flash_ctrl_pkg::flash_prog_e prog_type_i,
  input                              pg_erase_i,
  input                              bk_erase_i,
  input                              erase_suspend_req_i,
  input                              he_i,
  input [AddrW-1:0]                  addr_i,
  input flash_ctrl_pkg::flash_part_e part_i,
  input [InfoTypesWidth-1:0]         info_sel_i,
  input [DataWidth-1:0]              prog_data_i,
  output logic                       ack_o,
  output logic                       done_o,
  output logic [DataWidth-1:0]       rd_data_o,
  input                              init_i,
  output logic                       init_busy_o,
  input                              flash_power_ready_h_i,
  input                              flash_power_down_h_i
);

  `ifdef SYNTHESIS
    localparam int ReadLatency   = 1;
    localparam int ProgLatency   = 50;
    localparam int EraseLatency  = 200;

  `else
    int ReadLatency   = 1;
    int ProgLatency   = 50;
    int EraseLatency  = 200;

    initial begin
      void'($value$plusargs("flash_read_latency=%0d", ReadLatency));
      void'($value$plusargs("flash_program_latency=%0d", ProgLatency));
      void'($value$plusargs("flash_erase_latency=%0d", EraseLatency));
    end
  `endif

  // Emulated flash macro values
  localparam int BkEraseCycles = 2000;
  localparam int InitCycles = 100;

  // Locally derived values
  localparam int WordsPerBank  = PagesPerBank * WordsPerPage;
  localparam int WordsPerInfoBank = InfosPerBank * WordsPerPage;
  localparam int InfoAddrW = $clog2(WordsPerInfoBank);

  typedef enum logic [2:0] {
    StReset     = 'h0,
    StInit      = 'h1,
    StIdle      = 'h2,
    StRead      = 'h3,
    StProg      = 'h4,
    StErase     = 'h5,
    StErSuspend = 'h6
  } state_e;

  state_e st_q, st_d;

  logic [31:0]              time_cnt;
  logic [31:0]              index_cnt;
  logic                     time_cnt_inc ,time_cnt_clr, time_cnt_set1;
  logic                     index_cnt_inc, index_cnt_clr;
  logic [31:0]              index_limit_q, index_limit_d;
  logic [31:0]              time_limit_q, time_limit_d;
  logic                     prog_pend_q, prog_pend_d;
  logic                     mem_req;
  logic                     mem_wr;
  logic [DataWidth-1:0]     mem_wdata;
  logic [AddrW-1:0]         mem_addr;
  flash_ctrl_pkg::flash_part_e mem_part;
  logic                     mem_bk_erase;
  logic [InfoTypesWidth-1:0] mem_info_sel;

  // insert a fifo here to break the large fanout from inputs to memories on reads
  typedef struct packed {
    logic                        rd;
    logic                        prog;
    logic                        prog_last;
    flash_ctrl_pkg::flash_prog_e prog_type;
    logic                        pg_erase;
    logic                        bk_erase;
    logic [AddrW-1:0]            addr;
    flash_ctrl_pkg::flash_part_e part;
    logic [InfoTypesWidth-1:0]   info_sel;
    logic [DataWidth-1:0]        prog_data;
  } cmd_payload_t;

  cmd_payload_t cmd_d, cmd_q;
  logic cmd_valid;
  logic pop_cmd;
  logic mem_rd_q, mem_rd_d;

  assign cmd_d = '{
    rd :       rd_i,
    prog:      prog_i,
    prog_last: prog_last_i,
    prog_type: prog_type_i,
    pg_erase:  pg_erase_i,
    bk_erase:  bk_erase_i,
    addr:      addr_i,
    part:      part_i,
    info_sel:  info_sel_i,
    prog_data: prog_data_i
  };

  // for read transactions, in order to reduce latency, the
  // command fifo is popped early (before done_o).  This is to ensure that when
  // the current transaction is complete, during the same cycle
  // a new read can be issued. As a result, the command is popped
  // immediately after the read is issued, rather than waiting for
  // the read to be completed.  The same restrictions are not necessary
  // for program / erase, which do not have the same performance
  // requirements.

  // when the flash is going through init, do not accept any transactions
  logic wvalid;
  logic ack;
  assign wvalid = (rd_i | prog_i | pg_erase_i | bk_erase_i) & !init_busy_o;
  assign ack_o = ack & !init_busy_o;

  prim_fifo_sync #(
    .Width   ($bits(cmd_payload_t)),
    .Pass    (0),
    .Depth   (2)
  ) u_cmd_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(wvalid),
    .wready_o(ack),
    .wdata_i (cmd_d),
    .depth_o (),
    .full_o (),
    .rvalid_o(cmd_valid),
    .rready_i(pop_cmd),
    .rdata_o (cmd_q),
    .err_o   ()
  );

  logic rd_req, prog_req, pg_erase_req, bk_erase_req;
  assign rd_req = cmd_valid & cmd_q.rd;
  assign prog_req = cmd_valid & cmd_q.prog;
  assign pg_erase_req = cmd_valid & cmd_q.pg_erase;
  assign bk_erase_req = cmd_valid & cmd_q.bk_erase;

  // for read / program operations, the index cnt should be 0
  assign mem_rd_d = mem_req & ~mem_wr;
  assign mem_addr = cmd_q.addr + index_cnt[AddrW-1:0];
  assign mem_part = cmd_q.part;
  assign mem_bk_erase = cmd_q.bk_erase;

  assign mem_info_sel = cmd_q.info_sel;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) st_q <= StReset;
    else st_q <= st_d;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      time_limit_q  <= 'h0;
      index_limit_q <= 'h0;
      prog_pend_q   <= 'h0;
      mem_rd_q      <= 'h0;
    end else begin
      time_limit_q  <= time_limit_d;
      index_limit_q <= index_limit_d;
      prog_pend_q   <= prog_pend_d;
      mem_rd_q      <= mem_rd_d;
    end
  end

  // latch read data from emulated memories the cycle after a read
  logic [DataWidth-1:0] rd_data_q, rd_data_d;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd_data_q <= '0;
    end else if (mem_rd_q) begin
      rd_data_q <= rd_data_d;
    end
  end

  // latch partiton being read since the command fifo is popped early
  flash_ctrl_pkg::flash_part_e rd_part_q;
  logic [InfoTypesWidth-1:0] info_sel_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd_part_q <= flash_ctrl_pkg::FlashPartData;
      info_sel_q <= '0;
    end else if (mem_rd_d) begin
      rd_part_q <= cmd_q.part;
      info_sel_q <= cmd_q.info_sel;
    end
  end

  // if read cycle is only 1, we can expose the unlatched data directly
  assign rd_data_o = ReadLatency == 1 ? rd_data_d : rd_data_q;

  // prog_pend_q is necessary to emulate flash behavior that a bit written to 0 cannot be written
  // back to 1 without an erase
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      time_cnt  <= 'h0;
      index_cnt <= 'h0;
    end else begin
      if (time_cnt_inc) time_cnt <= time_cnt + 1'b1;
      else if (time_cnt_set1) time_cnt <= 32'h1;
      else if (time_cnt_clr) time_cnt <= 32'h0;

      if (index_cnt_inc) index_cnt <= index_cnt + 1'b1;
      else if (index_cnt_clr) index_cnt <= 32'h0;
    end
  end

  always_comb begin
    // state
    st_d             = st_q;

    // internally consumed signals
    index_limit_d    = index_limit_q;
    time_limit_d     = time_limit_q;
    prog_pend_d      = prog_pend_q;
    mem_req          = '0;
    mem_wr           = '0;
    mem_wdata        = '0;
    time_cnt_inc     = '0;
    time_cnt_clr     = '0;
    time_cnt_set1    = '0;
    index_cnt_inc    = '0;
    index_cnt_clr    = '0;

    // i/o
    init_busy_o      = '0;
    pop_cmd          = '0;
    done_o           = '0;

    unique case (st_q)
      StReset: begin
        init_busy_o = 1'b1;
        if (init_i && flash_power_ready_h_i && !flash_power_down_h_i) begin
          st_d = StInit;
        end
      end

      // Emulate flash initilaization with a wait timer
      StInit: begin
        init_busy_o = 1'h1;
        if (index_cnt < InitCycles) begin
          st_d = StInit;
          index_cnt_inc = 1'b1;
        end else begin
          st_d = StIdle;
          index_cnt_clr = 1'b1;
        end
      end

      StIdle: begin
        if (rd_req) begin
          pop_cmd = 1'b1;
          mem_req = 1'b1;
          time_cnt_inc = 1'b1;
          st_d = StRead;
        end else if (prog_req) begin
          mem_req = 1'b1;
          prog_pend_d = 1'b1;
          st_d = StRead;
        end else if (pg_erase_req) begin
          st_d = StErase;
          index_limit_d = WordsPerPage;
          time_limit_d = EraseLatency;
        end else if (bk_erase_req) begin
          st_d = StErase;
          index_limit_d = WordsPerBank;
          time_limit_d = BkEraseCycles;
        end
      end

      StRead: begin
        if (time_cnt < ReadLatency) begin
          time_cnt_inc = 1'b1;

        end else if (!prog_pend_q) begin
          done_o = 1'b1;

          // if another request already pending
          if (rd_req) begin
            pop_cmd = 1'b1;
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
        // if data is already 0, cannot program to 1 without erase
        mem_wdata = cmd_q.prog_data & rd_data_q;
        if (time_cnt < ProgLatency) begin
          mem_req = 1'b1;
          mem_wr = 1'b1;
          time_cnt_inc = 1'b1;
        end else begin
          st_d = StIdle;
          pop_cmd = 1'b1;
          done_o = cmd_q.prog_last;
          time_cnt_clr = 1'b1;
        end
      end

      StErase: begin
        // Actual erasing of the page
        if (erase_suspend_req_i) begin
          st_d = StErSuspend;
        end else if (index_cnt < index_limit_q || time_cnt < time_limit_q) begin
          mem_req = 1'b1;
          mem_wr = 1'b1;
          mem_wdata = {DataWidth{1'b1}};
          time_cnt_inc = (time_cnt < time_limit_q);
          index_cnt_inc = (index_cnt < index_limit_q);
        end else begin
          st_d = StIdle;
          pop_cmd = 1'b1;
          done_o = 1'b1;
          time_cnt_clr = 1'b1;
          index_cnt_clr = 1'b1;
        end
      end // case: StErase

      // The done can actually be signaled back in `StErase`, but move it
      // to a different state to better model the ack_o/done_o timing separation
      StErSuspend: begin
         done_o = 1'b1;
         pop_cmd = 1'b1;
         time_cnt_clr = 1'b1;
         index_cnt_clr = 1'b1;
         st_d = StIdle;
      end


      default: begin
        st_d = StIdle;
      end

    endcase // unique case (st_q)

    // Emulate power down and power loss behavior
    if (!flash_power_ready_h_i || flash_power_down_h_i) begin
      st_d = StReset;
    end

  end // always_comb

  logic [DataWidth-1:0] rd_data_main, rd_data_info;
  logic [InfoTypes-1:0][DataWidth-1:0] rd_nom_data_info;

  // data memory is requested whenver it's a transaction targetted at the data partition
  // OR if it's a bank erase
  logic data_mem_req;
  assign data_mem_req = mem_req &
                        (mem_part == flash_ctrl_pkg::FlashPartData |
                         mem_bk_erase);

  prim_ram_1p #(
    .Width(DataWidth),
    .Depth(WordsPerBank),
    .DataBitsPerMask(DataWidth)
  ) u_mem (
    .clk_i,
    .req_i    (data_mem_req),
    .write_i  (mem_wr),
    .addr_i   (mem_addr),
    .wdata_i  (mem_wdata),
    .wmask_i  ({DataWidth{1'b1}}),
    .rdata_o  (rd_data_main),
    .cfg_i    ('0)
  );

  for (genvar info_type = 0; info_type < InfoTypes; info_type++) begin : gen_info_types

    // when info partitions are selected for bank erase, all info types are erased.
    // if NOT bank erase, then only the selected info partition is erased
    logic info_mem_req;
    assign info_mem_req = mem_req &
                          (mem_part == flash_ctrl_pkg::FlashPartInfo) &
                          ((mem_info_sel == info_type) | mem_bk_erase);

    prim_ram_1p #(
      .Width(DataWidth),
      .Depth(WordsPerInfoBank),
      .DataBitsPerMask(DataWidth)
    ) u_info_mem (
      .clk_i,
      .req_i    (info_mem_req),
      .write_i  (mem_wr),
      .addr_i   (mem_addr[0 +: InfoAddrW]),
      .wdata_i  (mem_wdata),
      .wmask_i  ({DataWidth{1'b1}}),
      .rdata_o  (rd_nom_data_info[info_type]),
      .cfg_i    ('0)
    );
  end

  assign rd_data_info = rd_nom_data_info[info_sel_q];
  assign rd_data_d    = rd_part_q == flash_ctrl_pkg::FlashPartData ? rd_data_main : rd_data_info;

  flash_ctrl_pkg::flash_prog_e unused_prog_type;
  assign unused_prog_type = cmd_q.prog_type;

  logic unused_he;
  assign unused_he = he_i;

endmodule // prim_generic_flash
