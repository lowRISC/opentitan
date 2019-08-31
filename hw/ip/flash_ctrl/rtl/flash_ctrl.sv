// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Faux Flash Controller Module
//
//

module flash_ctrl (
  input        clk_i,
  input        rst_ni,

  // Bus Interface
  input        tlul_pkg::tl_h2d_t tl_i,
  output       tlul_pkg::tl_d2h_t tl_o,

  // Flash Interface
  input        flash_ctrl_pkg::flash_m2c_t flash_i,
  output       flash_ctrl_pkg::flash_c2m_t flash_o,

  // Interrupts
  output logic intr_prog_empty_o, // Program fifo is empty
  output logic intr_prog_lvl_o,   // Program fifo is empty
  output logic intr_rd_full_o,    // Read fifo is full
  output logic intr_rd_lvl_o,     // Read fifo is full
  output logic intr_op_done_o,    // Requested flash operation (wr/erase) done
  output logic intr_op_error_o    // Requested flash operation (wr/erase) done
);

  import flash_ctrl_pkg::*;
  import flash_ctrl_reg_pkg::*;

  localparam int NumBanks = top_pkg::FLASH_BANKS;
  localparam int PagesPerBank = top_pkg::FLASH_PAGES_PER_BANK;
  localparam int WordsPerPage = top_pkg::FLASH_WORDS_PER_PAGE;
  localparam int BankW = top_pkg::FLASH_BKW;
  localparam int PageW = top_pkg::FLASH_PGW;
  localparam int WordW = top_pkg::FLASH_WDW;
  localparam int AllPagesW = BankW + PageW;
  localparam int AddrW = top_pkg::FLASH_AW;
  localparam int DataWidth = top_pkg::FLASH_DW;
  localparam int DataBitWidth = $clog2(DataWidth/8);
  localparam int EraseBitWidth = $bits(flash_erase_op_e);
  localparam int FifoDepth = 16;
  localparam int FifoDepthW = $clog2(FifoDepth+1);
  localparam int MpRegions = 8;


  flash_ctrl_reg2hw_t reg2hw;
  flash_ctrl_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t tl_fifo_h2d [2];
  tlul_pkg::tl_d2h_t tl_fifo_d2h [2];

  //==============================================================================

  // Register module
  flash_ctrl_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .tl_win_o (tl_fifo_h2d),
    .tl_win_i (tl_fifo_d2h),

    .reg2hw,
    .hw2reg
  );

  // FIFO Connections
  logic                 prog_fifo_wready;
  logic                 prog_fifo_rvalid;
  logic                 prog_fifo_wvalid;
  logic                 prog_fifo_ren;
  logic [DataWidth-1:0] prog_fifo_wdata;
  logic [DataWidth-1:0] prog_fifo_rdata;
  logic [FifoDepthW-1:0] prog_fifo_depth;
  logic                 rd_fifo_wready;
  logic                 rd_fifo_rvalid;
  logic                 rd_fifo_wen;
  logic                 rd_fifo_ren;
  logic [DataWidth-1:0] rd_fifo_wdata;
  logic [DataWidth-1:0] rd_fifo_rdata;
  logic [FifoDepthW-1:0] rd_fifo_depth;

  // Program Control Connections
  logic prog_flash_req;
  logic prog_flash_ovfl;
  logic [AddrW-1:0] prog_flash_addr;

  // Read Control Connections
  logic rd_flash_req;
  logic rd_flash_ovfl;
  logic [AddrW-1:0] rd_flash_addr;

  // Erase Control Connections
  logic erase_flash_req;
  logic [AddrW-1:0] erase_flash_addr;
  logic [EraseBitWidth-1:0] erase_flash_type;

  // Done / Error signaling from ctrl modules
  logic [2:0] ctrl_done, ctrl_err;

  // Flash Memory Protection Connections
  logic flash_req;
  logic flash_rd_done, flash_prog_done, flash_erase_done;
  logic flash_error;
  logic [AddrW-1:0] flash_addr;
  logic [DataWidth-1:0] flash_prog_data;
  logic [DataWidth-1:0] flash_rd_data;
  logic init_busy;
  logic rd_op;
  logic prog_op;
  logic erase_op;
  logic [AllPagesW-1:0] err_page;
  logic [BankW-1:0] err_bank;

  assign rd_op = reg2hw.control.op.q == FlashRead;
  assign prog_op = reg2hw.control.op.q == FlashProg;
  assign erase_op = reg2hw.control.op.q == FlashErase;

  // Program FIFO
  // Since the program and read FIFOs are never used at the same time, it should really be one
  // FIFO with muxed inputs and outputs.  This should be addressed once the flash integration
  // strategy has been identified
  flash_tlul_to_fifo #(
    .Size(DataWidth),
    .Dir(0)
  ) u_to_prog_fifo (
    .clk_i,
    .rst_ni,
    .tl_i         (tl_fifo_h2d[0]),
    .tl_o         (tl_fifo_d2h[0]),
    .fifo_wen_o   (prog_fifo_wvalid),
    .fifo_wdata_o (prog_fifo_wdata),
    .fifo_full_i  (~prog_fifo_wready),
    .fifo_ren_o   (),
    .fifo_empty_i (1'b1),
    .fifo_rdata_i ('0)
  );

  prim_fifo_sync #(
    .Width(DataWidth),
    .Depth(FifoDepth)
  ) u_prog_fifo (
    .clk_i,
    .rst_ni (rst_ni & ~reg2hw.control.fifo_rst.q),
    .wvalid (prog_fifo_wvalid),
    .wready (prog_fifo_wready),
    .wdata  (prog_fifo_wdata),
    .depth  (prog_fifo_depth),
    .rvalid (prog_fifo_rvalid),
    .rready (prog_fifo_ren),
    .rdata  (prog_fifo_rdata)
  );

  // Program handler is consumer of prog_fifo
  flash_prog_ctrl #(
    .DataW(DataWidth),
    .AddrW(AddrW)
  ) u_flash_prog_ctrl (
    .clk_i,
    .rst_ni,

    // Software Interface
    .op_start_i     (reg2hw.control.start.q & prog_op),
    .op_num_words_i (reg2hw.control.num.q),
    .op_done_o      (ctrl_done[0]),
    .op_err_o       (ctrl_err[0]),
    .op_addr_i      (reg2hw.addr.q[DataBitWidth +: AddrW]),

    // FIFO Interface
    .data_i         (prog_fifo_rdata),
    .data_rdy_i     (prog_fifo_rvalid),
    .data_rd_o      (prog_fifo_ren),

    // Flash Macro Interface
    .flash_req_o    (prog_flash_req),
    .flash_addr_o   (prog_flash_addr),
    .flash_ovfl_o   (prog_flash_ovfl),
    .flash_data_o   (flash_prog_data),
    .flash_done_i   (flash_prog_done),
    .flash_error_i  (flash_error)
  );

  // Read FIFO
  flash_tlul_to_fifo #(
    .Size(DataWidth),
    .Dir(1)      //change this to something in package file later
  ) u_to_rd_fifo (
    .clk_i,
    .rst_ni,
    .tl_i         (tl_fifo_h2d[1]),
    .tl_o         (tl_fifo_d2h[1]),
    .fifo_wen_o   (),
    .fifo_wdata_o (),
    .fifo_full_i  (1'b1),
    .fifo_ren_o   (rd_fifo_ren),
    .fifo_empty_i (~rd_fifo_rvalid),
    .fifo_rdata_i (rd_fifo_rdata)
    );

  prim_fifo_sync #(
    .Width(DataWidth),
    .Depth(FifoDepth)
  ) u_rd_fifo (
    .clk_i,
    .rst_ni (rst_ni & ~reg2hw.control.fifo_rst.q),
    .wvalid (rd_fifo_wen),
    .wready (rd_fifo_wready),
    .wdata  (rd_fifo_wdata),
    .depth  (rd_fifo_depth),
    .rvalid (rd_fifo_rvalid),
    .rready (rd_fifo_ren),
    .rdata  (rd_fifo_rdata)
  );

  // Read handler is consumer of rd_fifo
  flash_rd_ctrl #(
    .DataW(DataWidth),
    .AddrW(AddrW)
  ) u_flash_rd_ctrl (
    .clk_i,
    .rst_ni,

    // Software Interface
    .op_start_i     (reg2hw.control.start.q & rd_op),
    .op_num_words_i (reg2hw.control.num.q),
    .op_done_o      (ctrl_done[1]),
    .op_err_o       (ctrl_err[1]),
    .op_addr_i      (reg2hw.addr.q[DataBitWidth +: AddrW]),

    // FIFO Interface
    .data_rdy_i     (rd_fifo_wready),
    .data_o         (rd_fifo_wdata),
    .data_wr_o      (rd_fifo_wen),

    // Flash Macro Interface
    .flash_req_o    (rd_flash_req),
    .flash_addr_o   (rd_flash_addr),
    .flash_ovfl_o   (rd_flash_ovfl),
    .flash_data_i   (flash_rd_data),
    .flash_done_i   (flash_rd_done),
    .flash_error_i  (flash_error)
  );

  // Erase handler does not consume fifo
  flash_erase_ctrl #(
    .AddrW(AddrW),
    .PagesPerBank(PagesPerBank),
    .WordsPerPage(WordsPerPage),
    .EraseBitWidth(EraseBitWidth)
  ) u_flash_erase_ctrl (
    // Software Interface
    .op_start_i     (reg2hw.control.start.q & erase_op),
    .op_type_i      (reg2hw.control.erase_sel.q),
    .op_done_o      (ctrl_done[2]),
    .op_err_o       (ctrl_err[2]),
    .op_addr_i      (reg2hw.addr.q[DataBitWidth +: AddrW]),

    // Flash Macro Interface
    .flash_req_o    (erase_flash_req),
    .flash_addr_o   (erase_flash_addr),
    .flash_op_o     (erase_flash_type),
    .flash_done_i   (flash_erase_done),
    .flash_error_i  (flash_error)
  );

  // Final muxing to flash macro module
  always_comb begin
    unique case (reg2hw.control.op.q)
      FlashRead: begin
        flash_req = rd_flash_req;
        flash_addr = rd_flash_addr;
      end
      FlashProg: begin
        flash_req = prog_flash_req;
        flash_addr = prog_flash_addr;
      end
      FlashErase: begin
        flash_req = erase_flash_req;
        flash_addr = erase_flash_addr;
      end
      default: begin
        flash_req = 1'b0;
        flash_addr  = '0;
      end
    endcase // unique case (flash_op_e'(reg2hw.control.op.q))
  end

  // extra region is the default region
  flash_mp_region_t region_cfgs[MpRegions+1];
  logic [NumBanks-1:0] bank_cfgs;

  // TODO: Templatize the assigments below
  assign bank_cfgs[0] = reg2hw.mp_bank_cfg.erase_en0.q;
  assign bank_cfgs[1] = reg2hw.mp_bank_cfg.erase_en1.q;

  assign region_cfgs[0].base_page = reg2hw.mp_region_cfg0.base0.q;
  assign region_cfgs[0].size      = reg2hw.mp_region_cfg0.size0.q;
  assign region_cfgs[0].en        = reg2hw.mp_region_cfg0.en0.q;
  assign region_cfgs[0].rd_en     = reg2hw.mp_region_cfg0.rd_en0.q;
  assign region_cfgs[0].prog_en   = reg2hw.mp_region_cfg0.prog_en0.q;
  assign region_cfgs[0].erase_en  = reg2hw.mp_region_cfg0.erase_en0.q;

  assign region_cfgs[1].base_page = reg2hw.mp_region_cfg1.base1.q;
  assign region_cfgs[1].size      = reg2hw.mp_region_cfg1.size1.q;
  assign region_cfgs[1].en        = reg2hw.mp_region_cfg1.en1.q;
  assign region_cfgs[1].rd_en     = reg2hw.mp_region_cfg1.rd_en1.q;
  assign region_cfgs[1].prog_en   = reg2hw.mp_region_cfg1.prog_en1.q;
  assign region_cfgs[1].erase_en  = reg2hw.mp_region_cfg1.erase_en1.q;

  assign region_cfgs[2].base_page = reg2hw.mp_region_cfg2.base2.q;
  assign region_cfgs[2].size      = reg2hw.mp_region_cfg2.size2.q;
  assign region_cfgs[2].en        = reg2hw.mp_region_cfg2.en2.q;
  assign region_cfgs[2].rd_en     = reg2hw.mp_region_cfg2.rd_en2.q;
  assign region_cfgs[2].prog_en   = reg2hw.mp_region_cfg2.prog_en2.q;
  assign region_cfgs[2].erase_en  = reg2hw.mp_region_cfg2.erase_en2.q;

  assign region_cfgs[3].base_page = reg2hw.mp_region_cfg3.base3.q;
  assign region_cfgs[3].size      = reg2hw.mp_region_cfg3.size3.q;
  assign region_cfgs[3].en        = reg2hw.mp_region_cfg3.en3.q;
  assign region_cfgs[3].rd_en     = reg2hw.mp_region_cfg3.rd_en3.q;
  assign region_cfgs[3].prog_en   = reg2hw.mp_region_cfg3.prog_en3.q;
  assign region_cfgs[3].erase_en  = reg2hw.mp_region_cfg3.erase_en3.q;

  assign region_cfgs[4].base_page = reg2hw.mp_region_cfg4.base4.q;
  assign region_cfgs[4].size      = reg2hw.mp_region_cfg4.size4.q;
  assign region_cfgs[4].en        = reg2hw.mp_region_cfg4.en4.q;
  assign region_cfgs[4].rd_en     = reg2hw.mp_region_cfg4.rd_en4.q;
  assign region_cfgs[4].prog_en   = reg2hw.mp_region_cfg4.prog_en4.q;
  assign region_cfgs[4].erase_en  = reg2hw.mp_region_cfg4.erase_en4.q;

  assign region_cfgs[5].base_page = reg2hw.mp_region_cfg5.base5.q;
  assign region_cfgs[5].size      = reg2hw.mp_region_cfg5.size5.q;
  assign region_cfgs[5].en        = reg2hw.mp_region_cfg5.en5.q;
  assign region_cfgs[5].rd_en     = reg2hw.mp_region_cfg5.rd_en5.q;
  assign region_cfgs[5].prog_en   = reg2hw.mp_region_cfg5.prog_en5.q;
  assign region_cfgs[5].erase_en  = reg2hw.mp_region_cfg5.erase_en5.q;

  assign region_cfgs[6].base_page = reg2hw.mp_region_cfg6.base6.q;
  assign region_cfgs[6].size      = reg2hw.mp_region_cfg6.size6.q;
  assign region_cfgs[6].en        = reg2hw.mp_region_cfg6.en6.q;
  assign region_cfgs[6].rd_en     = reg2hw.mp_region_cfg6.rd_en6.q;
  assign region_cfgs[6].prog_en   = reg2hw.mp_region_cfg6.prog_en6.q;
  assign region_cfgs[6].erase_en  = reg2hw.mp_region_cfg6.erase_en6.q;

  assign region_cfgs[7].base_page = reg2hw.mp_region_cfg7.base7.q;
  assign region_cfgs[7].size      = reg2hw.mp_region_cfg7.size7.q;
  assign region_cfgs[7].en        = reg2hw.mp_region_cfg7.en7.q;
  assign region_cfgs[7].rd_en     = reg2hw.mp_region_cfg7.rd_en7.q;
  assign region_cfgs[7].prog_en   = reg2hw.mp_region_cfg7.prog_en7.q;
  assign region_cfgs[7].erase_en  = reg2hw.mp_region_cfg7.erase_en7.q;

  assign region_cfgs[8].base_page = '0;
  assign region_cfgs[8].size      = {AllPagesW{1'b1}};
  assign region_cfgs[8].en        = 1'b1;
  assign region_cfgs[8].rd_en     = reg2hw.default_region.rd_en.q;
  assign region_cfgs[8].prog_en   = reg2hw.default_region.prog_en.q;
  assign region_cfgs[8].erase_en  = reg2hw.default_region.erase_en.q;

  // Flash memory protection
  flash_mp #(
    .MpRegions(MpRegions),
    .NumBanks(NumBanks),
    .AllPagesW(AllPagesW)
  ) u_flash_mp (
    .clk_i,
    .rst_ni,

    // sw configuration
    .region_cfgs_i(region_cfgs),
    .bank_cfgs_i(bank_cfgs),

    // read / prog / erase controls
    .req_i(flash_req),
    .req_addr_i(flash_addr[WordW +: AllPagesW]),
    .addr_ovfl_i(rd_flash_ovfl | prog_flash_ovfl),
    .req_bk_i(flash_addr[WordW + PageW +: BankW]),
    .rd_i(rd_op),
    .prog_i(prog_op),
    .pg_erase_i(erase_op & (erase_flash_type == PageErase)),
    .bk_erase_i(erase_op & (erase_flash_type == BankErase)),
    .rd_done_o(flash_rd_done),
    .prog_done_o(flash_prog_done),
    .erase_done_o(flash_erase_done),
    .error_o(flash_error),
    .err_addr_o(err_page),
    .err_bank_o(err_bank),

    // flash phy interface
    .req_o(flash_o.req),
    .rd_o(flash_o.rd),
    .prog_o(flash_o.prog),
    .pg_erase_o(flash_o.pg_erase),
    .bk_erase_o(flash_o.bk_erase),
    .rd_done_i(flash_i.rd_done),
    .prog_done_i(flash_i.prog_done),
    .erase_done_i(flash_i.erase_done)
  );


  assign hw2reg.op_status.done.d = 1'b1;
  assign hw2reg.op_status.done.de = |ctrl_done;
  assign hw2reg.op_status.err.d = 1'b1;
  assign hw2reg.op_status.err.de = |ctrl_err;
  assign hw2reg.status.rd_full.d = ~rd_fifo_wready;
  assign hw2reg.status.rd_empty.d = ~rd_fifo_rvalid;
  assign hw2reg.status.prog_full.d = ~prog_fifo_wready;
  assign hw2reg.status.prog_empty.d = ~prog_fifo_rvalid;
  assign hw2reg.status.init_wip.d = init_busy;
  assign hw2reg.status.error_page.d = err_page;
  assign hw2reg.status.error_bank.d = err_bank;
  assign hw2reg.control.start.d = 1'b0;
  assign hw2reg.control.start.de = |ctrl_done;

  // Flash Interface
  assign flash_o.addr = flash_addr;
  assign flash_o.prog_data = flash_prog_data;
  assign flash_rd_data = flash_i.rd_data;
  assign init_busy = flash_i.init_busy;

  // Interrupts
  assign intr_prog_empty_o = reg2hw.intr_enable.prog_empty.q & reg2hw.intr_state.prog_empty.q;
  assign intr_prog_lvl_o = reg2hw.intr_enable.prog_lvl.q & reg2hw.intr_state.prog_lvl.q;
  assign intr_rd_full_o = reg2hw.intr_enable.rd_full.q & reg2hw.intr_state.rd_full.q;
  assign intr_rd_lvl_o = reg2hw.intr_enable.rd_lvl.q & reg2hw.intr_state.rd_lvl.q;
  assign intr_op_done_o = reg2hw.intr_enable.op_done.q & reg2hw.intr_state.op_done.q;
  assign intr_op_error_o = reg2hw.intr_enable.op_error.q & reg2hw.intr_state.op_error.q;

  assign hw2reg.intr_state.prog_empty.d  = 1'b1;
  assign hw2reg.intr_state.prog_empty.de = ~prog_fifo_rvalid  |
                                           (reg2hw.intr_test.prog_empty.qe  &
                                           reg2hw.intr_test.prog_empty.q);

  assign hw2reg.intr_state.prog_lvl.d  = 1'b1;
  assign hw2reg.intr_state.prog_lvl.de = (reg2hw.fifo_lvl.prog.q == prog_fifo_depth)  |
                                         (reg2hw.intr_test.prog_lvl.qe  &
                                         reg2hw.intr_test.prog_lvl.q);

  assign hw2reg.intr_state.rd_full.d  = 1'b1;
  assign hw2reg.intr_state.rd_full.de = ~rd_fifo_wready |
                                        (reg2hw.intr_test.rd_full.qe  &
                                        reg2hw.intr_test.rd_full.q);

  assign hw2reg.intr_state.rd_lvl.d  = 1'b1;
  assign hw2reg.intr_state.rd_lvl.de = (reg2hw.fifo_lvl.rd.q == rd_fifo_depth)  |
                                       (reg2hw.intr_test.rd_lvl.qe  &
                                       reg2hw.intr_test.rd_lvl.q);


  assign hw2reg.intr_state.op_done.d  = 1'b1;
  assign hw2reg.intr_state.op_done.de = |ctrl_done  |
                                        (reg2hw.intr_test.op_done.qe  &
                                        reg2hw.intr_test.op_done.q);

  assign hw2reg.intr_state.op_error.d  = 1'b1;
  assign hw2reg.intr_state.op_error.de = |ctrl_err  |
                                        (reg2hw.intr_test.op_error.qe  &
                                        reg2hw.intr_test.op_error.q);



  // Unused bits
  logic [DataBitWidth-1:0] unused_byte_sel;
  logic [31-AddrW:0] unused_higher_addr_bits;
  logic [31:0] unused_scratch;


  // Unused signals
  assign unused_byte_sel = reg2hw.addr.q[DataBitWidth-1:0];
  assign unused_higher_addr_bits = reg2hw.addr.q[31:AddrW];
  assign unused_scratch = reg2hw.scratch;



endmodule
