// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Top-level debug module (DM)
//
// This module implements the RISC-V debug specification version 0.13,
//
// This toplevel wraps the PULP debug module available from
// https://github.com/pulp-platform/riscv-dbg to match the needs of
// the TL-UL-based lowRISC chip design.

`include "prim_assert.sv"

module rv_dm #(
  parameter int                 NrHarts = 1,
  parameter logic [31:0]        IdcodeValue = 32'h 0000_0001
) (
  input  logic                  clk_i,       // clock
  input  logic                  rst_ni,      // asynchronous reset active low, connect PoR
                                             // here, not the system reset
  input  logic                  testmode_i,
  output logic                  ndmreset_o,  // non-debug module reset
  output logic                  dmactive_o,  // debug module is active
  output logic [NrHarts-1:0]    debug_req_o, // async debug request
  input  logic [NrHarts-1:0]    unavailable_i, // communicate whether the hart is unavailable
                                               // (e.g.: power down)

  // bus device with debug memory, for an execution based technique
  input  tlul_pkg::tl_h2d_t tl_d_i,
  output tlul_pkg::tl_d2h_t tl_d_o,

  // bus host, for system bus accesses
  output tlul_pkg::tl_h2d_t  tl_h_o,
  input  tlul_pkg::tl_d2h_t  tl_h_i,

  input  logic               tck_i,           // JTAG test clock pad
  input  logic               tms_i,           // JTAG test mode select pad
  input  logic               trst_ni,         // JTAG test reset pad
  input  logic               td_i,            // JTAG test data input pad
  output logic               td_o,            // JTAG test data output pad
  output logic               tdo_oe_o         // Data out output enable
);

  `ASSERT_INIT(paramCheckNrHarts, NrHarts > 0)

  // Currently only 32 bit busses are supported by our TL-UL IP
  localparam int BusWidth = 32;
  // all harts have contiguous IDs
  localparam logic [NrHarts-1:0] SelectableHarts = {NrHarts{1'b1}};

  // Debug CSRs
  dm::hartinfo_t [NrHarts-1:0]      hartinfo;
  logic [NrHarts-1:0]               halted;
  // logic [NrHarts-1:0]               running;
  logic [NrHarts-1:0]               resumeack;
  logic [NrHarts-1:0]               haltreq;
  logic [NrHarts-1:0]               resumereq;
  logic                             clear_resumeack;
  logic                             cmd_valid;
  dm::command_t                     cmd;

  logic                             cmderror_valid;
  dm::cmderr_e                      cmderror;
  logic                             cmdbusy;
  logic [dm::ProgBufSize-1:0][31:0] progbuf;
  logic [dm::DataCount-1:0][31:0]   data_csrs_mem;
  logic [dm::DataCount-1:0][31:0]   data_mem_csrs;
  logic                             data_valid;
  logic [19:0]                      hartsel;
  // System Bus Access Module
  logic [BusWidth-1:0]              sbaddress_csrs_sba;
  logic [BusWidth-1:0]              sbaddress_sba_csrs;
  logic                             sbaddress_write_valid;
  logic                             sbreadonaddr;
  logic                             sbautoincrement;
  logic [2:0]                       sbaccess;
  logic                             sbreadondata;
  logic [BusWidth-1:0]              sbdata_write;
  logic                             sbdata_read_valid;
  logic                             sbdata_write_valid;
  logic [BusWidth-1:0]              sbdata_read;
  logic                             sbdata_valid;
  logic                             sbbusy;
  logic                             sberror_valid;
  logic [2:0]                       sberror;

  dm::dmi_req_t  dmi_req;
  dm::dmi_resp_t dmi_rsp;
  logic dmi_req_valid, dmi_req_ready;
  logic dmi_rsp_valid, dmi_rsp_ready;
  logic dmi_rst_n;

  // static debug hartinfo
  localparam dm::hartinfo_t DebugHartInfo = '{
    zero1:      '0,
    nscratch:   2, // Debug module needs at least two scratch regs
    zero0:      0,
    dataaccess: 1'b1, // data registers are memory mapped in the debugger
    datasize:   dm::DataCount,
    dataaddr:   dm::DataAddr
  };
  for (genvar i = 0; i < NrHarts; i++) begin : gen_dm_hart_ctrl
    assign hartinfo[i] = DebugHartInfo;
  end

  dm_csrs #(
    .NrHarts(NrHarts),
    .BusWidth(BusWidth),
    .SelectableHarts(SelectableHarts)
  ) i_dm_csrs (
    .clk_i                   ( clk_i                 ),
    .rst_ni                  ( rst_ni                ),
    .testmode_i              ( testmode_i            ),
    .dmi_rst_ni              ( dmi_rst_n             ),
    .dmi_req_valid_i         ( dmi_req_valid         ),
    .dmi_req_ready_o         ( dmi_req_ready         ),
    .dmi_req_i               ( dmi_req               ),
    .dmi_resp_valid_o        ( dmi_rsp_valid         ),
    .dmi_resp_ready_i        ( dmi_rsp_ready         ),
    .dmi_resp_o              ( dmi_rsp               ),
    .ndmreset_o              ( ndmreset_o            ),
    .dmactive_o              ( dmactive_o            ),
    .hartsel_o               ( hartsel               ),
    .hartinfo_i              ( hartinfo              ),
    .halted_i                ( halted                ),
    .unavailable_i,
    .resumeack_i             ( resumeack             ),
    .haltreq_o               ( haltreq               ),
    .resumereq_o             ( resumereq             ),
    .clear_resumeack_o       ( clear_resumeack       ),
    .cmd_valid_o             ( cmd_valid             ),
    .cmd_o                   ( cmd                   ),
    .cmderror_valid_i        ( cmderror_valid        ),
    .cmderror_i              ( cmderror              ),
    .cmdbusy_i               ( cmdbusy               ),
    .progbuf_o               ( progbuf               ),
    .data_i                  ( data_mem_csrs         ),
    .data_valid_i            ( data_valid            ),
    .data_o                  ( data_csrs_mem         ),
    .sbaddress_o             ( sbaddress_csrs_sba    ),
    .sbaddress_i             ( sbaddress_sba_csrs    ),
    .sbaddress_write_valid_o ( sbaddress_write_valid ),
    .sbreadonaddr_o          ( sbreadonaddr          ),
    .sbautoincrement_o       ( sbautoincrement       ),
    .sbaccess_o              ( sbaccess              ),
    .sbreadondata_o          ( sbreadondata          ),
    .sbdata_o                ( sbdata_write          ),
    .sbdata_read_valid_o     ( sbdata_read_valid     ),
    .sbdata_write_valid_o    ( sbdata_write_valid    ),
    .sbdata_i                ( sbdata_read           ),
    .sbdata_valid_i          ( sbdata_valid          ),
    .sbbusy_i                ( sbbusy                ),
    .sberror_valid_i         ( sberror_valid         ),
    .sberror_i               ( sberror               )
  );

  logic                   master_req;
  logic   [BusWidth-1:0]  master_add;
  logic                   master_we;
  logic   [BusWidth-1:0]  master_wdata;
  logic [BusWidth/8-1:0]  master_be;
  logic                   master_gnt;
  logic                   master_r_valid;
  logic   [BusWidth-1:0]  master_r_rdata;

  dm_sba #(
    .BusWidth(BusWidth)
  ) i_dm_sba (
    .clk_i                   ( clk_i                 ),
    .rst_ni                  ( rst_ni                ),
    .master_req_o            ( master_req            ),
    .master_add_o            ( master_add            ),
    .master_we_o             ( master_we             ),
    .master_wdata_o          ( master_wdata          ),
    .master_be_o             ( master_be             ),
    .master_gnt_i            ( master_gnt            ),
    .master_r_valid_i        ( master_r_valid        ),
    .master_r_rdata_i        ( master_r_rdata        ),
    .dmactive_i              ( dmactive_o            ),
    .sbaddress_i             ( sbaddress_csrs_sba    ),
    .sbaddress_o             ( sbaddress_sba_csrs    ),
    .sbaddress_write_valid_i ( sbaddress_write_valid ),
    .sbreadonaddr_i          ( sbreadonaddr          ),
    .sbautoincrement_i       ( sbautoincrement       ),
    .sbaccess_i              ( sbaccess              ),
    .sbreadondata_i          ( sbreadondata          ),
    .sbdata_i                ( sbdata_write          ),
    .sbdata_read_valid_i     ( sbdata_read_valid     ),
    .sbdata_write_valid_i    ( sbdata_write_valid    ),
    .sbdata_o                ( sbdata_read           ),
    .sbdata_valid_o          ( sbdata_valid          ),
    .sbbusy_o                ( sbbusy                ),
    .sberror_valid_o         ( sberror_valid         ),
    .sberror_o               ( sberror               )
  );

  tlul_adapter_host #(
    .AW(BusWidth),
    .DW(BusWidth)
  ) tl_adapter_host_sba (
    .clk_i,
    .rst_ni,
    .req_i        (master_req),
    .gnt_o        (master_gnt),
    .addr_i       (master_add),
    .we_i         (master_we),
    .wdata_i      (master_wdata),
    .be_i         (master_be),
    .size_i       (sbaccess[1:0]),
    .valid_o      (master_r_valid),
    .rdata_o      (master_r_rdata),
    .tl_o         (tl_h_o),
    .tl_i         (tl_h_i)
  );

  localparam int unsigned AddressWidthWords = BusWidth - $clog2(BusWidth/8);

  logic                         req;
  logic                         we;
  logic [BusWidth/8-1:0]        be;
  logic   [BusWidth-1:0]        wdata;
  logic   [BusWidth-1:0]        rdata;
  logic                         rvalid;

  logic [BusWidth-1:0]          addr_b;
  logic [AddressWidthWords-1:0] addr_w;

  // TODO: The tlul_adapter_sram give us a bitwise write mask currently,
  // but dm_mem only supports byte write masks. Disable sub-word access in the
  // adapter for now until we figure out a good strategy to deal with this.
  assign be = {BusWidth/8{1'b1}};

  assign addr_b = {addr_w, {$clog2(BusWidth/8){1'b0}}};

  dm_mem #(
    .NrHarts(NrHarts),
    .BusWidth(BusWidth),
    .SelectableHarts(SelectableHarts)
  ) i_dm_mem (
    .clk_i                   ( clk_i                 ),
    .rst_ni                  ( rst_ni                ),
    .debug_req_o             ( debug_req_o           ),
    .hartsel_i               ( hartsel               ),
    .haltreq_i               ( haltreq               ),
    .resumereq_i             ( resumereq             ),
    .clear_resumeack_i       ( clear_resumeack       ),
    .halted_o                ( halted                ),
    .resuming_o              ( resumeack             ),
    .cmd_valid_i             ( cmd_valid             ),
    .cmd_i                   ( cmd                   ),
    .cmderror_valid_o        ( cmderror_valid        ),
    .cmderror_o              ( cmderror              ),
    .cmdbusy_o               ( cmdbusy               ),
    .progbuf_i               ( progbuf               ),
    .data_i                  ( data_csrs_mem         ),
    .data_o                  ( data_mem_csrs         ),
    .data_valid_o            ( data_valid            ),
    .req_i                   ( req                   ),
    .we_i                    ( we                    ),
    .addr_i                  ( addr_b                ),
    .wdata_i                 ( wdata                 ),
    .be_i                    ( be                    ),
    .rdata_o                 ( rdata                 )
  );

  // Bound-in DPI module replaces the TAP
`ifndef DMIDirectTAP
  // JTAG TAP
  dmi_jtag #(
    .IdcodeValue    (IdcodeValue)
  ) dap (
    .clk_i            (clk_i),
    .rst_ni           (rst_ni),
    .testmode_i       (testmode_i),

    .dmi_rst_no       (dmi_rst_n),
    .dmi_req_o        (dmi_req),
    .dmi_req_valid_o  (dmi_req_valid),
    .dmi_req_ready_i  (dmi_req_ready),

    .dmi_resp_i       (dmi_rsp      ),
    .dmi_resp_ready_o (dmi_rsp_ready),
    .dmi_resp_valid_i (dmi_rsp_valid),

    //JTAG
    .tck_i,
    .tms_i,
    .trst_ni,
    .td_i,
    .td_o,
    .tdo_oe_o
  );
`endif

  tlul_adapter_sram #(
    .SramAw(AddressWidthWords),
    .SramDw(BusWidth),
    .Outstanding(1),
    .ByteAccess(0)
  ) tl_adapter_device_mem (
    .clk_i,
    .rst_ni,

    .req_o    (req),
    .gnt_i    (1'b1),
    .we_o     (we),
    .addr_o   (addr_w),
    .wdata_o  (wdata),
    .wmask_o  (),
    .rdata_i  (rdata),
    .rvalid_i (rvalid),
    .rerror_i (2'b00),

    .tl_o     (tl_d_o),
    .tl_i     (tl_d_i)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvalid <= '0;
    end else begin
      rvalid <= req & ~we;
    end
  end

endmodule
