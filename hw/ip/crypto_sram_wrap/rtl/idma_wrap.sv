// Copyright 2023 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "idma/typedef.svh"
`include "axi/typedef.svh"

module idma_wrap  import idma_pkg::*; #(
  parameter int unsigned BufferDepth           = 3,
  parameter int unsigned NumAxInFlight         = 3,
  parameter int unsigned TFLenWidth            = 32,
  parameter int unsigned MemSysDepth           = 0,
  parameter int unsigned AXI_MemNumReqOutst    = 1,
  parameter int unsigned AXI_MemLatency        = 0,
  parameter int unsigned WatchDogNumCycles     = 100,
  parameter bit          CombinedShifter       = 1'b0,
  parameter bit          MaskInvalidData       = 1,
  parameter bit          RAWCouplingAvail      = 1,
  parameter bit          HardwareLegalizer     = 1,
  parameter bit          RejectZeroTransfers   = 1,
  parameter bit          ErrorHandling         = 0,
  parameter bit          DmaTracing            = 1,
  parameter bit          PrintFifoInfo         = 1'b0,
  parameter int unsigned RegAddrWidth          = 32,
  parameter int unsigned RegDataWidth          = 32,
  parameter int unsigned AxiAddrWidth          = 64,
  parameter int unsigned AxiDataWidth          = 32,
  parameter int unsigned AxiIdWidth            = 7,
  parameter int unsigned AxiUserWidth          = 1,
  parameter int unsigned StrideWidth           = 32,
  parameter type         axi_req_t             = logic,
  parameter type         axi_rsp_t             = logic,
  parameter type         reg_req_t             = logic,
  parameter type         reg_rsp_t             = logic
) (
  input  logic     clk_i,
  input  logic     rst_ni,
  input  reg_req_t reg_req_i,
  output reg_rsp_t reg_rsp_o,
  output axi_req_t axi_req_host_o,
  input  axi_rsp_t axi_rsp_host_i,
  output axi_req_t axi_req_tcdm_o,
  input  axi_rsp_t axi_rsp_tcdm_i
);

  // dependent parameters
  localparam logic [2:0][31:0] RepWidth = '{default: 32'd32};
  localparam int unsigned IdCounterWidth  = 16;
  localparam int unsigned AxiStrbWidth    = AxiDataWidth / 8;
  localparam int unsigned RegStrbWidth    = RegDataWidth / 8;
  localparam     idma_pkg::error_cap_e ErrorCap = ErrorHandling ? idma_pkg::ERROR_HANDLING :
                                                                  idma_pkg::NO_ERROR_HANDLING;

  localparam int unsigned MstIdWidth = AxiIdWidth + $clog2(2);
  localparam int unsigned SlvIdWidth = AxiIdWidth;

  typedef logic [AxiDataWidth/8-1:0] axi_strb_t;
  typedef logic [AxiDataWidth-1:0]   axi_data_t;
  typedef logic [AxiAddrWidth-1:0]   axi_addr_t;
  typedef logic [AxiUserWidth-1:0]   axi_user_t;
  typedef logic [MstIdWidth-1:0]     axi_id_t;
  typedef logic [SlvIdWidth-1:0]     slv_id_t;

  typedef logic [31:0]               reps_t;
  typedef logic [StrideWidth-1:0]    strides_t;

  // AXI4+ATOP channels typedefs
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(slv_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, axi_data_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, slv_id_t, axi_user_t)

  `AXI_TYPEDEF_AR_CHAN_T(axi_ar_chan_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_AW_CHAN_T(axi_aw_chan_t, axi_addr_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(axi_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(axi_r_chan_t, axi_data_t, axi_id_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(axi_b_chan_t, axi_id_t, axi_user_t)

  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, slv_w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_rsp_t, slv_b_chan_t, slv_r_chan_t)

  //iDMA defines
  `IDMA_TYPEDEF_FULL_REQ_T(idma_req_t, axi_id_t, axi_addr_t, axi_addr_t)
  `IDMA_TYPEDEF_FULL_RSP_T(idma_rsp_t, axi_addr_t)
  `IDMA_TYPEDEF_FULL_ND_REQ_T(idma_nd_req_t, idma_req_t, reps_t, strides_t)

  typedef struct packed {
      slv_ar_chan_t ar_chan;
  } axi_read_meta_channel_t;

  typedef struct packed {
      axi_read_meta_channel_t axi;
  } read_meta_channel_t;

  typedef struct packed {
      slv_aw_chan_t aw_chan;
  } axi_write_meta_channel_t;

  typedef struct packed {
      axi_write_meta_channel_t axi;
  } write_meta_channel_t;

  slv_req_t axi_req_tcdm, axi_req_host;
  slv_rsp_t axi_rsp_tcdm, axi_rsp_host;

  idma_req_t            be_idma_req;
  idma_rsp_t            be_idma_rsp;
  idma_nd_req_t         fe_idma_req;

  idma_pkg::idma_busy_t busy;
  logic me_busy;

  logic fe_req_valid, fe_req_ready;
  logic be_req_valid, be_req_ready;

  logic [IdCounterWidth-1:0] done_id, next_id;

  idma_reg32_3d #(
       .NumRegs        ( 32'd1          ),
       .NumStreams     ( 32'd1          ),
       .IdCounterWidth ( IdCounterWidth ),
       .reg_req_t      ( reg_req_t      ),
       .reg_rsp_t      ( reg_rsp_t      ),
       .dma_req_t      ( idma_nd_req_t  )
  ) idma_frontend (
       .clk_i,
       .rst_ni,
       .dma_ctrl_req_i ( reg_req_i     ),
       .dma_ctrl_rsp_o ( reg_rsp_o     ),
       .dma_req_o      ( fe_idma_req   ),
       .req_valid_o    ( fe_req_valid  ),
       .req_ready_i    ( fe_req_ready  ),
       .next_id_i      ( next_id       ),
       .stream_idx_o   (               ),
       .done_id_i      ( done_id       ),
       .busy_i         ( busy          ),
       .midend_busy_i  ( me_busy       )
  );

  idma_nd_midend #(
      .NumDim        ( 3             ),
      .addr_t        ( axi_addr_t    ),
      .idma_req_t    ( idma_req_t    ),
      .idma_rsp_t    ( idma_rsp_t    ),
      .idma_nd_req_t ( idma_nd_req_t ),
      .RepWidths     ( RepWidth      )
  ) idma_midend_i (
      .clk_i,
      .rst_ni,
      .nd_req_i          ( fe_idma_req  ),
      .nd_req_valid_i    ( fe_req_valid ),
      .nd_req_ready_o    ( fe_req_ready ),
      .nd_rsp_o          (              ),
      .nd_rsp_valid_o    (              ),
      .nd_rsp_ready_i    ( 1'b1         ),
      .burst_req_o       ( be_idma_req  ),
      .burst_req_valid_o ( be_req_valid ),
      .burst_req_ready_i ( be_req_ready ),
      .burst_rsp_i       ( be_idma_rsp  ),
      .burst_rsp_valid_i ( be_rsp_valid ),
      .burst_rsp_ready_o ( be_rsp_ready ),
      .busy_o            ( me_busy      )
  );

  idma_backend_rw_axi #(
      .CombinedShifter      ( CombinedShifter      ),
      .DataWidth            ( AxiDataWidth         ),
      .AddrWidth            ( AxiAddrWidth         ),
      .AxiIdWidth           ( SlvIdWidth           ),
      .UserWidth            ( AxiUserWidth         ),
      .TFLenWidth           ( TFLenWidth           ),
      .MaskInvalidData      ( MaskInvalidData      ),
      .BufferDepth          ( BufferDepth          ),
      .RAWCouplingAvail     ( RAWCouplingAvail     ),
      .HardwareLegalizer    ( HardwareLegalizer    ),
      .RejectZeroTransfers  ( RejectZeroTransfers  ),
      .ErrorCap             ( ErrorCap             ),
      .PrintFifoInfo        ( PrintFifoInfo        ),
      .NumAxInFlight        ( NumAxInFlight        ),
      .MemSysDepth          ( MemSysDepth          ),
      .idma_req_t           ( idma_req_t           ),
      .idma_rsp_t           ( idma_rsp_t           ),
      .idma_eh_req_t        ( idma_eh_req_t        ),
      .idma_busy_t          ( idma_busy_t          ),
      .axi_req_t            ( slv_req_t            ),
      .axi_rsp_t            ( slv_rsp_t            ),
      .write_meta_channel_t ( write_meta_channel_t ),
      .read_meta_channel_t  ( read_meta_channel_t  )
  ) i_idma_backend  (
      .clk_i,
      .rst_ni,
      .testmode_i           ( 1'b0                 ),
      .idma_req_i           ( be_idma_req          ),
      .req_valid_i          ( be_req_valid         ),
      .req_ready_o          ( be_req_ready         ),
      .idma_rsp_o           ( be_idma_rsp          ),
      .rsp_valid_o          ( be_rsp_valid         ),
      .rsp_ready_i          ( be_rsp_ready         ),
      .idma_eh_req_i        ( '0                   ),
      .eh_req_valid_i       ( 1'b0                 ),
      .eh_req_ready_o       (                      ),
      .axi_read_req_o       ( axi_req_tcdm         ),
      .axi_read_rsp_i       ( axi_rsp_tcdm         ),

      .axi_write_req_o      ( axi_req_host         ),
      .axi_write_rsp_i      ( axi_rsp_host         ),
      .busy_o               ( busy                 )
  );

  idma_transfer_id_gen #(
    .IdWidth ( IdCounterWidth )
  ) i_transfer_id_gen (
    .clk_i,
    .rst_ni,
    .issue_i     ( fe_req_valid && fe_req_ready ),
    .retire_i    ( me_busy                      ),
    .next_o      ( next_id                      ),
    .completed_o ( done_id                      )
  );

  // ------------------------------------------------------
  // AXI connection to EXT/TCDM
  // ------------------------------------------------------

  // xbar
  localparam int unsigned NumRules = 2;
  typedef struct packed {
    int unsigned idx;
    logic [AxiAddrWidth-1:0] start_addr;
    logic [AxiAddrWidth-1:0] end_addr;
  } xbar_rule_t;
  xbar_rule_t [NumRules-1:0] addr_map;
  logic [AxiAddrWidth-1:0] host_base_addr;
  logic [AxiAddrWidth-1:0] host_end_addr;
  logic [AxiAddrWidth-1:0] tcdm_base_addr;
  logic [AxiAddrWidth-1:0] tcdm_end_addr;
  assign host_base_addr = 32'h0001_0000;
  assign host_end_addr = 32'hA000_0000;
  assign tcdm_base_addr = 32'hfff0_0000;
  assign tcdm_end_addr = 32'hfff0_8000;
  assign addr_map = '{
    '{ // TCDM
      start_addr: tcdm_base_addr,
      end_addr:   tcdm_end_addr,
      idx:        0
    },
    '{ // SoC low
      start_addr: host_base_addr,
      end_addr:   host_end_addr,
      idx:        1
    }
  };
  localparam int unsigned NumMstPorts = 2;
  localparam int unsigned NumSlvPorts = 2;

  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:                    NumSlvPorts,
    NoMstPorts:                    NumMstPorts,
    MaxMstTrans:                            10,
    MaxSlvTrans:                            10,
    FallThrough:                          1'b0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    PipelineStages:                      32'd0,
    AxiIdWidthSlvPorts:             SlvIdWidth,
    AxiIdUsedSlvPorts:              SlvIdWidth,
    UniqueIds:                            1'b0,
    AxiAddrWidth:                 AxiAddrWidth,
    AxiDataWidth:                 AxiDataWidth,
    NoAddrRules:                      NumRules
  };

  axi_xbar #(
    .Cfg          ( XbarCfg       ),
    .slv_aw_chan_t( slv_aw_chan_t ),
    .mst_aw_chan_t( axi_aw_chan_t ),
    .w_chan_t     ( axi_w_chan_t  ),
    .slv_b_chan_t ( slv_b_chan_t  ),
    .mst_b_chan_t ( axi_b_chan_t  ),
    .slv_ar_chan_t( slv_ar_chan_t ),
    .mst_ar_chan_t( axi_ar_chan_t ),
    .slv_r_chan_t ( slv_r_chan_t  ),
    .mst_r_chan_t ( axi_r_chan_t  ),
    .slv_req_t    ( slv_req_t     ),
    .slv_resp_t   ( slv_rsp_t     ),
    .mst_req_t    ( axi_req_t     ),
    .mst_resp_t   ( axi_rsp_t     ),
    .rule_t       ( xbar_rule_t   )
  ) i_dma_axi_xbar (
    .clk_i                  ( clk_i                              ),
    .rst_ni                 ( rst_ni                             ),
    .test_i                 ( '0                                 ),
    .slv_ports_req_i        ( { axi_req_host  , axi_req_tcdm }   ),
    .slv_ports_resp_o       ( { axi_rsp_host  , axi_rsp_tcdm }   ),
    .mst_ports_req_o        ( { axi_req_host_o, axi_req_tcdm_o } ),
    .mst_ports_resp_i       ( { axi_rsp_host_i, axi_rsp_tcdm_i } ),
    .addr_map_i             ( addr_map                           ),
    .en_default_mst_port_i  ( '0                                 ),
    .default_mst_port_i     ( '0                                 )
  );

endmodule
