// Copyright 2022 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

/* OpenTitan iDMA Core Wrapper
 * Author: Maicol Ciani <maicol.ciani@unibo.it>
 */

`include "axi/assign.svh"
`include "axi/typedef.svh"
`include "idma/typedef.svh"
`include "register_interface/typedef.svh"

module idma_wrap #(
  parameter int unsigned AxiAddrWidth          = 64,
  parameter int unsigned AxiDataWidth          = 32,
  parameter int unsigned AxiIdWidth            = 8,
  parameter int unsigned AxiUserWidth          = 1,
  parameter int unsigned NUM_STREAMS           = 1,
  parameter int unsigned NB_OUTSND_BURSTS      = 8,
  parameter int unsigned GLOBAL_QUEUE_DEPTH    = 16,
  parameter type         axi_req_t             = logic,
  parameter type         axi_rsp_t             = logic,
  parameter type         reg_req_t             = logic,
  parameter type         reg_rsp_t             = logic
) (
  input logic         clk_i,
  input logic         rst_ni,
  output logic        term_event_o,
  output logic        term_irq_o,
  output logic        busy_o,
  input  reg_req_t    reg_req_i,
  output reg_rsp_t    reg_rsp_o,
  output axi_req_t    axi_req_host_o,
  input  axi_rsp_t    axi_rsp_host_i,
  output axi_req_t    axi_req_tcdm_o,
  input  axi_rsp_t    axi_rsp_tcdm_i
);

  logic test_mode_i;
  assign test_mode_i = 1'b0;

  localparam int unsigned NumRegs = 1;
  localparam int unsigned MstIdxWidth = AxiIdWidth;
  localparam int unsigned SlvIdxWidth = AxiIdWidth - $clog2(NUM_STREAMS);

  // AXI4+ATOP types
  typedef logic [AxiAddrWidth-1:0]   addr_t;
  typedef logic [AxiDataWidth-1:0]   data_t;
  typedef logic [SlvIdxWidth-1:0]      slv_id_t;
  typedef logic [MstIdxWidth-1:0]      mst_id_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  typedef logic [AxiUserWidth-1:0]   user_t;
  // AXI4+ATOP channels typedefs
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, slv_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, mst_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, addr_t, mst_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, data_t, slv_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, data_t, mst_id_t, user_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)
  // BUS definitions
  slv_req_t  [NUM_STREAMS-1:0] dma_req;
  slv_resp_t [NUM_STREAMS-1:0] dma_rsp;

  // iDMA struct definitions
  localparam int unsigned TFLenWidth  = AxiAddrWidth;
  localparam int unsigned NumDim      = 2; // Support 2D midend for 2D transfers
  localparam int unsigned RepWidth    = 32;
  localparam int unsigned StrideWidth = 32;
  typedef logic [TFLenWidth-1:0]  tf_len_t;
  typedef logic [RepWidth-1:0]    reps_t;
  typedef logic [StrideWidth-1:0] strides_t;

  // iDMA request / response types
  `IDMA_TYPEDEF_FULL_REQ_T(idma_req_t, slv_id_t, addr_t, tf_len_t)
  `IDMA_TYPEDEF_FULL_RSP_T(idma_rsp_t, addr_t)

  // iDMA ND request
  `IDMA_TYPEDEF_FULL_ND_REQ_T(idma_nd_req_t, idma_req_t, reps_t, strides_t)

  idma_nd_req_t twod_req, twod_req_queue;
  idma_req_t burst_req;
  idma_rsp_t idma_rsp;

  logic fe_valid, twod_queue_valid, be_valid, be_rsp_valid;
  logic fe_ready, twod_queue_ready, be_ready, be_rsp_ready;
  logic trans_complete, midend_busy;
  idma_pkg::idma_busy_t idma_busy;

  // ------------------------------------------------------
  // FRONTEND
  // ------------------------------------------------------

  idma_reg32_2d_frontend #(
    .NumRegs        ( NumRegs        ),
    .IdCounterWidth ( 28             ),
    .dma_regs_req_t ( reg_req_t      ),
    .dma_regs_rsp_t ( reg_rsp_t      ),
    .burst_req_t    ( idma_nd_req_t  )
  ) i_idma_reg32_2d_frontend (
    .clk_i,
    .rst_ni,
    .dma_ctrl_req_i   ( reg_req_i      ),
    .dma_ctrl_rsp_o   ( reg_rsp_o      ),
    .burst_req_o      ( twod_req       ),
    .valid_o          ( fe_valid       ),
    .ready_i          ( fe_ready       ),
    .backend_idle_i   ( ~busy_o        ),
    .trans_complete_i ( trans_complete )
  );

  // interrupts and events
  assign term_event_o    = |trans_complete ? '1 : '0;
  assign term_irq_o      = '0;

  assign busy_o = midend_busy | |idma_busy;

  // ------------------------------------------------------
  // MIDEND
  // ------------------------------------------------------

  // global (2D) request FIFO
  stream_fifo #(
    .DEPTH       ( GLOBAL_QUEUE_DEPTH ),
    .T           (idma_nd_req_t       )
  ) i_2D_request_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0            ),
    .testmode_i ( test_mode_i     ),
    .usage_o    (/*NOT CONNECTED*/),

    .data_i    ( twod_req         ),
    .valid_i   ( fe_valid         ),
    .ready_o   ( fe_ready         ),

    .data_o    ( twod_req_queue   ),
    .valid_o   ( twod_queue_valid ),
    .ready_i   ( twod_queue_ready )
  );

  localparam logic [1:0][31:0] RepWidths = '{default: 32'd32};

  idma_nd_midend #(
    .NumDim       ( NumDim        ),
    .addr_t       ( addr_t        ),
    .idma_req_t   ( idma_req_t    ),
    .idma_rsp_t   ( idma_rsp_t    ),
    .idma_nd_req_t( idma_nd_req_t ),
    .RepWidths    ( RepWidths     )
  ) i_idma_2D_midend (
    .clk_i,
    .rst_ni,

    .nd_req_i         ( twod_req_queue   ),
    .nd_req_valid_i   ( twod_queue_valid ),
    .nd_req_ready_o   ( twod_queue_ready ),

    .nd_rsp_o         (/*NOT CONNECTED*/ ),
    .nd_rsp_valid_o   ( trans_complete   ),
    .nd_rsp_ready_i   ( 1'b1             ), // Always ready to accept completed transfers

    .burst_req_o      ( burst_req        ),
    .burst_req_valid_o( be_valid         ),
    .burst_req_ready_i( be_ready         ),

    .burst_rsp_i      ( idma_rsp         ),
    .burst_rsp_valid_i( be_rsp_valid     ),
    .burst_rsp_ready_o( be_rsp_ready     ),

    .busy_o           ( midend_busy      )
  );

  // ------------------------------------------------------
  // BACKEND
  // ------------------------------------------------------

  idma_backend #(
    .DataWidth           ( AxiDataWidth              ),
    .AddrWidth           ( AxiAddrWidth              ),
    .UserWidth           ( AxiUserWidth              ),
    .AxiIdWidth          ( AxiIdWidth                ),
    .NumAxInFlight       ( NB_OUTSND_BURSTS            ),
    .BufferDepth         ( 3                           ),
    .TFLenWidth          ( TFLenWidth                  ),
    .RAWCouplingAvail    ( 1'b1                        ),
    .MaskInvalidData     ( 1'b1                        ),
    .HardwareLegalizer   ( 1'b1                        ),
    .RejectZeroTransfers ( 1'b1                        ),
    .MemSysDepth         ( 32'd0                       ),
    .ErrorCap            ( idma_pkg::NO_ERROR_HANDLING ),
    .idma_req_t          ( idma_req_t                  ),
    .idma_rsp_t          ( idma_rsp_t                  ),
    .idma_eh_req_t       ( idma_pkg::idma_eh_req_t     ),
    .idma_busy_t         ( idma_pkg::idma_busy_t       ),
    .protocol_req_t      ( slv_req_t                   ),
    .protocol_rsp_t      ( slv_resp_t                  ),
    .aw_chan_t           ( slv_aw_chan_t               ),
    .ar_chan_t           ( slv_ar_chan_t               )
  ) i_idma_backend (
    .clk_i,
    .rst_ni,
    .testmode_i      ( test_mode_i     ),

    .idma_req_i      ( burst_req       ),
    .req_valid_i     ( be_valid        ),
    .req_ready_o     ( be_ready        ),

    .idma_rsp_o      ( idma_rsp        ),
    .rsp_valid_o     ( be_rsp_valid    ),
    .rsp_ready_i     ( be_rsp_ready    ),

    .idma_eh_req_i   ( '0              ), // No error handling
    .eh_req_valid_i  ( 1'b1            ),
    .eh_req_ready_o  (/*NOT CONNECTED*/),

    .protocol_req_o  ( dma_req         ),
    .protocol_rsp_i  ( dma_rsp         ),
    .busy_o          ( idma_busy       )
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
    '{ // SoC low
      start_addr: host_base_addr,
      end_addr:   host_end_addr,
      idx:        0
    },
    '{ // TCDM
      start_addr: tcdm_base_addr,
      end_addr:   tcdm_end_addr,
      idx:        1
    }
  };
  localparam int unsigned NumMstPorts = 2;
  localparam int unsigned NumSlvPorts = NUM_STREAMS;

  localparam axi_pkg::xbar_cfg_t XbarCfg = '{
    NoSlvPorts:                    NumSlvPorts,
    NoMstPorts:                    NumMstPorts,
    MaxMstTrans:              NB_OUTSND_BURSTS,
    MaxSlvTrans:              NB_OUTSND_BURSTS,
    FallThrough:                          1'b0,
    LatencyMode:           axi_pkg::NO_LATENCY,
    PipelineStages:                      32'd0,
    AxiIdWidthSlvPorts:            SlvIdxWidth,
    AxiIdUsedSlvPorts:             SlvIdxWidth,
    UniqueIds:                            1'b0,
    AxiAddrWidth:                 AxiAddrWidth,
    AxiDataWidth:                 AxiDataWidth,
    NoAddrRules:                      NumRules
  };

  axi_xbar #(
    .Cfg          ( XbarCfg       ),
    .slv_aw_chan_t( slv_aw_chan_t ),
    .mst_aw_chan_t( mst_aw_chan_t ),
    .w_chan_t     ( w_chan_t      ),
    .slv_b_chan_t ( slv_b_chan_t  ),
    .mst_b_chan_t ( mst_b_chan_t  ),
    .slv_ar_chan_t( slv_ar_chan_t ),
    .mst_ar_chan_t( mst_ar_chan_t ),
    .slv_r_chan_t ( slv_r_chan_t  ),
    .mst_r_chan_t ( mst_r_chan_t  ),
    .slv_req_t    ( slv_req_t     ),
    .slv_resp_t   ( slv_resp_t    ),
    .mst_req_t    ( mst_req_t     ),
    .mst_resp_t   ( mst_resp_t    ),
    .rule_t       ( xbar_rule_t   )
  ) i_dma_axi_xbar (
    .clk_i                  ( clk_i                 ),
    .rst_ni                 ( rst_ni                ),
    .test_i                 ( test_mode_i           ),
    .slv_ports_req_i        ( dma_req               ),
    .slv_ports_resp_o       ( dma_rsp               ),
    .mst_ports_req_o        ( { axi_req_tcdm_o, axi_req_host_o } ),
    .mst_ports_resp_i       ( { axi_rsp_tcdm_i, axi_rsp_host_i } ),
    .addr_map_i             ( addr_map              ),
    .en_default_mst_port_i  ( '0                    ),
    .default_mst_port_i     ( '0                    )
  );

endmodule
