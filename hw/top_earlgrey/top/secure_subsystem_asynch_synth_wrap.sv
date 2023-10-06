// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "axi/typedef.svh"

module secure_subsystem_synth_wrap
   import axi_pkg::*;
   import jtag_ot_pkg::*;
   import tlul2axi_pkg::*;
   import dm_ot::*;
   import lc_ctrl_pkg::*;
   import secure_subsystem_synth_pkg::*;
   import top_earlgrey_pkg::*;
#(
   parameter int unsigned HartIdOffs            = 0,
   parameter int unsigned AxiAddrWidth          = SynthAxiAddrWidth,
   parameter int unsigned AxiDataWidth          = SynthAxiDataWidth,
   parameter int unsigned AxiUserWidth          = SynthAxiUserWidth,
   parameter int unsigned AxiOutIdWidth         = SynthAxiOutIdWidth,

   parameter int unsigned AxiOtAddrWidth        = SynthOtAxiAddrWidth,
   parameter int unsigned AxiOtDataWidth        = SynthOtAxiDataWidth,
   parameter int unsigned AxiOtUserWidth        = SynthOtAxiUserWidth,
   parameter int unsigned AxiOtOutIdWidth       = SynthOtAxiOutIdWidth,

   parameter int unsigned AsyncAxiOutAwWidth    = SynthAsyncAxiOutAwWidth,
   parameter int unsigned AsyncAxiOutWWidth     = SynthAsyncAxiOutWWidth,
   parameter int unsigned AsyncAxiOutBWidth     = SynthAsyncAxiOutBWidth,
   parameter int unsigned AsyncAxiOutArWidth    = SynthAsyncAxiOutArWidth,
   parameter int unsigned AsyncAxiOutRWidth     = SynthAsyncAxiOutRWidth,

   parameter type         axi_out_aw_chan_t     = synth_axi_out_aw_chan_t,
   parameter type         axi_out_w_chan_t      = synth_axi_out_w_chan_t,
   parameter type         axi_out_b_chan_t      = synth_axi_out_b_chan_t,
   parameter type         axi_out_ar_chan_t     = synth_axi_out_ar_chan_t,
   parameter type         axi_out_r_chan_t      = synth_axi_out_r_chan_t,
   parameter type         axi_out_req_t         = synth_axi_out_req_t,
   parameter type         axi_out_resp_t        = synth_axi_out_resp_t,

   parameter type         axi_ot_out_aw_chan_t  = synth_ot_axi_out_aw_chan_t,
   parameter type         axi_ot_out_w_chan_t   = synth_ot_axi_out_w_chan_t,
   parameter type         axi_ot_out_b_chan_t   = synth_ot_axi_out_b_chan_t,
   parameter type         axi_ot_out_ar_chan_t  = synth_ot_axi_out_ar_chan_t,
   parameter type         axi_ot_out_r_chan_t   = synth_ot_axi_out_r_chan_t,
   parameter type         axi_ot_out_req_t      = synth_ot_axi_out_req_t,
   parameter type         axi_ot_out_resp_t     = synth_ot_axi_out_resp_t,

   parameter int unsigned LogDepth              = SynthLogDepth,
   parameter int unsigned CdcSyncStages         = SynthCdcSyncStages,
   parameter int unsigned SyncStages            = 3
)  (
   input logic                           clk_i,
   input logic                           clk_ref_i,
   input logic                           rst_ni,
   input logic                           pwr_on_rst_ni,
   input logic                           test_enable_i,
   input logic [1:0]                     bootmode_i,
   input logic                           fetch_en_i,
   // JTAG port
   input logic                           jtag_tck_i,
   input logic                           jtag_tms_i,
   input logic                           jtag_trst_n_i,
   input logic                           jtag_tdi_i,
   output logic                          jtag_tdo_o,
   output logic                          jtag_tdo_oe_o,
   // Asynch AXI port
   output logic [AsyncAxiOutAwWidth-1:0] async_axi_out_aw_data_o,
   output logic [LogDepth:0]             async_axi_out_aw_wptr_o,
   input logic [LogDepth:0]              async_axi_out_aw_rptr_i,
   output logic [AsyncAxiOutWWidth-1:0]  async_axi_out_w_data_o,
   output logic [LogDepth:0]             async_axi_out_w_wptr_o,
   input logic [LogDepth:0]              async_axi_out_w_rptr_i,
   input logic [AsyncAxiOutBWidth-1:0]   async_axi_out_b_data_i,
   input logic [LogDepth:0]              async_axi_out_b_wptr_i,
   output logic [LogDepth:0]             async_axi_out_b_rptr_o,
   output logic [AsyncAxiOutArWidth-1:0] async_axi_out_ar_data_o,
   output logic [LogDepth:0]             async_axi_out_ar_wptr_o,
   input logic [LogDepth:0]              async_axi_out_ar_rptr_i,
   input logic [AsyncAxiOutRWidth-1:0]   async_axi_out_r_data_i,
   input logic [LogDepth:0]              async_axi_out_r_wptr_i,
   output logic [LogDepth:0]             async_axi_out_r_rptr_o,
   // Axi Isolate
   input  logic                          axi_isolate_i,
   output logic                          axi_isolated_o,
   // Interrupt signal
   input logic                           irq_ibex_i,
   // OT peripherals
   input logic                           ibex_uart_rx_i,
   output logic                          ibex_uart_tx_o,
   // GPIO
   output logic                          gpio_0_o,
   output logic                          gpio_0_oe_o,
   output logic                          gpio_1_o,
   output logic                          gpio_1_oe_o,
   input  logic                          gpio_0_i,
   input  logic                          gpio_1_i,
   // SPI Host
   output logic                          spi_host_SCK_o,
   output logic                          spi_host_SCK_en_o,
   output logic                          spi_host_CSB_o,
   output logic                          spi_host_CSB_en_o,
   output logic [3:0]                    spi_host_SD_o,
   input logic [3:0]                     spi_host_SD_i,
   output logic [3:0]                    spi_host_SD_en_o

);

   axi_out_req_t        axi_req;
   axi_out_resp_t       axi_rsp;

   axi_ot_out_req_t     ot_axi_req;
   axi_ot_out_resp_t    ot_axi_rsp;

   jtag_ot_pkg::jtag_req_t jtag_i;
   jtag_ot_pkg::jtag_rsp_t jtag_o;

   entropy_src_pkg::entropy_src_rng_req_t es_rng_req;
   entropy_src_pkg::entropy_src_rng_rsp_t es_rng_rsp;

   axi_out_req_t axi_out_req;
   axi_out_resp_t axi_out_rsp;

   logic [15:0] dio_in_i;
   logic [15:0] dio_out_o;
   logic [15:0] dio_oe_o;

   logic [46:0] mio_in_i;
   logic [46:0] mio_out_o;
   logic [46:0] mio_oe_o;

   logic es_rng_fips;

   logic test_en_tieoff;
   logic s_rst_n, s_init_n;

   logic fetch_en_sync;
   logic irq_ibex_sync;
   logic axi_isolate_sync;

   wire [1:0] flash_testmode_tieoff;
   wire otp_ext_tieoff, flash_testvolt_tieoff;

   assign flash_testmode_tieoff = '0;
   assign otp_ext_tieoff = '0;
   assign flash_testvolt_tieoff = '0;

   assign dio_in_i[1:0]   = '0;
   assign dio_in_i[15:6]  = '0;

   assign mio_in_i[0] = gpio_0_i ;
   assign mio_in_i[1] = gpio_1_i ;

   assign mio_in_i[25:2]  = '0;
   assign mio_in_i[46:27] = '0;

   assign spi_host_SCK_o  = dio_out_o[DioSpiHost0Sck];
   assign spi_host_CSB_o  = dio_out_o[DioSpiHost0Csb];

   assign spi_host_SCK_en_o = dio_oe_o[DioSpiHost0Sck];
   assign spi_host_CSB_en_o = dio_oe_o[DioSpiHost0Csb];

   assign spi_host_SD_o[0] = dio_out_o[DioSpiHost0Sd0];
   assign spi_host_SD_o[1] = dio_out_o[DioSpiHost0Sd1];
   assign spi_host_SD_o[2] = dio_out_o[DioSpiHost0Sd2];
   assign spi_host_SD_o[3] = dio_out_o[DioSpiHost0Sd3];

   assign spi_host_SD_en_o[0] = dio_oe_o[DioSpiHost0Sd0];
   assign spi_host_SD_en_o[1] = dio_oe_o[DioSpiHost0Sd1];
   assign spi_host_SD_en_o[2] = dio_oe_o[DioSpiHost0Sd2];
   assign spi_host_SD_en_o[3] = dio_oe_o[DioSpiHost0Sd3];

   assign dio_in_i[DioSpiHost0Sd0]  = spi_host_SD_i[0];
   assign dio_in_i[DioSpiHost0Sd1]  = spi_host_SD_i[1];
   assign dio_in_i[DioSpiHost0Sd2]  = spi_host_SD_i[2];
   assign dio_in_i[DioSpiHost0Sd3]  = spi_host_SD_i[3];

   assign mio_in_i[26]  = ibex_uart_rx_i;
   assign ibex_uart_tx_o = mio_out_o[26];

   assign gpio_0_o = mio_out_o[0];
   assign gpio_1_o = mio_out_o[1];

   assign gpio_0_oe_o = mio_oe_o[0];
   assign gpio_1_oe_o = mio_oe_o[1];

   //Unwrapping JTAG strucutres

   assign jtag_i.tck     = jtag_tck_i;
   assign jtag_i.tms     = jtag_tms_i;
   assign jtag_i.trst_n  = jtag_trst_n_i;
   assign jtag_i.tdi     = jtag_tdi_i;

   assign jtag_tdo_o     = jtag_o.tdo;
   assign jtag_tdo_oe_o  = jtag_o.tdo_oe;

   assign test_en_tieoff = test_enable_i;

   rstgen rstgen_i (
     .clk_i      ( clk_i         ),
     .rst_ni     ( rst_ni        ),
     .test_mode_i( test_enable_i ),
     .rst_no     ( s_rst_n       ),
     .init_no    ( s_init_n      )
   );

   sync #(
     .STAGES     ( SyncStages ),
     .ResetValue ( 1'b0       )
   ) i_fetch_en_sync (
     .clk_i,
     .rst_ni   ( pwr_on_rst_ni ),
     .serial_i ( fetch_en_i    ),
     .serial_o ( fetch_en_sync )
   );

   sync #(
     .STAGES     ( SyncStages ),
     .ResetValue ( 1'b0       )
   ) i_irq_sync (
     .clk_i,
     .rst_ni   ( pwr_on_rst_ni ),
     .serial_i ( irq_ibex_i    ),
     .serial_o ( irq_ibex_sync )
   );

   sync #(
     .STAGES     ( SyncStages ),
     .ResetValue ( 1'b1       )
   ) i_isolate_sync (
     .clk_i,
     .rst_ni   ( pwr_on_rst_ni    ),
     .serial_i ( axi_isolate_i    ),
     .serial_o ( axi_isolate_sync )
   );

   axi_isolate            #(
     .NumPending           ( secure_subsystem_synth_pkg::AxiMaxOutTrans ),
     .TerminateTransaction ( 1              ),
     .AtopSupport          ( 1              ),
     .AxiAddrWidth         ( AxiAddrWidth   ),
     .AxiDataWidth         ( AxiDataWidth   ),
     .AxiIdWidth           ( AxiOutIdWidth  ),
     .AxiUserWidth         ( AxiUserWidth   ),
     .axi_req_t            ( axi_out_req_t  ),
     .axi_resp_t           ( axi_out_resp_t )
   ) i_axi_out_isolate     (
     .clk_i                ( clk_i            ),
     .rst_ni               ( rst_ni           ),
     .slv_req_i            ( axi_req          ),
     .slv_resp_o           ( axi_rsp          ),
     .mst_req_o            ( axi_out_req      ),
     .mst_resp_i           ( axi_out_rsp      ),
     .isolate_i            ( axi_isolate_sync ),
     .isolated_o           ( axi_isolated_o   )
   );

   axi_dw_converter #(
      .AxiMaxReads        ( 8                   ),
      .AxiSlvPortDataWidth( AxiOtDataWidth      ),
      .AxiMstPortDataWidth( AxiDataWidth        ),
      .AxiAddrWidth       ( AxiAddrWidth        ),
      .AxiIdWidth         ( AxiOutIdWidth       ),
      .aw_chan_t          ( axi_out_aw_chan_t   ),
      .mst_w_chan_t       ( axi_out_w_chan_t    ),
      .slv_w_chan_t       ( axi_ot_out_w_chan_t ),
      .b_chan_t           ( axi_out_b_chan_t    ),
      .ar_chan_t          ( axi_out_ar_chan_t   ),
      .mst_r_chan_t       ( axi_out_r_chan_t    ),
      .slv_r_chan_t       ( axi_ot_out_r_chan_t ),
      .axi_mst_req_t      ( axi_out_req_t       ),
      .axi_mst_resp_t     ( axi_out_resp_t      ),
      .axi_slv_req_t      ( axi_ot_out_req_t    ),
      .axi_slv_resp_t     ( axi_ot_out_resp_t   )
   )  i_axi_dw_converter (
      .clk_i,
      .rst_ni     ( rst_ni     ),
      // slave port
      .slv_req_i  ( ot_axi_req ),
      .slv_resp_o ( ot_axi_rsp ),
      // master port
      .mst_req_o  ( axi_req    ),
      .mst_resp_i ( axi_rsp    )
   );

   // CDC domain

   axi_cdc_src #(
      .LogDepth   ( LogDepth          ),
      .SyncStages ( CdcSyncStages     ),
      .aw_chan_t  ( axi_out_aw_chan_t ),
      .w_chan_t   ( axi_out_w_chan_t  ),
      .b_chan_t   ( axi_out_b_chan_t  ),
      .ar_chan_t  ( axi_out_ar_chan_t ),
      .r_chan_t   ( axi_out_r_chan_t  ),
      .axi_req_t  ( axi_out_req_t     ),
      .axi_resp_t ( axi_out_resp_t    )
   ) i_cdc_out (
      .src_clk_i                  ( clk_i                   ),
      .src_rst_ni                 ( pwr_on_rst_ni           ),
      .src_req_i                  ( axi_out_req             ),
      .src_resp_o                 ( axi_out_rsp             ),
      .async_data_master_aw_data_o( async_axi_out_aw_data_o ),
      .async_data_master_aw_wptr_o( async_axi_out_aw_wptr_o ),
      .async_data_master_aw_rptr_i( async_axi_out_aw_rptr_i ),
      .async_data_master_w_data_o ( async_axi_out_w_data_o  ),
      .async_data_master_w_wptr_o ( async_axi_out_w_wptr_o  ),
      .async_data_master_w_rptr_i ( async_axi_out_w_rptr_i  ),
      .async_data_master_b_data_i ( async_axi_out_b_data_i  ),
      .async_data_master_b_wptr_i ( async_axi_out_b_wptr_i  ),
      .async_data_master_b_rptr_o ( async_axi_out_b_rptr_o  ),
      .async_data_master_ar_data_o( async_axi_out_ar_data_o ),
      .async_data_master_ar_wptr_o( async_axi_out_ar_wptr_o ),
      .async_data_master_ar_rptr_i( async_axi_out_ar_rptr_i ),
      .async_data_master_r_data_i ( async_axi_out_r_data_i  ),
      .async_data_master_r_wptr_i ( async_axi_out_r_wptr_i  ),
      .async_data_master_r_rptr_o ( async_axi_out_r_rptr_o  )
   );


   top_earlgrey #(
      .HartIdOffs(HartIdOffs),
      .axi_req_t(axi_ot_out_req_t),
      .axi_rsp_t(axi_ot_out_resp_t)
   ) u_RoT (
      .mio_attr_o                   (                       ),
      .dio_attr_o                   (                       ),
      .adc_req_o                    (                       ),
      .adc_rsp_i                    ( '0                    ),
      .ast_edn_rsp_o                (                       ),
      .ast_lc_dft_en_o              (                       ),
      .rom_cfg_i                    ( '0                    ),
      .clk_main_jitter_en_o         (                       ),
      .io_clk_byp_req_o             (                       ),
      .all_clk_byp_req_o            (                       ),
      .hi_speed_sel_o               (                       ),
      .flash_obs_o                  (                       ),
      .ast_tl_req_o                 (                       ),
      .ast_tl_rsp_i                 ( '0                    ),
      .dft_strap_test_o             (                       ),
      .usb_dp_pullup_en_o           (                       ),
      .usb_dn_pullup_en_o           (                       ),
      .pwrmgr_ast_req_o             (                       ),
      .otp_ctrl_otp_ast_pwr_seq_o   (                       ),
      .otp_ext_voltage_h_io         ( otp_ext_tieoff        ),
      .otp_obs_o                    (                       ),
      .sensor_ctrl_ast_alert_req_i  ( '0                    ),
      .sensor_ctrl_ast_alert_rsp_o  (                       ),
      .sensor_ctrl_ast_status_i     ( '0                    ),
      .ast2pinmux_i                 ( '0                    ),
      .flash_test_mode_a_io         ( flash_testmode_tieoff ),
      //.flash_test_voltage_h_io(),
      .ast_init_done_i              ( lc_ctrl_pkg::On       ),
      .sck_monitor_o                (                       ),
      .usbdev_usb_rx_d_i            ( '0                    ),
      .usbdev_usb_tx_d_o            (                       ),
      .usbdev_usb_tx_se0_o          (                       ),
      .usbdev_usb_tx_use_d_se0_o    (                       ),
      .usbdev_usb_rx_enable_o       (                       ),
      .usbdev_usb_ref_val_o         (                       ),
      .usbdev_usb_ref_pulse_o       (                       ),
      .clks_ast_o                   (                       ),
      .rsts_ast_o                   (                       ),
      .dio_in_i,
      .dio_out_o,
      .dio_oe_o,
      .mio_in_i,
      .mio_out_o,
      .mio_oe_o,
      .ast_edn_req_i                ( '0                    ),
      .obs_ctrl_i                   ( '0                    ),
      .ram_1p_cfg_i                 ( '0                    ),
      .ram_2p_cfg_i                 ( '0                    ),
      .io_clk_byp_ack_i             ( lc_ctrl_pkg::Off      ),
      .all_clk_byp_ack_i            ( lc_ctrl_pkg::Off      ),
      .div_step_down_req_i          ( lc_ctrl_pkg::Off      ),
      .calib_rdy_i                  ( lc_ctrl_pkg::Off      ),
      .flash_bist_enable_i          ( lc_ctrl_pkg::Off      ),
      .flash_power_down_h_i         ( '0                    ),
      .flash_power_ready_h_i        ( 1'b1                  ),
      .flash_test_voltage_h_io      ( flash_testvolt_tieoff ),
      .dft_hold_tap_sel_i           ( '0                    ),
      .pwrmgr_ast_rsp_i             ( 5'b11111              ),
      .otp_ctrl_otp_ast_pwr_seq_h_i ( '0                    ),
      .fpga_info_i                  ( '0                    ),
      .scan_rst_ni                  ( s_rst_n               ),
      .scan_en_i                    ( 1'b0                  ),
      .scanmode_i                   ( lc_ctrl_pkg::Off      ),
      .es_rng_fips_o                ( es_rng_fips           ),
      .es_rng_rsp_i                 ( es_rng_rsp            ),
      .es_rng_req_o                 ( es_rng_req            ),
      .por_n_i                      ( {s_rst_n, s_rst_n}    ),
      .clk_main_i                   ( clk_i                 ),
      .clk_io_i                     ( clk_i                 ),
      .clk_aon_i                    ( clk_i                 ),
      .clk_usb_i                    ( clk_i                 ),
      .axi_req_o                    ( ot_axi_req            ),
      .axi_rsp_i                    ( ot_axi_rsp            ),
      .irq_ibex_i                   ( irq_ibex_sync         ),
      .jtag_req_i                   ( jtag_i                ),
      .jtag_rsp_o                   ( jtag_o                ),
      .fetch_en_i                   ( fetch_en_sync         ),
      .bootmode_i                   ( bootmode_i            )
   );

   rng #(
      .EntropyStreams ( 4 )
   ) u_rng (
      .clk_i          ( clk_i                 ),
      .rst_ni         ( s_rst_n               ),
      .clk_ast_rng_i  ( clk_i                 ),
      .rst_ast_rng_ni ( s_rst_n               ),
      .rng_en_i       ( '1                    ), //es_rng_req.rng_enable ),
      .rng_fips_i     ( es_rng_fips           ),
      .scan_mode_i    ( '0                    ),
      .rng_b_o        ( es_rng_rsp.rng_b      ),
      .rng_val_o      ( es_rng_rsp.rng_valid  )
   );


endmodule
