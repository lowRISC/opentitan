// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module chip_darjeeling_verilator (
  // Clock and Reset
  input clk_i,
  input rst_ni,

  // communication with GPIO
  input [31:0] cio_gpio_p2d_i,
  output logic [31:0] cio_gpio_d2p_o,
  output logic [31:0] cio_gpio_en_d2p_o,
  output logic [31:0] cio_gpio_pull_en_o,
  output logic [31:0] cio_gpio_pull_select_o,

  // communication with UART
  input cio_uart_rx_p2d_i,
  output logic cio_uart_tx_d2p_o,
  output logic cio_uart_tx_en_d2p_o,

  // communication with SPI
  input cio_spi_device_sck_p2d_i,
  input cio_spi_device_csb_p2d_i,
  input cio_spi_device_sdi_p2d_i,
  output logic cio_spi_device_sdo_d2p_o,
  output logic cio_spi_device_sdo_en_d2p_o,

  // communication with JTAG
  input logic  cio_jtag_tck_i,
  input logic  cio_jtag_tms_i,
  input logic  cio_jtag_tdi_i,
  input logic  cio_jtag_trst_ni,
  output logic cio_jtag_tdo_o
);

  import top_darjeeling_pkg::*;


  // JTAG
  jtag_pkg::jtag_req_t jtag_req;
  jtag_pkg::jtag_rsp_t jtag_rsp;
  tlul_pkg::tl_h2d_t   dbg_tl_h2d;
  tlul_pkg::tl_d2h_t   dbg_tl_d2h;
  assign jtag_req.tck    = cio_jtag_tck_i;
  assign jtag_req.tms    = cio_jtag_tms_i;
  assign jtag_req.trst_n = cio_jtag_trst_ni;
  assign jtag_req.tdi    = cio_jtag_tdi_i;
  assign cio_jtag_tdo_o  = jtag_rsp.tdo;

  tlul_jtag_dtm #(
    .IdcodeValue(jtag_id_pkg::LC_DM_COMBINED_JTAG_IDCODE),
    // Notes:
    // - one RV_DM instance uses 9bits
    // - our crossbar tooling expects individual IPs to be spaced apart by 12bits at the moment
    // - the DMI address shifted through jtag is a word address and hence 2bits smaller than this
    // - setting this to 18bits effectively gives us 2^6 = 64 addressable 12bit ranges
    .NumDmiByteAbits(18)
  ) u_tlul_jtag_dtm (
    .clk_i      (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni     (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .jtag_i     (jtag_req),
    .jtag_o     (jtag_rsp),
    .scan_rst_ni(scan_rst_n),
    .scanmode_i (scanmode),
    .tl_h2d_o   (dbg_tl_h2d),
    .tl_d2h_i   (dbg_tl_d2h)
  );

  // TODO: instantiate padring and route these signals through that module
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;
  prim_pad_wrapper_pkg::pad_attr_t[pinmux_reg_pkg::NDioPads-1:0] dio_attr;

  always_comb begin : assign_dio_in
    dio_in = '0;
    // SPI Device
    dio_in[DioSpiDeviceSck] = cio_spi_device_sck_p2d_i;
    dio_in[DioSpiDeviceCsb] = cio_spi_device_csb_p2d_i;
    dio_in[DioSpiDeviceSd0] = cio_spi_device_sdi_p2d_i;
    // 14 generic GPIOs
    dio_in[DioGpioGpio13:DioGpioGpio0] = cio_gpio_p2d_i[13:0];
    // SW straps
    dio_in[DioGpioGpio24:DioGpioGpio22] = cio_gpio_p2d_i[24:22];
    // UART RX
    dio_in[DioUart0Rx] = cio_uart_rx_p2d_i;
  end

  // SPI Device
  assign cio_spi_device_sdo_d2p_o = dio_out[DioSpiDeviceSd1];
  assign cio_spi_device_sdo_en_d2p_o = dio_oe[DioSpiDeviceSd1];
  // 14 generic GPIOs
  assign cio_gpio_d2p_o[13:0]        = dio_out[DioGpioGpio13:DioGpioGpio0];
  assign cio_gpio_en_d2p_o[13:0]     = dio_oe[DioGpioGpio13:DioGpioGpio0];
  assign cio_gpio_d2p_o[21:14]      = '0;
  assign cio_gpio_en_d2p_o[21:14]   = '0;
  // SW straps
  assign cio_gpio_d2p_o[24:22]      = dio_out[DioGpioGpio24:DioGpioGpio22];
  assign cio_gpio_en_d2p_o[24:22]   = dio_oe[DioGpioGpio24:DioGpioGpio22];
  assign cio_gpio_d2p_o[26:25]      = '0;
  assign cio_gpio_en_d2p_o[26:25]   = '0;
  // UART TX
  assign cio_uart_tx_d2p_o    = dio_out[DioUart0Tx];
  assign cio_uart_tx_en_d2p_o = dio_oe[DioUart0Tx];

  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe;
  prim_pad_wrapper_pkg::pad_attr_t[pinmux_reg_pkg::NMioPads-1:0] mio_attr;

  always_comb begin : assign_mio_in
    mio_in = '0;
    // TAP straps
    mio_in[MioPadMio1] = cio_gpio_p2d_i[27];
    mio_in[MioPadMio0] = cio_gpio_p2d_i[30];
  end

  // TAP straps
  assign cio_gpio_d2p_o[27]         = mio_out[MioPadMio1];
  assign cio_gpio_en_d2p_o[27]      = mio_oe[MioPadMio1];
  assign cio_gpio_d2p_o[29:28]      = '0;
  assign cio_gpio_en_d2p_o[29:28]   = '0;
  assign cio_gpio_d2p_o[30]         = mio_out[MioPadMio0];
  assign cio_gpio_en_d2p_o[30]      = mio_oe[MioPadMio0];
  assign cio_gpio_d2p_o[31]         = '0;
  assign cio_gpio_en_d2p_o[31]      = '0;

  // Note: we're collecting the `pull_en` and `pull_select` signals together
  // so that the GPIO DPI functions can simulate weak and strong GPIO
  // inputs.  The `cio_gpio_pull_en_o` and `cio_gpio_pull_select_o` bit
  // vectors should have the same ordering as the `cio_gpio_d2p_o` vector.
  // See gpiodpi.c to see how weak/strong inputs work.
  //
  // Pull enable for 14 generic GPIOs
  assign cio_gpio_pull_en_o[0] = dio_attr[DioGpioGpio0].pull_en;
  assign cio_gpio_pull_en_o[1] = dio_attr[DioGpioGpio1].pull_en;
  assign cio_gpio_pull_en_o[2] = dio_attr[DioGpioGpio2].pull_en;
  assign cio_gpio_pull_en_o[3] = dio_attr[DioGpioGpio3].pull_en;
  assign cio_gpio_pull_en_o[4] = dio_attr[DioGpioGpio4].pull_en;
  assign cio_gpio_pull_en_o[5] = dio_attr[DioGpioGpio5].pull_en;
  assign cio_gpio_pull_en_o[6] = dio_attr[DioGpioGpio6].pull_en;
  assign cio_gpio_pull_en_o[7] = dio_attr[DioGpioGpio7].pull_en;
  assign cio_gpio_pull_en_o[8] = dio_attr[DioGpioGpio8].pull_en;
  assign cio_gpio_pull_en_o[9] = dio_attr[DioGpioGpio9].pull_en;
  assign cio_gpio_pull_en_o[10] = dio_attr[DioGpioGpio10].pull_en;
  assign cio_gpio_pull_en_o[11] = dio_attr[DioGpioGpio11].pull_en;
  assign cio_gpio_pull_en_o[12] = dio_attr[DioGpioGpio12].pull_en;
  assign cio_gpio_pull_en_o[13] = dio_attr[DioGpioGpio13].pull_en;
  assign cio_gpio_pull_en_o[21:14] = '0;

  // Pull enable for SW STRAPs
  assign cio_gpio_pull_en_o[22] = dio_attr[DioGpioGpio22].pull_en;
  assign cio_gpio_pull_en_o[23] = dio_attr[DioGpioGpio23].pull_en;
  assign cio_gpio_pull_en_o[24] = dio_attr[DioGpioGpio24].pull_en;

  // Pull enable for TAP STRAPs
  assign cio_gpio_pull_en_o[26:25] = '0;
  assign cio_gpio_pull_en_o[27] = mio_attr[MioPadMio1].pull_en;
  assign cio_gpio_pull_en_o[29:28] = '0;
  assign cio_gpio_pull_en_o[30] = mio_attr[MioPadMio0].pull_en;
  assign cio_gpio_pull_en_o[31] = '0;

  // Pull select for 14 generic GPIOs
  assign cio_gpio_pull_select_o[0] = dio_attr[DioGpioGpio0].pull_select;
  assign cio_gpio_pull_select_o[1] = dio_attr[DioGpioGpio1].pull_select;
  assign cio_gpio_pull_select_o[2] = dio_attr[DioGpioGpio2].pull_select;
  assign cio_gpio_pull_select_o[3] = dio_attr[DioGpioGpio3].pull_select;
  assign cio_gpio_pull_select_o[4] = dio_attr[DioGpioGpio4].pull_select;
  assign cio_gpio_pull_select_o[5] = dio_attr[DioGpioGpio5].pull_select;
  assign cio_gpio_pull_select_o[6] = dio_attr[DioGpioGpio6].pull_select;
  assign cio_gpio_pull_select_o[7] = dio_attr[DioGpioGpio7].pull_select;
  assign cio_gpio_pull_select_o[8] = dio_attr[DioGpioGpio8].pull_select;
  assign cio_gpio_pull_select_o[9] = dio_attr[DioGpioGpio9].pull_select;
  assign cio_gpio_pull_select_o[10] = dio_attr[DioGpioGpio10].pull_select;
  assign cio_gpio_pull_select_o[11] = dio_attr[DioGpioGpio11].pull_select;
  assign cio_gpio_pull_select_o[12] = dio_attr[DioGpioGpio12].pull_select;
  assign cio_gpio_pull_select_o[13] = dio_attr[DioGpioGpio13].pull_select;
  assign cio_gpio_pull_select_o[21:14] = '0;

  // Pull select for SW STRAPs
  assign cio_gpio_pull_select_o[22] = dio_attr[DioGpioGpio22].pull_select;
  assign cio_gpio_pull_select_o[23] = dio_attr[DioGpioGpio23].pull_select;
  assign cio_gpio_pull_select_o[24] = dio_attr[DioGpioGpio24].pull_select;

  // Pull select for TAP STRAPs
  assign cio_gpio_pull_select_o[26:25] = '0;
  assign cio_gpio_pull_select_o[27] = mio_attr[MioPadMio1].pull_select;
  assign cio_gpio_pull_select_o[29:28] = '0;
  assign cio_gpio_pull_select_o[30] = mio_attr[MioPadMio0].pull_select;
  assign cio_gpio_pull_select_o[31] = '0;

  ////////////////////////////////
  // AST - Custom for Verilator //
  ////////////////////////////////
  ast_pkg::ast_pwst_t ast_pwst;
  ast_pkg::ast_pwst_t ast_pwst_h;

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
  pwrmgr_pkg::pwr_boot_status_t pwrmgr_boot_status;

  ast_pkg::ast_clks_t ast_base_clks;

  // external clock comes in at a fixed position
  logic ext_clk;
  assign ext_clk = '0;

  logic clk_aon;
  // reset is not used below becuase verilator uses only sync resets
  // and also does not under 'x'.
  // if we allow the divider below to reset, clk_aon will be silenced,
  // and as a result all the clk_aon logic inside top_darjeeling does not
  // get reset
  prim_clock_div #(
    .Divisor(4)
  ) u_aon_div (
    .clk_i,
    .rst_ni(1'b1),
    .step_down_req_i('0),
    .step_down_ack_o(),
    .test_en_i('0),
    .clk_o(clk_aon)
  );

  ast_pkg::clks_osc_byp_t clks_osc_byp;
  assign clks_osc_byp = '{
    usb: clk_i,
    sys: clk_i,
    io:  clk_i,
    aon: clk_aon
  };

  ////////////////////////////////////////////
  // CTN Address decoding and SRAM Instance //
  ////////////////////////////////////////////

  // synchronization clocks / rests
  clkmgr_pkg::clkmgr_out_t clkmgr_aon_clocks;
  rstmgr_pkg::rstmgr_out_t rstmgr_aon_resets;

  localparam int CtnSramDw = top_pkg::TL_DW + tlul_pkg::DataIntgWidth;

  tlul_pkg::tl_h2d_t ctn_egress_tl_h2d;
  tlul_pkg::tl_d2h_t ctn_egress_tl_d2h;

  tlul_pkg::tl_h2d_t ctn_s1n_tl_h2d[1];
  tlul_pkg::tl_d2h_t ctn_s1n_tl_d2h[1];

  // Steering signal for address decoding.
  logic [0:0] ctn_dev_sel_s1n;

  logic sram_intg_error, sram_req, sram_gnt, sram_we, sram_rvalid;
  logic [top_pkg::CtnSramAw-1:0] sram_addr;
  logic [CtnSramDw-1:0] sram_wdata, sram_wmask, sram_rdata;

  // Steering of requests.
  // Addresses leaving the RoT through the CTN port are mapped to an internal 1G address space of
  // 0x4000_0000 - 0x8000_0000. However, the CTN RAM only covers a 1MB region inside that space,
  // and hence additional decoding and steering logic is needed here.
  // TODO: this should in the future be replaced by an automatically generated crossbar.
  always_comb begin
    // Default steering to generate error response if address is not within the range
    ctn_dev_sel_s1n = 1'b1;
    // Steering to CTN SRAM.
    if ((ctn_egress_tl_h2d.a_address & ~(TOP_DARJEELING_RAM_CTN_SIZE_BYTES-1)) ==
        TOP_DARJEELING_RAM_CTN_BASE_ADDR) begin
      ctn_dev_sel_s1n = 1'd0;
    end
  end

  tlul_socket_1n #(
    .HReqDepth (4'h0),
    .HRspDepth (4'h0),
    .DReqDepth (8'h0),
    .DRspDepth (8'h0),
    .N         (1)
  ) u_ctn_s1n (
    .clk_i        (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni       (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .tl_h_i       (ctn_egress_tl_h2d),
    .tl_h_o       (ctn_egress_tl_d2h),
    .tl_d_o       (ctn_s1n_tl_h2d),
    .tl_d_i       (ctn_s1n_tl_d2h),
    .dev_select_i (ctn_dev_sel_s1n)
  );

  tlul_adapter_sram #(
    .SramAw(top_pkg::CtnSramAw),
    .SramDw(CtnSramDw - tlul_pkg::DataIntgWidth),
    .Outstanding(2),
    .ByteAccess(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(0),
    .EnableDataIntgPt(1),
    .SecFifoPtr      (0)
  ) u_tlul_adapter_sram_ctn (
    .clk_i       (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni      (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .tl_i        (ctn_s1n_tl_h2d[0]),
    .tl_o        (ctn_s1n_tl_d2h[0]),
    // Ifetch is explicitly allowed
    .en_ifetch_i (prim_mubi_pkg::MuBi4True),
    .req_o       (sram_req),
    .req_type_o  (),
    // SRAM can always accept a request.
    .gnt_i       (1),
    .we_o        (sram_we),
    .addr_o      (sram_addr),
    .wdata_o     (sram_wdata),
    .wmask_o     (sram_wmask),
    .intg_error_o(),
    .rdata_i     (sram_rdata),
    .rvalid_i    (sram_rvalid),
    .rerror_i    (1'b0)
  );

  prim_ram_1p_adv #(
    .Depth(top_pkg::CtnSramDepth),
    .Width(CtnSramDw),
    .DataBitsPerMask(CtnSramDw),
    .EnableECC(0),
    .EnableParity(0),
    .EnableInputPipeline(1),
    .EnableOutputPipeline(1)
  ) u_prim_ram_1p_adv_ctn (
    .clk_i    (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .req_i    (sram_req),
    .write_i  (sram_we),
    .addr_i   (sram_addr),
    .wdata_i  (sram_wdata),
    .wmask_i  (sram_wmask),
    .rdata_o  (sram_rdata),
    .rvalid_o (sram_rvalid),
    // No error detection is enabled inside SRAM.
    // Bus ECC is checked at the consumer side.
    .rerror_o (),
    .cfg_i    ('0)
  );



  ///////////////////////////////////////
  // AST - Common with other platforms //
  ///////////////////////////////////////

  // platform specific supply manipulation to create POR
  logic [3:0] cnt;
  logic vcc_supp;

  // keep incrementing until saturation
  always_ff @(posedge clk_aon) begin
    if (cnt < 4'hf) begin
      cnt <= cnt + 1'b1;
    end
  end

  // create fake por condition
  assign vcc_supp = cnt < 4'h4 ? 1'b0 :
                    cnt < 4'h8 ? 1'b1 :
                    cnt < 4'hc ? 1'b0 : 1'b1;

  // TLUL interface
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;

  assign ast_base_pwr.main_pok = ast_pwst.main_pok;

  // monitored clock
  logic sck_monitor;

  // otp power sequence
  otp_ctrl_pkg::otp_ast_req_t otp_ctrl_otp_ast_pwr_seq;
  otp_ctrl_pkg::otp_ast_rsp_t otp_ctrl_otp_ast_pwr_seq_h;

  // entropy source interface
  // The entropy source pacakge definition should eventually be moved to es
  entropy_src_pkg::entropy_src_hw_if_req_t entropy_src_hw_if_req;
  entropy_src_pkg::entropy_src_hw_if_rsp_t entropy_src_hw_if_rsp;

  // entropy distribution network
  edn_pkg::edn_req_t ast_edn_edn_req;
  edn_pkg::edn_rsp_t ast_edn_edn_rsp;

  // alerts interface
  ast_pkg::ast_alert_rsp_t ast_alert_rsp;
  ast_pkg::ast_alert_req_t ast_alert_req;

  // Life cycle clock bypass req/ack
  prim_mubi_pkg::mubi4_t all_clk_byp_req;
  prim_mubi_pkg::mubi4_t all_clk_byp_ack;
  prim_mubi_pkg::mubi4_t io_clk_byp_req;
  prim_mubi_pkg::mubi4_t io_clk_byp_ack;
  prim_mubi_pkg::mubi4_t div_step_down_req;
  logic hi_speed_sel;

  // DFT connections
  logic scan_en;
  lc_ctrl_pkg::lc_tx_t dft_en;
  pinmux_pkg::dft_strap_test_req_t dft_strap_test;

  // Debug connections
  logic [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux;

  // Jitter enable
  logic jen;

  // reset domain connections
  import rstmgr_pkg::PowerDomains;
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;

  // AST does not use all clocks / resets forwarded to it
  logic unused_slow_clk_en;
  assign unused_slow_clk_en = base_ast_pwr.slow_clk_en;

  logic unused_pwr_clamp;
  assign unused_pwr_clamp = base_ast_pwr.pwr_clamp;

  prim_mubi_pkg::mubi4_t ast_init_done;
  ast #(
    .EntropyStreams(ast_pkg::EntropyStreams),
    .AdcChannels(ast_pkg::AdcChannels),
    .AdcDataWidth(ast_pkg::AdcDataWidth),
    .UsbCalibWidth(ast_pkg::UsbCalibWidth),
    .Ast2PadOutWidth(ast_pkg::Ast2PadOutWidth),
    .Pad2AstInWidth(ast_pkg::Pad2AstInWidth)
  ) u_ast (
    // different between verilator and other platforms
    .clk_ast_ext_i         ( clk_i ),
    .por_ni                ( rst_ni ),
    // USB IO Pull-up Calibration Setting
    .usb_io_pu_cal_o       (  ),
    // Direct short to PAD
    .ast2pad_t0_ao         (  ),
    .ast2pad_t1_ao         (  ),
    // Memory configuration connections
    .dpram_rmf_o           (  ),
    .dpram_rml_o           (  ),
    .spram_rm_o            (  ),
    .sprgf_rm_o            (  ),
    .sprom_rm_o            (  ),
    // clocks' oschillator bypass for FPGA
    .clk_osc_byp_i         ( clks_osc_byp ),


    // clocks and resets supplied for detection
    .sns_clks_i      ( clkmgr_aon_clocks    ),
    .sns_rsts_i      ( rstmgr_aon_resets    ),
    .sns_spi_ext_clk_i ( sck_monitor          ),
    // tlul
    .tl_i                  ( base_ast_bus ),
    .tl_o                  ( ast_base_bus ),
    // init done indication
    .ast_init_done_o       ( ast_init_done),
    // buffered clocks & resets
    .clk_ast_tlul_i (clkmgr_aon_clocks.clk_io_div4_secure),
    .clk_ast_adc_i (clkmgr_aon_clocks.clk_aon_secure),
    .clk_ast_alert_i (clkmgr_aon_clocks.clk_io_div4_secure),
    .clk_ast_es_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_rng_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_usb_i (clkmgr_aon_clocks.clk_usb_peri),
    .rst_ast_tlul_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_adc_ni (rstmgr_aon_resets.rst_lc_aon_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_alert_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_es_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_rng_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_usb_ni ('1),

    // pok test for FPGA
    .vcc_supp_i            ( vcc_supp ),
    .vcaon_supp_i          ( 1'b1 ),
    .vcmain_supp_i         ( 1'b1 ),
    .vioa_supp_i           ( 1'b1 ),
    .viob_supp_i           ( 1'b1 ),
    // pok
    .ast_pwst_o            ( ast_pwst ),
    .ast_pwst_h_o          ( ast_pwst_h ),
    // main regulator
    .main_env_iso_en_i     ( base_ast_pwr.pwr_clamp_env ),
    .main_pd_ni            ( base_ast_pwr.main_pd_n ),
    // pdm control (flash)/otp
    .flash_power_down_h_o  (  ),
    .flash_power_ready_h_o (  ),
    .otp_power_seq_i       ( otp_ctrl_otp_ast_pwr_seq ),
    .otp_power_seq_h_o     ( otp_ctrl_otp_ast_pwr_seq_h ),
    // system source clock
    .clk_src_sys_en_i      ( base_ast_pwr.core_clk_en ),
    // need to add function in clkmgr
    .clk_src_sys_jen_i     ( jen ),
    .clk_src_sys_o         ( ast_base_clks.clk_sys  ),
    .clk_src_sys_val_o     ( ast_base_pwr.core_clk_val ),
    // aon source clock
    .clk_src_aon_o         ( ast_base_clks.clk_aon ),
    .clk_src_aon_val_o     ( ast_base_pwr.slow_clk_val ),
    // io source clock
    .clk_src_io_en_i       ( base_ast_pwr.io_clk_en ),
    .clk_src_io_o          ( ast_base_clks.clk_io ),
    .clk_src_io_val_o      ( ast_base_pwr.io_clk_val ),
    .clk_src_io_48m_o      ( div_step_down_req ),
    // usb source clock
    .usb_ref_pulse_i       ( '0 ),
    .usb_ref_val_i         ( '0 ),
    .clk_src_usb_en_i      ( base_ast_pwr.usb_clk_en ),
    .clk_src_usb_o         ( ast_base_clks.clk_usb ),
    .clk_src_usb_val_o     ( ast_base_pwr.usb_clk_val ),
    // adc
    .adc_pd_i              ( '0 ),
    .adc_chnsel_i          ( '0 ),
    .adc_d_o               ( ),
    .adc_d_val_o           ( ),
    // entropy_src
    .es_req_i              ( entropy_src_hw_if_req ),
    .es_rsp_o              ( entropy_src_hw_if_rsp ),
    // entropy
    .entropy_rsp_i         ( ast_edn_edn_rsp ),
    .entropy_req_o         ( ast_edn_edn_req ),
    // alerts
    .alert_rsp_i           ( ast_alert_rsp  ),
    .alert_req_o           ( ast_alert_req  ),
    // dft
    .dft_strap_test_i      ( dft_strap_test   ),
    .lc_dft_en_i           ( dft_en           ),
    .fla_obs_i             ( '0 ),
    .otp_obs_i             ( '0 ),
    .otm_obs_i             ( '0 ),
    .usb_obs_i             ( '0 ),
    .obs_ctrl_o            (  ),
    // pinmux related
    .padmux2ast_i          ( '0 ),
    .ast2padmux_o          ( ),
    .ext_freq_is_96m_i     ( hi_speed_sel ),
    .all_clk_byp_req_i     ( ast_clk_byp_req ),
    .all_clk_byp_ack_o     ( ast_clk_byp_ack ),
    .io_clk_byp_req_i      ( io_clk_byp_req   ),
    .io_clk_byp_ack_o      ( io_clk_byp_ack   ),
    .flash_bist_en_o       (  ),
    // scan
    .dft_scan_md_o         ( scanmode ),
    .scan_shift_en_o       ( scan_en ),
    .scan_reset_no         ( scan_rst_n )
  );


  // TODO: generate these indices from the target-specific
  // pinout configuration. But first, this verilator top needs
  // to be split into a Verilator TB and a Verilator chiplevel.
  // DFT and Debug signal positions in the pinout.
  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    tck_idx:        MioPadMio4,
    tms_idx:        MioPadMio5,
    trst_idx:       MioPadMio6,
    tdi_idx:        MioPadMio7,
    tdo_idx:        MioPadMio8,
    tap_strap0_idx: MioPadMio0,
    tap_strap1_idx: MioPadMio1,
    dft_strap0_idx: MioPadMio2,
    dft_strap1_idx: MioPadMio3,
    // TODO: check whether there is a better way to pass these USB-specific params
    usb_dp_idx:     0,
    usb_dn_idx:     0,
    usb_sense_idx:  0,
    // TODO: connect these once the verilator chip-level has been merged with the chiplevel.sv.tpl
    dio_pad_type: {pinmux_reg_pkg::NDioPads{prim_pad_wrapper_pkg::BidirStd}},
    mio_pad_type: {pinmux_reg_pkg::NMioPads{prim_pad_wrapper_pkg::BidirStd}}
  };

  prim_mubi_pkg::mubi4_t lc_clk_bypass;


  // Top-level design

  logic [rstmgr_pkg::PowerDomains-1:0] por_n;
  assign por_n = {ast_pwst.main_pok, ast_pwst.aon_pok};

  // The logic below is a is a loopback path.  It listens to the internal reset request generated by
  // the power manager and translates this request into a stretched pulse (modeled by the counter).
  // The stretched pulse is fed back to top_darjeeling as external async SoC reset request.
  // TODO(#22710): This should be moved to the DV environment, and we need to extend the code to be
  // able to asynchronously assert the external reset pin without any internal request.
  logic  internal_request_d, internal_request_q;
  logic  external_reset, count_up;
  logic  [3:0] count;
  assign internal_request_d = pwrmgr_boot_status.light_reset_req;
  always_ff @(posedge ast_base_clks.clk_aon or negedge por_n[0]) begin
    if (!por_n[0]) begin
      external_reset     <= 1'b0;
      internal_request_q <= 1'b0;
      count_up           <= '0;
      count              <= '0;
    end else begin
      internal_request_q <= internal_request_d;
      if (!internal_request_q && internal_request_d) begin
        count_up       <= 1'b1;
        external_reset <= 1;
      end else if (count == 'd8) begin
        count_up       <= 0;
        external_reset <= 0;
        count          <= '0;
      end else if (count_up) begin
        count <= count + 1;
      end
    end
  end

  top_darjeeling #(
    .PinmuxAonTargetCfg(PinmuxTargetCfg),
    .SecAesAllowForcingMasks(1'b1),
    .SramCtrlMainInstrExec(1),
    .SramCtrlRetAonInstrExec(0)
  ) top_darjeeling (
    // update por / reset connections, this is not quite right here
    .por_n_i                      (por_n             ),
    .clk_main_i                   (clk_i             ),
    .clk_io_i                     (clk_i             ),
    .clk_usb_i                    (clk_i             ),
    .clk_aon_i                    (clk_aon           ),
    // change the above
    .clks_ast_o                   (clkmgr_aon_clocks ),
    .clk_main_jitter_en_o         ( jen              ),
    .rsts_ast_o                   ( rstmgr_aon_resets),
    .sck_monitor_o                ( sck_monitor      ),
    .pwrmgr_ast_req_o             ( base_ast_pwr     ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr     ),
    .sensor_ctrl_ast_alert_req_i  ( ast_alert_req    ),
    .sensor_ctrl_ast_alert_rsp_o  ( ast_alert_rsp    ),
    .sensor_ctrl_ast_status_i     ( ast_pwst.io_pok  ),
    .ast_tl_req_o                 ( base_ast_bus     ),
    .ast_tl_rsp_i                 ( ast_base_bus     ),
    .ast_edn_req_i                ( ast_edn_edn_req  ),
    .ast_edn_rsp_o                ( ast_edn_edn_rsp  ),
    .otp_ctrl_otp_ast_pwr_seq_o   ( otp_ctrl_otp_ast_pwr_seq   ),
    .otp_ctrl_otp_ast_pwr_seq_h_i ( otp_ctrl_otp_ast_pwr_seq_h ),
    .entropy_src_hw_if_req_o      ( entropy_src_hw_if_req      ),
    .entropy_src_hw_if_rsp_i      ( entropy_src_hw_if_rsp      ),
    .all_clk_byp_req_o            ( all_clk_byp_req            ),
    .all_clk_byp_ack_i            ( all_clk_byp_ack            ),
    .io_clk_byp_req_o             ( io_clk_byp_req             ),
    .io_clk_byp_ack_i             ( io_clk_byp_ack             ),
    .hi_speed_sel_o               ( hi_speed_sel               ),
    .div_step_down_req_i          ( div_step_down_req          ),
    .calib_rdy_i                  ( ast_init_done              ),
    .ast_init_done_i              ( ast_init_done              ),

    // DMI into rv_dm and lc_ctrl
    .dbg_tl_req_i                 ( dbg_tl_h2d ),
    .dbg_tl_rsp_o                 ( dbg_tl_d2h ),

    // ingress / egress ports and soc proxy signals
    .ctn_tl_h2d_o                 ( ctn_egress_tl_h2d ),
    .ctn_tl_d2h_i                 ( ctn_egress_tl_d2h ),
    .soc_gpi_async_o              ( ),
    .soc_gpo_async_i              ( '0 ),
    .dma_sys_req_o                ( ),
    .dma_sys_rsp_i                ( '0 ),
    .dma_ctn_tl_h2d_o             ( ),
    .dma_ctn_tl_d2h_i             ( tlul_pkg::TL_D2H_DEFAULT ),
    .pwrmgr_boot_status_o         ( pwrmgr_boot_status       ),
    .soc_fatal_alert_req_i        ( 1'b0 ),
    .soc_fatal_alert_rsp_o        ( ),
    .soc_recov_alert_req_i        ( ),
    .soc_recov_alert_rsp_o        ( ),
    .soc_intr_async_i             ( '0 ),
    .soc_wkup_async_i             ( 1'b0 ),
    // TODO(#22710): this should come from modeled SoC (e.g., from TB).
    .soc_rst_req_async_i          ( external_reset),
    .soc_lsio_trigger_i           ( '0 ),

    // OTP external voltage
    .otp_ext_voltage_h_io         ( ),

    // Multiplexed I/O
    .mio_in_i                     (mio_in),
    .mio_out_o                    (mio_out),
    .mio_oe_o                     (mio_oe),

    // Dedicated I/O
    .dio_in_i                     (dio_in),
    .dio_out_o                    (dio_out),
    .dio_oe_o                     (dio_oe),

    // Pad attributes
    .mio_attr_o                   (mio_attr),
    .dio_attr_o                   (dio_attr),

    // Memory attributes
    // This is different between verilator and the rest of the platforms right now
    .ram_1p_cfg_i                 ('0),
    .spi_ram_2p_cfg_i             ('0),
    .rom_cfg_i                    ('0),

    // DFT signals
    .ast_lc_dft_en_o              ( dft_en                     ),
    .dft_strap_test_o             ( dft_strap_test             ),
    .dft_hold_tap_sel_i           ( '0                         ),
    .scan_rst_ni                  ( scan_rst_n                 ),
    .scan_en_i                    ( scan_en                    ),
    .scanmode_i                   ( scanmode                   )
  );

endmodule : chip_darjeeling_verilator
