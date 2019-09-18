// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey (
  // Clock and Reset
  input               clk_i,
  input               rst_ni,

  // uart
  input  cio_uart_rx_p2d_i,
  output cio_uart_tx_d2p_o,
  output cio_uart_tx_en_d2p_o,
  // gpio
  input  [31:0] cio_gpio_gpio_p2d_i,
  output [31:0] cio_gpio_gpio_d2p_o,
  output [31:0] cio_gpio_gpio_en_d2p_o,
  // spi_device
  input  cio_spi_device_sck_p2d_i,
  input  cio_spi_device_csb_p2d_i,
  input  cio_spi_device_mosi_p2d_i,
  output cio_spi_device_miso_d2p_o,
  output cio_spi_device_miso_en_d2p_o,
  // flash_ctrl
  // rv_timer
  // hmac
  // rv_plic

  // JTAG interface
  input               jtag_tck_i,
  input               jtag_tms_i,
  input               jtag_trst_ni,
  input               jtag_td_i,
  output              jtag_td_o
);

  import tlul_pkg::*;
  import top_pkg::*;
  import tl_main_pkg::*;
  import flash_ctrl_pkg::*;

  logic scanmode_i;
  assign scanmode_i = 1'b0;

  tl_h2d_t  tl_corei_h_h2d;
  tl_d2h_t  tl_corei_h_d2h;

  tl_h2d_t  tl_cored_h_h2d;
  tl_d2h_t  tl_cored_h_d2h;

  tl_h2d_t  tl_dm_sba_h_h2d;
  tl_d2h_t  tl_dm_sba_h_d2h;

  tl_h2d_t  tl_debug_mem_d_h2d;
  tl_d2h_t  tl_debug_mem_d_d2h;

  tl_h2d_t  tl_uart_d_h2d;
  tl_d2h_t  tl_uart_d_d2h;
  tl_h2d_t  tl_gpio_d_h2d;
  tl_d2h_t  tl_gpio_d_d2h;
  tl_h2d_t  tl_spi_device_d_h2d;
  tl_d2h_t  tl_spi_device_d_d2h;
  tl_h2d_t  tl_flash_ctrl_d_h2d;
  tl_d2h_t  tl_flash_ctrl_d_d2h;
  tl_h2d_t  tl_rv_timer_d_h2d;
  tl_d2h_t  tl_rv_timer_d_d2h;
  tl_h2d_t  tl_hmac_d_h2d;
  tl_d2h_t  tl_hmac_d_d2h;
  tl_h2d_t  tl_rv_plic_d_h2d;
  tl_d2h_t  tl_rv_plic_d_d2h;

  tl_h2d_t tl_rom_d_h2d;
  tl_d2h_t tl_rom_d_d2h;
  tl_h2d_t tl_ram_main_d_h2d;
  tl_d2h_t tl_ram_main_d_d2h;
  tl_h2d_t tl_eflash_d_h2d;
  tl_d2h_t tl_eflash_d_d2h;
  logic [51:0]  intr_vector;
  // Interrupt source list
  logic intr_uart_tx_watermark;
  logic intr_uart_rx_watermark;
  logic intr_uart_tx_overflow;
  logic intr_uart_rx_overflow;
  logic intr_uart_rx_frame_err;
  logic intr_uart_rx_break_err;
  logic intr_uart_rx_timeout;
  logic intr_uart_rx_parity_err;
  logic [31:0] intr_gpio_gpio;
  logic intr_spi_device_rxf;
  logic intr_spi_device_rxlvl;
  logic intr_spi_device_txlvl;
  logic intr_spi_device_rxerr;
  logic intr_flash_ctrl_prog_empty;
  logic intr_flash_ctrl_prog_lvl;
  logic intr_flash_ctrl_rd_full;
  logic intr_flash_ctrl_rd_lvl;
  logic intr_flash_ctrl_op_done;
  logic intr_flash_ctrl_op_error;
  logic intr_rv_timer_timer_expired_0_0;
  logic intr_hmac_hmac_done;
  logic intr_hmac_fifo_full;


  logic [0:0]   irq_plic;
  logic [5:0] irq_id[1];
  logic [0:0]   msip;

  // Non-debug module reset == reset for everything except for the debug module
  // and the logic required to access it.
  logic ndmreset_n;
  logic ndmreset_from_dm;
  assign ndmreset_n = (scanmode_i) ? rst_ni : ~ndmreset_from_dm & rst_ni;

  logic debug_req;

  // processor core
  rv_core_ibex #(
    .MHPMCounterNum      (8),
    .MHPMCounterWidth    (40),
    .RV32E               (0),
    .RV32M               (1),
    .DmHaltAddr          (ADDR_SPACE_DEBUG_MEM + dm::HaltAddress),
    .DmExceptionAddr     (ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress)
  ) core (
    // clock and reset
    .clk_i                (clk_i),
    .rst_ni               (ndmreset_n),
    .test_en_i            (1'b0),
    // static pinning
    .hart_id_i            (32'b0),
    .boot_addr_i          (ADDR_SPACE_ROM),
    // TL-UL buses
    .tl_i_o               (tl_corei_h_h2d),
    .tl_i_i               (tl_corei_h_d2h),
    .tl_d_o               (tl_cored_h_h2d),
    .tl_d_i               (tl_cored_h_d2h),
    // interrupts
    .irq_software_i       (msip),
    .irq_timer_i          (intr_rv_timer_timer_expired_0_0),
    .irq_external_i       (irq_plic),
    .irq_fast_i           (15'b0),// PLIC handles all peripheral interrupts
    .irq_nm_i             (1'b0),// TODO - add and connect alert responder
    // debug interface
    .debug_req_i          (debug_req),
    // CPU control signals
    .fetch_enable_i       (1'b1),
    .core_sleep_o         ()
  );

  // Debug Module (RISC-V Debug Spec 0.13)
  //

  rv_dm #(
    .NrHarts     (  1),
    .IdcodeValue (32'h00000001) // Temporary value
                                // xxxx             version
                                // xxxxxxxxxxxxxxxx part number
                                // xxxxxxxxxxx      manufacturer id
                                // 1                required by standard
  ) u_dm_top (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .testmode_i    (1'b0),
    .ndmreset_o    (ndmreset_from_dm),
    .dmactive_o    (),
    .debug_req_o   (debug_req),
    .unavailable_i (1'b0),

    // bus device with debug memory (for execution-based debug)
    .tl_d_i        (tl_debug_mem_d_h2d),
    .tl_d_o        (tl_debug_mem_d_d2h),

    // bus host (for system bus accesses, SBA)
    .tl_h_o        (tl_dm_sba_h_h2d),
    .tl_h_i        (tl_dm_sba_h_d2h),

    //JTAG
    .tck_i            (jtag_tck_i),
    .tms_i            (jtag_tms_i),
    .trst_ni          (jtag_trst_ni),
    .td_i             (jtag_td_i),
    .td_o             (jtag_td_o),
    .tdo_oe_o         (       )
  );

  // sram device
  logic        rom_req;
  logic        rom_we;
  logic [10:0] rom_addr;
  logic [31:0] rom_wdata;
  logic [31:0] rom_wmask;
  logic [31:0] rom_rdata;
  logic        rom_rvalid;

  tlul_adapter_sram #(
    .SramAw(11),
    .SramDw(32),
    .Outstanding(1)
  ) tl_adapter_rom (
    .clk_i,
    .rst_ni   (ndmreset_n),

    .tl_i     (tl_rom_d_h2d),
    .tl_o     (tl_rom_d_d2h),

    .req_o    (rom_req),
    .gnt_i    (1'b1), // Always grant as only one requester exists
    .we_o     (rom_we),
    .addr_o   (rom_addr),
    .wdata_o  (rom_wdata),
    .wmask_o  (rom_wmask),
    .rdata_i  (rom_rdata),
    .rvalid_i (rom_rvalid),
    .rerror_i (2'b00)
  );

  prim_ram_1p #(
    .Width(32),
    .Depth(2048),
    .DataBitsPerMask(8)
  ) u_ram1p_rom (
    .clk_i,
    .rst_ni   (ndmreset_n),

    .req_i    (rom_req),
    .write_i  (rom_we),
    .addr_i   (rom_addr),
    .wdata_i  (rom_wdata),
    .wmask_i  (rom_wmask),
    .rvalid_o (rom_rvalid),
    .rdata_o  (rom_rdata)
  );
  // sram device
  logic        ram_main_req;
  logic        ram_main_we;
  logic [13:0] ram_main_addr;
  logic [31:0] ram_main_wdata;
  logic [31:0] ram_main_wmask;
  logic [31:0] ram_main_rdata;
  logic        ram_main_rvalid;

  tlul_adapter_sram #(
    .SramAw(14),
    .SramDw(32),
    .Outstanding(1)
  ) tl_adapter_ram_main (
    .clk_i,
    .rst_ni   (ndmreset_n),

    .tl_i     (tl_ram_main_d_h2d),
    .tl_o     (tl_ram_main_d_d2h),

    .req_o    (ram_main_req),
    .gnt_i    (1'b1), // Always grant as only one requester exists
    .we_o     (ram_main_we),
    .addr_o   (ram_main_addr),
    .wdata_o  (ram_main_wdata),
    .wmask_o  (ram_main_wmask),
    .rdata_i  (ram_main_rdata),
    .rvalid_i (ram_main_rvalid),
    .rerror_i (2'b00)
  );

  prim_ram_1p #(
    .Width(32),
    .Depth(16384),
    .DataBitsPerMask(8)
  ) u_ram1p_ram_main (
    .clk_i,
    .rst_ni   (ndmreset_n),

    .req_i    (ram_main_req),
    .write_i  (ram_main_we),
    .addr_i   (ram_main_addr),
    .wdata_i  (ram_main_wdata),
    .wmask_i  (ram_main_wmask),
    .rvalid_o (ram_main_rvalid),
    .rdata_o  (ram_main_rdata)
  );

  // flash controller to eflash communication
  flash_c2m_t flash_c2m;
  flash_m2c_t flash_m2c;

  // host to flash communication
  logic flash_host_req;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic [FLASH_DW-1:0] flash_host_rdata;
  logic [FLASH_AW-1:0] flash_host_addr;

  tlul_adapter_sram #(
    .SramAw(FLASH_AW),
    .SramDw(FLASH_DW),
    .Outstanding(1),
    .ByteAccess(0),
    .ErrOnWrite(1)
  ) tl_adapter_eflash (
    .clk_i,
    .rst_ni     (ndmreset_n),

    .tl_i       (tl_eflash_d_h2d),
    .tl_o       (tl_eflash_d_d2h),

    .req_o    (flash_host_req),
    .gnt_i    (flash_host_req_rdy),
    .we_o     (),
    .addr_o   (flash_host_addr),
    .wdata_o  (),
    .wmask_o  (),
    .rdata_i  (flash_host_rdata),
    .rvalid_i (flash_host_req_done),
    .rerror_i (2'b00)
  );

  flash_phy #(
    .NumBanks(FLASH_BANKS),
    .PagesPerBank(FLASH_PAGES_PER_BANK),
    .WordsPerPage(FLASH_WORDS_PER_PAGE),
    .DataWidth(32)
  ) u_flash_eflash (
    .clk_i,
    .rst_ni,
    .host_req_i      (flash_host_req),
    .host_addr_i     (flash_host_addr),
    .host_req_rdy_o  (flash_host_req_rdy),
    .host_req_done_o (flash_host_req_done),
    .host_rdata_o    (flash_host_rdata),
    .flash_ctrl_i    (flash_c2m),
    .flash_ctrl_o    (flash_m2c)
  );


  uart uart (
      .tl_i (tl_uart_d_h2d),
      .tl_o (tl_uart_d_d2h),
      .cio_rx_i (cio_uart_rx_p2d_i),
      .cio_tx_o    (cio_uart_tx_d2p_o),
      .cio_tx_en_o (cio_uart_tx_en_d2p_o),
      .intr_tx_watermark_o (intr_uart_tx_watermark),
      .intr_rx_watermark_o (intr_uart_rx_watermark),
      .intr_tx_overflow_o (intr_uart_tx_overflow),
      .intr_rx_overflow_o (intr_uart_rx_overflow),
      .intr_rx_frame_err_o (intr_uart_rx_frame_err),
      .intr_rx_break_err_o (intr_uart_rx_break_err),
      .intr_rx_timeout_o (intr_uart_rx_timeout),
      .intr_rx_parity_err_o (intr_uart_rx_parity_err),
      .clk_i(clk_i),
      .rst_ni(ndmreset_n)
  );

  gpio gpio (
      .tl_i (tl_gpio_d_h2d),
      .tl_o (tl_gpio_d_d2h),
      .cio_gpio_i (cio_gpio_gpio_p2d_i),
      .cio_gpio_o    (cio_gpio_gpio_d2p_o),
      .cio_gpio_en_o (cio_gpio_gpio_en_d2p_o),
      .intr_gpio_o (intr_gpio_gpio),
      .clk_i(clk_i),
      .rst_ni(ndmreset_n)
  );

  spi_device spi_device (
      .tl_i (tl_spi_device_d_h2d),
      .tl_o (tl_spi_device_d_d2h),
      .cio_sck_i (cio_spi_device_sck_p2d_i),
      .cio_csb_i (cio_spi_device_csb_p2d_i),
      .cio_mosi_i (cio_spi_device_mosi_p2d_i),
      .cio_miso_o    (cio_spi_device_miso_d2p_o),
      .cio_miso_en_o (cio_spi_device_miso_en_d2p_o),
      .intr_rxf_o (intr_spi_device_rxf),
      .intr_rxlvl_o (intr_spi_device_rxlvl),
      .intr_txlvl_o (intr_spi_device_txlvl),
      .intr_rxerr_o (intr_spi_device_rxerr),
      .clk_i(clk_i),
      .rst_ni(ndmreset_n)
  );

  flash_ctrl flash_ctrl (
      .tl_i (tl_flash_ctrl_d_h2d),
      .tl_o (tl_flash_ctrl_d_d2h),
      .intr_prog_empty_o (intr_flash_ctrl_prog_empty),
      .intr_prog_lvl_o (intr_flash_ctrl_prog_lvl),
      .intr_rd_full_o (intr_flash_ctrl_rd_full),
      .intr_rd_lvl_o (intr_flash_ctrl_rd_lvl),
      .intr_op_done_o (intr_flash_ctrl_op_done),
      .intr_op_error_o (intr_flash_ctrl_op_error),
      .flash_o(flash_c2m),
      .flash_i(flash_m2c),
      .clk_i(clk_i),
      .rst_ni(ndmreset_n)
  );

  rv_timer rv_timer (
      .tl_i (tl_rv_timer_d_h2d),
      .tl_o (tl_rv_timer_d_d2h),
      .intr_timer_expired_0_0_o (intr_rv_timer_timer_expired_0_0),
      .clk_i(clk_i),
      .rst_ni(ndmreset_n)
  );

  hmac hmac (
      .tl_i (tl_hmac_d_h2d),
      .tl_o (tl_hmac_d_d2h),
      .intr_hmac_done_o (intr_hmac_hmac_done),
      .intr_fifo_full_o (intr_hmac_fifo_full),
      .clk_i(clk_i),
      .rst_ni(ndmreset_n)
  );

  rv_plic #(
    .FIND_MAX("MATRIX")
  ) rv_plic (
      .tl_i (tl_rv_plic_d_h2d),
      .tl_o (tl_rv_plic_d_d2h),
      .intr_src_i (intr_vector),
      .irq_o      (irq_plic),
      .irq_id_o   (irq_id),
      .msip_o     (msip),
      .clk_i(clk_i),
      .rst_ni(ndmreset_n)
  );

  // interrupt assignments
  assign intr_vector = {
      intr_hmac_fifo_full,
      intr_hmac_hmac_done,
      intr_flash_ctrl_op_error,
      intr_flash_ctrl_op_done,
      intr_flash_ctrl_rd_lvl,
      intr_flash_ctrl_rd_full,
      intr_flash_ctrl_prog_lvl,
      intr_flash_ctrl_prog_empty,
      intr_spi_device_rxerr,
      intr_spi_device_txlvl,
      intr_spi_device_rxlvl,
      intr_spi_device_rxf,
      intr_uart_rx_parity_err,
      intr_uart_rx_timeout,
      intr_uart_rx_break_err,
      intr_uart_rx_frame_err,
      intr_uart_rx_overflow,
      intr_uart_tx_overflow,
      intr_uart_rx_watermark,
      intr_uart_tx_watermark,
      intr_gpio_gpio
  };

  // TL-UL Crossbar
  logic clk_main;
  logic ndmreset_sync_main_n;   // ndmreset synchronized to clk_main

  assign clk_main = clk_i;
  assign ndmreset_sync_main_n = ndmreset_n;

  xbar_main #(
  `ifdef FPGA_CORE_PIPE
      .s1n_corei_pass (1'h0),
      .s1n_corei_depth(4'h2),
      .s1n_cored_pass (1'h0),
      .s1n_cored_depth(4'h2)
      
  `endif
  ) u_xbar_main (
    .clk_main_i  (clk_main),
    .rst_main_ni (ndmreset_sync_main_n),

    .tl_corei_i      (tl_corei_h_h2d),
    .tl_corei_o      (tl_corei_h_d2h),
    .tl_cored_i      (tl_cored_h_h2d),
    .tl_cored_o      (tl_cored_h_d2h),
    .tl_dm_sba_i     (tl_dm_sba_h_h2d),
    .tl_dm_sba_o     (tl_dm_sba_h_d2h),
    .tl_rom_o        (tl_rom_d_h2d),
    .tl_rom_i        (tl_rom_d_d2h),
    .tl_debug_mem_o  (tl_debug_mem_d_h2d),
    .tl_debug_mem_i  (tl_debug_mem_d_d2h),
    .tl_ram_main_o   (tl_ram_main_d_h2d),
    .tl_ram_main_i   (tl_ram_main_d_d2h),
    .tl_eflash_o     (tl_eflash_d_h2d),
    .tl_eflash_i     (tl_eflash_d_d2h),
    .tl_uart_o       (tl_uart_d_h2d),
    .tl_uart_i       (tl_uart_d_d2h),
    .tl_gpio_o       (tl_gpio_d_h2d),
    .tl_gpio_i       (tl_gpio_d_d2h),
    .tl_spi_device_o (tl_spi_device_d_h2d),
    .tl_spi_device_i (tl_spi_device_d_d2h),
    .tl_flash_ctrl_o (tl_flash_ctrl_d_h2d),
    .tl_flash_ctrl_i (tl_flash_ctrl_d_d2h),
    .tl_rv_timer_o   (tl_rv_timer_d_h2d),
    .tl_rv_timer_i   (tl_rv_timer_d_d2h),
    .tl_hmac_o       (tl_hmac_d_h2d),
    .tl_hmac_i       (tl_hmac_d_d2h),
    .tl_rv_plic_o    (tl_rv_plic_d_h2d),
    .tl_rv_plic_i    (tl_rv_plic_d_d2h),

    .scanmode_i
  );

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_i, 0)

endmodule
