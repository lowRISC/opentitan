// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: USB UART core module
//

module usbuart_core (
  input        clk_i,
  input        rst_ni,
  input        clk_usb_48mhz_i,
  input        rst_usb_48mhz_ni,

  input        usbuart_reg_pkg::usbuart_reg2hw_t reg2hw,
  output       usbuart_reg_pkg::usbuart_hw2reg_t hw2reg,

  input        cio_usb_dp_i,
  output logic cio_usb_dp_o,
  output logic cio_usb_dp_en_o,

  input        cio_usb_dn_i,
  output logic cio_usb_dn_o,
  output logic cio_usb_dn_en_o,

  input        cio_usb_sense_i,

  output logic cio_usb_pullup_en_o,

  output logic intr_tx_watermark_o,
  output logic intr_rx_watermark_o,
  output logic intr_tx_overflow_o,
  output logic intr_rx_overflow_o,
  output logic intr_rx_frame_err_o,
  output logic intr_rx_break_err_o,
  output logic intr_rx_timeout_o,
  output logic intr_rx_parity_err_o
);

  import usbuart_reg_pkg::*;

  logic [7:0]    uart_rdata;
  logic          tx_fifo_rst_n, rx_fifo_rst_n;
  logic [5:0]    tx_fifo_depth, rx_fifo_depth;
  logic [5:0]    rx_fifo_depth_prev;
  // rx timeout interrupt
  logic [23:0]   rx_timeout_count, rx_timeout_count_next, uart_rxto_val;
  logic          rx_fifo_depth_changed, uart_rxto_en;

  logic          tx_enable, rx_enable;
  logic          sys_loopback;
  logic          uart_fifo_rxrst, uart_fifo_txrst;
  logic [2:0]    uart_fifo_rxilvl;
  logic [1:0]    uart_fifo_txilvl;

  logic [7:0]    usb_tx_fifo_rdata;
  logic          usb_tx_rready, usb_if_tx_read, usb_tx_rvalid;
  logic          tx_fifo_wready;
  logic          lb_data_move;
  logic [7:0]    usb_rx_fifo_wdata;
  logic [7:0]    usb_if_rx_fifo_wdata;
  logic          usb_rx_wvalid, usb_if_rx_write;
  logic          rx_fifo_rvalid, usb_rx_wready;
  logic          event_tx_watermark, event_rx_watermark, event_tx_overflow, event_rx_overflow;
  logic          event_rx_frame_err, event_rx_break_err, event_rx_timeout, event_rx_parity_err;
  logic          host_lost, host_timeout;
  logic          usb_pullup_en;

  assign tx_enable     = reg2hw.ctrl.tx.q;
  assign rx_enable     = reg2hw.ctrl.rx.q;
  assign sys_loopback  = reg2hw.ctrl.slpbk.q;
  assign usb_pullup_en = tx_enable | rx_enable;

  logic [3:0]    unused_ctrl_q;
  assign unused_ctrl_q = {reg2hw.ctrl.nf.q, reg2hw.ctrl.llpbk.q, reg2hw.ctrl.parity_en.q,
                          reg2hw.ctrl.parity_odd.q};

  // 4 cycle reset pulse
  logic [2:0]    rxres_cnt;
  logic [2:0]    txres_cnt;
  logic          uart_start_rxrst, uart_start_txrst;

  assign uart_start_rxrst  = reg2hw.fifo_ctrl.rxrst.q & reg2hw.fifo_ctrl.rxrst.qe;
  assign uart_start_txrst  = reg2hw.fifo_ctrl.txrst.q & reg2hw.fifo_ctrl.txrst.qe;
  assign uart_fifo_rxrst  = ~rxres_cnt[2];
  assign uart_fifo_txrst  = ~txres_cnt[2];

  always_ff @(posedge clk_i or negedge rst_ni)
      begin
        if (!rst_ni) begin
            txres_cnt <= 3'h0;
            rxres_cnt <= 3'h0;
        end else begin
          if (uart_start_txrst) begin
            txres_cnt <= 3'b0;
          end else if (uart_fifo_txrst) begin
            txres_cnt <= txres_cnt + 1;
          end
          if (uart_start_rxrst) begin
            rxres_cnt <= 3'b0;
          end else if (uart_fifo_rxrst) begin
            rxres_cnt <= rxres_cnt + 1;
          end
        end // else: !if(!rst_ni)
      end // always_ff @ (posedge clk_i or negedge rst_ni)

  assign uart_fifo_rxilvl = reg2hw.fifo_ctrl.rxilvl.q;
  assign uart_fifo_txilvl = reg2hw.fifo_ctrl.txilvl.q;

  logic [1:0]    unused_fifo_ctrl_qe;
  assign unused_fifo_ctrl_qe = {reg2hw.fifo_ctrl.rxilvl.qe, reg2hw.fifo_ctrl.txilvl.qe};

  logic          unused_ovrd_tx_en, unused_ovrd_tx_val;
  assign unused_ovrd_tx_en  = reg2hw.ovrd.txen.q;
  assign unused_ovrd_tx_val = reg2hw.ovrd.txval.q;

  // VAL register not used at the moment
  assign hw2reg.val.d  = 16'b0;

  assign hw2reg.rdata.d = uart_rdata;
  logic [7:0]    unused_rdata_q;
  assign unused_rdata_q = reg2hw.rdata.q;

  assign hw2reg.status.rxempty.d     = ~rx_fifo_rvalid;
  assign hw2reg.status.rxidle.d      = ~rx_fifo_rvalid; // TODO
  assign hw2reg.status.txidle.d      = ~usb_tx_rvalid;  // TODO
  assign hw2reg.status.txempty.d     = ~usb_tx_rvalid;
  assign hw2reg.status.rxfull.d      = ~usb_rx_wready;
  assign hw2reg.status.txfull.d      = ~tx_fifo_wready;

  assign hw2reg.fifo_status.txlvl.d  = tx_fifo_depth;
  assign hw2reg.fifo_status.rxlvl.d  = rx_fifo_depth;

  // resets are self-clearing, so need to update FIFO_CTRL
  assign hw2reg.fifo_ctrl.rxrst.de = reg2hw.fifo_ctrl.rxrst.q;
  assign hw2reg.fifo_ctrl.rxrst.d  = 1'b0;
  assign hw2reg.fifo_ctrl.txrst.de = reg2hw.fifo_ctrl.txrst.q;
  assign hw2reg.fifo_ctrl.txrst.d  = 1'b0;
  assign hw2reg.fifo_ctrl.rxilvl.de = 1'b0;
  assign hw2reg.fifo_ctrl.rxilvl.d  = 3'h0;
  assign hw2reg.fifo_ctrl.txilvl.de = 1'b0;
  assign hw2reg.fifo_ctrl.txilvl.d  = 2'h0;


  //              NCO 16x Baud Generator
  // output clock rate is:
  //      Fin * (NCO/2**16)
  // So, with a 16 bit accumulator, the output clock is
  //      Fin * (NCO/65536)
  logic   [16:0]     nco_sum; // extra bit to get the carry
  logic              tick_baud_x16;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni)
      nco_sum <= 17'h0;
    else if (tx_enable || rx_enable)
      nco_sum <= {1'b0,nco_sum[15:0]} + {1'b0,reg2hw.ctrl.nco.q};

  assign tick_baud_x16 = nco_sum[16];

  //////////////
  // TX Logic //
  //////////////

  // TODO: This is not a safe way to create a reset signal
  assign tx_fifo_rst_n = rst_usb_48mhz_ni & ~uart_fifo_txrst;

  // Character fifo also crosses to USB clock domain
  //`$dfifo_uart_tx->mname()`
  prim_fifo_async #(
    .Width(8),
    .Depth(32)
  ) usbuart_txfifo (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (tx_fifo_rst_n),
    .wvalid_i  (reg2hw.wdata.qe),
    .wready_o  (tx_fifo_wready),
    .wdata_i   (reg2hw.wdata.q),
    .wdepth_o  (tx_fifo_depth),

    .clk_rd_i  (clk_usb_48mhz_i),
    .rst_rd_ni (tx_fifo_rst_n), // CDC: rely on it being there a long time
    .rvalid_o  (usb_tx_rvalid),
    .rready_i  (usb_tx_rready),
    .rdata_o   (usb_tx_fifo_rdata),
    .rdepth_o  () // only using empty
  );

  //////////////
  // RX Logic //
  //////////////
  logic usb_rx_oflw;

  // TODO: This is not a safe way to create a reset signal
  assign rx_fifo_rst_n = rst_usb_48mhz_ni & ~uart_fifo_rxrst;

  //`$dfifo_uart_rx->mname()`
  prim_fifo_async #(
    .Width(8),
    .Depth(32)
  ) usbuart_rxfifo (
    .clk_wr_i  (clk_usb_48mhz_i),
    .rst_wr_ni (rx_fifo_rst_n),  // CDC: rely on it being there a long time
    .wvalid_i  (usb_rx_wvalid),
    .wready_o  (usb_rx_wready),
    .wdata_i   (usb_rx_fifo_wdata),
    .wdepth_o  (), // only using full

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rx_fifo_rst_n),
    .rvalid_o  (rx_fifo_rvalid),
    .rready_i  (reg2hw.rdata.re),
    .rdata_o   (uart_rdata),
    .rdepth_o  (rx_fifo_depth)
  );


  // Sys loopback is done at the bottom of the fifos
  // TODO could do line loopback in a similar way at top of fifos?
  always_ff @(posedge clk_usb_48mhz_i) begin
    lb_data_move <= sys_loopback & usb_tx_rvalid & usb_rx_wready & ~lb_data_move;
  end
  assign usb_tx_rready     = sys_loopback ? lb_data_move      : usb_if_tx_read;
  assign usb_rx_wvalid     = sys_loopback ? lb_data_move      : usb_if_rx_write;
  assign usb_rx_fifo_wdata = sys_loopback ? usb_tx_fifo_rdata : usb_if_rx_fifo_wdata;

  logic usb_rx_d;
  logic usb_rx_se0;
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_tx_oe;

  usbuart_usbif usbuart_usbif (
    .clk_48mhz_i (clk_usb_48mhz_i),
    .rst_ni      (rst_usb_48mhz_ni & cio_usb_sense_i), // TODO: This is not a safe way to create a
                                                       // reset signal

    .usb_d_i                (usb_rx_d),
    .usb_se0_i              (usb_rx_se0),
    .usb_d_o                (usb_tx_d),
    .usb_se0_o              (usb_tx_se0),
    .usb_oe_o               (usb_tx_oe),

    // Fifo used to communicate with system
    // fake tx always empty and rx never full when in internal loopback
    .tx_empty       (~usb_tx_rvalid & ~sys_loopback),
    .rx_full        (~usb_rx_wready & ~sys_loopback),
    .tx_read        (usb_if_tx_read),
    .rx_write       (usb_if_rx_write),
    .rx_err         (usb_rx_oflw), // RX overflow
    .rx_fifo_wdata  (usb_if_rx_fifo_wdata),
    .tx_fifo_rdata  (usb_tx_fifo_rdata),
    .status_frame_o (hw2reg.usbstat.frame.d),
    .status_host_lost_o (host_lost),
    .status_host_timeout_o (host_timeout),
    .status_device_address_o (hw2reg.usbstat.device_address.d),
    .parity_o       (hw2reg.usbparam.parity_req.d),
    .baud_o         (hw2reg.usbparam.baud_req.d)
    );
  assign hw2reg.usbstat.host_lost.d = host_lost;
  assign hw2reg.usbstat.host_timeout.d = host_timeout;

  ////////////////////////
  // Interrupt & Status //
  ////////////////////////

  always_comb
    unique case(uart_fifo_txilvl)
      2'h0:       event_tx_watermark = (tx_fifo_depth >= 6'd1);
      2'h1:       event_tx_watermark = (tx_fifo_depth >= 6'd4);
      2'h2:       event_tx_watermark = (tx_fifo_depth >= 6'd8);
      default:    event_tx_watermark = (tx_fifo_depth >= 6'd16);
      endcase


  always_comb
    unique case(uart_fifo_rxilvl)
      3'h0:       event_rx_watermark = (rx_fifo_depth >= 6'd1);
      3'h1:       event_rx_watermark = (rx_fifo_depth >= 6'd4);
      3'h2:       event_rx_watermark = (rx_fifo_depth >= 6'd8);
      3'h3:       event_rx_watermark = (rx_fifo_depth >= 6'd16);
      3'h4:       event_rx_watermark = (rx_fifo_depth >= 6'd30);
      default:    event_rx_watermark = 1'b0;
      endcase


  // rx timeout interrupt
  assign uart_rxto_en  = reg2hw.timeout_ctrl.en.q;
  assign uart_rxto_val = reg2hw.timeout_ctrl.val.q;

  assign rx_fifo_depth_changed = (rx_fifo_depth != rx_fifo_depth_prev);

  assign rx_timeout_count_next =
              // don't count if timeout feature not enabled ;
              // will never reach timeout val + lower power
              (uart_rxto_en == 1'b0)              ? 24'd0 :
              // reset count if timeout interrupt is set
              event_rx_timeout                    ? 24'd0 :
              // reset count upon change in fifo level: covers both read and receiving a new byte
              rx_fifo_depth_changed               ? 24'd0 :
              // reset count if no bytes are pending
              (rx_fifo_depth == 6'd0)             ? 24'd0 :
              // stop the count at timeout value (this will set the interrupt)
              (rx_timeout_count == uart_rxto_val) ? rx_timeout_count :
              // increment if at rx baud tick (x16 for now)
              tick_baud_x16                     ? (rx_timeout_count + 24'd1) :
              rx_timeout_count;

  assign event_rx_timeout = (rx_timeout_count == uart_rxto_val) & uart_rxto_en;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      rx_timeout_count   <= 24'd0;
      rx_fifo_depth_prev <= 6'd0;
    end else begin
      rx_timeout_count    <= rx_timeout_count_next;
      rx_fifo_depth_prev  <= rx_fifo_depth;
    end

  logic sys_usb_sense; // USB sense synced to clk_i

  assign event_rx_overflow  = usb_rx_oflw; // TODO CDC
  assign event_tx_overflow  = reg2hw.wdata.qe & (~tx_fifo_wready);
  assign event_rx_break_err = ~sys_usb_sense |
                              (reg2hw.ctrl.rxblvl.q == 0) ? host_lost : host_timeout;
  assign event_rx_frame_err = 0; // TODO is there a related USB error?
  assign event_rx_parity_err = 0; // TODO is there a related USB error?

  // instantiate interrupt hardware primitives

  prim_intr_hw #(.Width(1)) intr_hw_tx_watermark (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_tx_watermark),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tx_watermark.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tx_watermark.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tx_watermark.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tx_watermark.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tx_watermark.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tx_watermark.d),
    .intr_o                 (intr_tx_watermark_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_rx_watermark (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_watermark),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_watermark.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_watermark.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_watermark.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_watermark.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_watermark.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_watermark.d),
    .intr_o                 (intr_rx_watermark_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_tx_overflow (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_tx_overflow),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tx_overflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tx_overflow.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tx_overflow.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tx_overflow.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tx_overflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tx_overflow.d),
    .intr_o                 (intr_tx_overflow_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_rx_overflow (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_overflow),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_overflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_overflow.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_overflow.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_overflow.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_overflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_overflow.d),
    .intr_o                 (intr_rx_overflow_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_rx_frame_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_frame_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_frame_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_frame_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_frame_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_frame_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_frame_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_frame_err.d),
    .intr_o                 (intr_rx_frame_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_rx_break_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_break_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_break_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_break_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_break_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_break_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_break_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_break_err.d),
    .intr_o                 (intr_rx_break_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_rx_timeout (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_timeout),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_timeout.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_timeout.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_timeout.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_timeout.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_timeout.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_timeout.d),
    .intr_o                 (intr_rx_timeout_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_rx_parity_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_parity_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_parity_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_parity_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_parity_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_parity_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_parity_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_parity_err.d),
    .intr_o                 (intr_rx_parity_err_o)
  );

  /////////////////////////////////
  // USB IO Muxing               //
  /////////////////////////////////
  logic cio_oe;

  // Static configuration
  usbdev_reg_pkg::usbdev_reg2hw_phy_config_reg_t usb_phy_config;
  assign usb_phy_config.rx_differential_mode.q   = 1'b0;
  assign usb_phy_config.tx_differential_mode.q   = 1'b0;
  assign usb_phy_config.pinflip.q                = 1'b0;
  assign usb_phy_config.eop_single_bit.q         = 1'b1;
  assign usb_phy_config.override_pwr_sense_en.q  = 1'b0;
  assign usb_phy_config.override_pwr_sense_val.q = 1'b0;
  assign usb_phy_config.usb_ref_disable.q        = 1'b0;
  assign usb_phy_config.tx_osc_test_mode.q       = 1'b0;

  usbdev_iomux i_usbdev_iomux (
    .clk_i                  ( clk_i                  ),
    .rst_ni                 ( rst_ni                 ),
    .clk_usb_48mhz_i        ( clk_usb_48mhz_i        ),
    .rst_usb_48mhz_ni       ( rst_usb_48mhz_ni       ),

    // Register interface
    .sys_reg2hw_config_i    ( usb_phy_config         ),
    .sys_usb_sense_o        ( sys_usb_sense          ),

    // Chip IO
    .cio_usb_d_i            ( 1'b0                   ),
    .cio_usb_dp_i           ( cio_usb_dp_i           ),
    .cio_usb_dn_i           ( cio_usb_dn_i           ),
    .cio_usb_d_o            (                        ),
    .cio_usb_se0_o          (                        ),
    .cio_usb_dp_o           ( cio_usb_dp_o           ),
    .cio_usb_dn_o           ( cio_usb_dn_o           ),
    .cio_usb_oe_o           ( cio_oe                 ),
    .cio_usb_tx_mode_se_o   (                        ),
    .cio_usb_sense_i        ( cio_usb_sense_i        ),
    .cio_usb_dp_pullup_en_o ( cio_usb_pullup_en_o    ),
    .cio_usb_dn_pullup_en_o (                        ),
    .cio_usb_suspend_o      (                        ),

    // Internal interface
    .usb_rx_d_o             ( usb_rx_d               ),
    .usb_rx_se0_o           ( usb_rx_se0             ),
    .usb_tx_d_i             ( usb_tx_d               ),
    .usb_tx_se0_i           ( usb_tx_se0             ),
    .usb_tx_oe_i            ( usb_tx_oe              ),
    .usb_pwr_sense_o        (                        ),
    .usb_pullup_en_i        ( usb_pullup_en          ),
    .usb_suspend_i          ( 1'b0                   )  // not used
  );

  assign cio_usb_dp_en_o = cio_oe;
  assign cio_usb_dn_en_o = cio_oe;

endmodule
