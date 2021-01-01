// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: USB UART core module
//

module usbuart_core (
  input logic  clk_i,
  input logic  rst_ni,
  input logic  clk_usb_48mhz_i,
  input logic  rst_usb_48mhz_ni,

  input        usbuart_reg_pkg::usbuart_reg2hw_t reg2hw,
  output       usbuart_reg_pkg::usbuart_hw2reg_t hw2reg,

  input logic  usb_rx_d_i,
  input logic  usb_rx_dp_i,
  input logic  usb_rx_dn_i,
  output logic usb_tx_d_o,
  output logic usb_tx_se0_o,
  output logic usb_tx_oe_o,
  input logic  usb_pwr_sense_i,
  output logic usb_pullup_en_o,
  output logic usb_suspend_o,

  // SOF reference for clock calibration
  output logic usb_ref_val_o,
  output logic usb_ref_pulse_o,

  // Interrupts -- for testing logic list needs to match udbdev, actual match uart
  // The two lists are in the order they land in the register bits (bit 0 first)
  output logic intr_pkt_received_o, // intr_tx_watermark_o
  output logic intr_pkt_sent_o, // intr_rx_watermark_o
  output logic intr_disconnected_o, // intr_tx_empty_o
  output logic intr_host_lost_o, // intr_rx_overflow_o
  output logic intr_link_reset_o, // intr_rx_frame_err_o
  output logic intr_link_suspend_o, // intr_rx_break_err_o
  output logic intr_link_resume_o, // intr_rx_timeout_o
  output logic intr_av_empty_o, // intr_rx_parity_err_o
  output logic intr_rx_full_o,
  output logic intr_av_overflow_o,
  output logic intr_link_in_err_o,
  output logic intr_rx_crc_err_o,
  output logic intr_rx_pid_err_o,
  output logic intr_rx_bitstuff_err_o,
  output logic intr_frame_o,
  output logic intr_connected_o,
  output logic intr_link_out_err_o
);

  import usbuart_reg_pkg::*;

  localparam int       FifoDepth = 32;

  // width of param and signal should match
  localparam bit [5:0] FifoDepthForRegCompare = 6'(FifoDepth);
  logic [5:0]    tx_fifo_depth, rx_fifo_depth;
  logic [5:0]    rx_fifo_depth_prev;

  logic [7:0]    uart_rdata;
  // rx timeout interrupt
  logic [23:0]   rx_timeout_count, rx_timeout_count_next, uart_rxto_val;
  logic          rx_fifo_depth_changed, uart_rxto_en;

  logic          tx_enable, rx_enable;
  logic          uart_fifo_rxrst, uart_fifo_txrst;
  logic [2:0]    uart_fifo_rxilvl;
  logic [1:0]    uart_fifo_txilvl;

  logic [7:0]    usb_tx_fifo_rdata;
  logic          usb_tx_rready, usb_if_tx_read, usb_tx_rvalid;
  logic          tx_fifo_wready;
  logic          usb_lb_data_move;
  logic [7:0]    usb_rx_fifo_wdata;
  logic [7:0]    usb_if_rx_fifo_wdata;
  logic          usb_rx_wvalid, usb_if_rx_write;
  logic          rx_fifo_rvalid, usb_rx_wready;
  logic          usb_host_lost, usb_link_reset;
  logic          sys_pwr_sense, sys_rx_oflw, sys_host_lost, sys_link_reset, sys_link_suspend;
  logic [10:0]   usb_frame, sys_frame;
  logic          event_tx_watermark, event_rx_watermark, event_tx_empty, event_rx_overflow;
  logic          event_rx_frame_err, event_rx_break_err, event_rx_timeout;
  logic          event_rx_parity_err;


  assign tx_enable       = reg2hw.ctrl.tx.q;
  assign rx_enable       = reg2hw.ctrl.rx.q;

  // Note: this goes to an async pin so ok register is in sys clock domain
  assign usb_pullup_en_o = tx_enable | rx_enable;

  logic [3:0]    unused_ctrl_q;
  assign unused_ctrl_q = {reg2hw.ctrl.nf.q, reg2hw.ctrl.llpbk.q, reg2hw.ctrl.parity_en.q,
                          reg2hw.ctrl.parity_odd.q};

  assign uart_fifo_rxrst  = reg2hw.fifo_ctrl.rxrst.q & reg2hw.fifo_ctrl.rxrst.qe;
  assign uart_fifo_txrst  = reg2hw.fifo_ctrl.txrst.q & reg2hw.fifo_ctrl.txrst.qe;

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
  assign hw2reg.status.rxidle.d      = ~rx_fifo_rvalid;        // ignore pkt being received
  assign hw2reg.status.txidle.d      = (tx_fifo_depth == '0);  // TODO: ignores packet tail
  assign hw2reg.status.txempty.d     = (tx_fifo_depth == '0);
  assign hw2reg.status.rxfull.d      = (rx_fifo_depth == FifoDepthForRegCompare);
  assign hw2reg.status.txfull.d      = ~tx_fifo_wready;

  assign hw2reg.fifo_status.txlvl.d  = tx_fifo_depth;
  assign hw2reg.fifo_status.rxlvl.d  = rx_fifo_depth;

  // TODO: not sure why these are hrw rather than hro but that is what uart does
  assign hw2reg.fifo_ctrl.rxilvl.de = 1'b0;
  assign hw2reg.fifo_ctrl.rxilvl.d  = 3'h0;
  assign hw2reg.fifo_ctrl.txilvl.de = 1'b0;
  assign hw2reg.fifo_ctrl.txilvl.d  = 2'h0;


  // sys clk -> USB clk (arguably these are set once at init so don't need sync)
  logic usb_ref_disable, usb_rx_diff, usb_slpbk;
  prim_flop_2sync #(
    .Width      (3)
  ) cdc_sys_to_usb_ctrl (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d_i    ({reg2hw.usbctrl.ref_disable.q, reg2hw.usbctrl.rx_diff.q, reg2hw.ctrl.slpbk.q}),
    .q_o    ({usb_ref_disable,              usb_rx_diff,              usb_slpbk})
  );


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

  // Don't really reset the fifo when the register bit is set, fake by draining (in usb domain)
  logic usb_fifo_txrst, usb_tx_rvalid_raw;
  logic usb_tx_rst_pop_d, usb_tx_rst_pop_q;
  prim_pulse_sync sync_txrst (
    .clk_src_i   (clk_i),
    .clk_dst_i   (clk_usb_48mhz_i),
    .rst_src_ni  (rst_ni),
    .rst_dst_ni  (rst_usb_48mhz_ni),
    .src_pulse_i (uart_fifo_txrst),
    .dst_pulse_o (usb_fifo_txrst)
  );

  // if there is anything valid then pop each clock cycle
  assign usb_tx_rst_pop_d = (usb_tx_rst_pop_q | usb_fifo_txrst) & usb_tx_rvalid_raw;
  always_ff @(posedge clk_usb_48mhz_i or negedge rst_usb_48mhz_ni) begin
    if (!rst_usb_48mhz_ni) begin
      usb_tx_rst_pop_q <= 1'b0;
    end else begin
      usb_tx_rst_pop_q <= usb_tx_rst_pop_d;
    end
  end

  // Character fifo also crosses to USB clock domain
  //`$dfifo_uart_tx->mname()`
  prim_fifo_async #(
    .Width(8),
    .Depth(FifoDepth)
  ) usbuart_txfifo (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),
    .wvalid_i  (reg2hw.wdata.qe), // need to block if resetting is active
    .wready_o  (tx_fifo_wready),
    .wdata_i   (reg2hw.wdata.q),
    .wdepth_o  (tx_fifo_depth),

    .clk_rd_i  (clk_usb_48mhz_i),
    .rst_rd_ni (rst_usb_48mhz_ni),
    .rvalid_o  (usb_tx_rvalid_raw),
    .rready_i  (usb_tx_rready | usb_tx_rst_pop_d),
    .rdata_o   (usb_tx_fifo_rdata),
    .rdepth_o  () // only using empty
  );

  // never show valid if the fifo is being reset
  assign usb_tx_rvalid = usb_tx_rvalid_raw & ~usb_tx_rst_pop_d;

  //////////////
  // RX Logic //
  //////////////
  logic usb_rx_oflw, rx_fifo_rvalid_raw;

  // Don't really reset the fifo when the register bit is set, fake by draining it
  // if there is anything valid then pop each clock cycle
  logic rx_rst_pop_d, rx_rst_pop_q;

  assign rx_rst_pop_d = (rx_rst_pop_q | uart_fifo_rxrst) & rx_fifo_rvalid_raw;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rx_rst_pop_q <= 1'b0;
    end else begin
      rx_rst_pop_q <= rx_rst_pop_d;
    end
  end

  //`$dfifo_uart_rx->mname()`
  prim_fifo_async #(
    .Width(8),
    .Depth(FifoDepth)
  ) usbuart_rxfifo (
    .clk_wr_i  (clk_usb_48mhz_i),
    .rst_wr_ni (rst_usb_48mhz_ni),
    .wvalid_i  (usb_rx_wvalid),
    .wready_o  (usb_rx_wready),
    .wdata_i   (usb_rx_fifo_wdata),
    .wdepth_o  (), // only using full

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .rvalid_o  (rx_fifo_rvalid_raw),
    .rready_i  (reg2hw.rdata.re | rx_rst_pop_d),
    .rdata_o   (uart_rdata),
    .rdepth_o  (rx_fifo_depth)
  );

  // never show valid if the fifo is being reset
  assign rx_fifo_rvalid = rx_fifo_rvalid_raw & ~rx_rst_pop_d;

  // Sys loopback is done at the bottom of the fifos
  // TODO could do line loopback in a similar way at top of fifos?
  always_ff @(posedge clk_usb_48mhz_i) begin
    usb_lb_data_move <= usb_slpbk & usb_tx_rvalid & usb_rx_wready & ~usb_lb_data_move;
  end
  assign usb_tx_rready     = usb_slpbk ? usb_lb_data_move  : usb_if_tx_read;
  assign usb_rx_wvalid     = usb_slpbk ? usb_lb_data_move  : usb_if_rx_write;
  assign usb_rx_fifo_wdata = usb_slpbk ? usb_tx_fifo_rdata : usb_if_rx_fifo_wdata;

  usbuart_usbif usbuart_usbif (
    .clk_48mhz_i       (clk_usb_48mhz_i),
    .rst_ni            (rst_usb_48mhz_ni),

    .usb_d_i           (usb_rx_d_i),
    .usb_dp_i          (usb_rx_dp_i),
    .usb_dn_i          (usb_rx_dn_i),
    .usb_d_o           (usb_tx_d_o),
    .usb_se0_o         (usb_tx_se0_o),
    .usb_oe_o          (usb_tx_oe_o),
    .rx_diff_mode_i    (usb_rx_diff),
    // SOF reference for clock calibration
    .usb_ref_disable_i (usb_ref_disable),
    .usb_ref_val_o     (usb_ref_val_o),
    .usb_ref_pulse_o   (usb_ref_pulse_o),

    // Fifo used to communicate with system
    // fake tx always empty and rx never full when in internal loopback
    .tx_empty          (~usb_tx_rvalid & ~usb_slpbk),
    .rx_full           (~usb_rx_wready & ~usb_slpbk),
    .tx_read           (usb_if_tx_read),
    .rx_write          (usb_if_rx_write),
    .rx_err            (usb_rx_oflw), // RX overflow
    .rx_fifo_wdata     (usb_if_rx_fifo_wdata),
    .tx_fifo_rdata     (usb_tx_fifo_rdata),
    .frame_o           (usb_frame),
    .host_lost_o       (usb_host_lost),
    .link_reset_o      (usb_link_reset),
    .link_suspend_o    (usb_suspend_o),
    .device_address_o  (hw2reg.usbstat.device_address.d),  // CDC: these are static after init
    .parity_o          (hw2reg.usbparam.parity_req.d),  // CDC: these are static after init
    .baud_o            (hw2reg.usbparam.baud_req.d)  // CDC: these are static after init
    );

  ////////////////////////
  // Interrupt & Status //
  ////////////////////////
  logic           tx_watermark_d, tx_watermark_prev_q;
  logic           rx_watermark_d, rx_watermark_prev_q;

  // Because the USB will poll at discrete intervals will not have the same
  // issue with empty as in the UART case, the first write of a burst will sit in the
  // fifo until the next polling interval.
  assign event_tx_empty  = (tx_fifo_depth == 0);

  always_comb begin
    unique case(uart_fifo_txilvl)
      2'h0:       tx_watermark_d = (tx_fifo_depth < 6'd2);
      2'h1:       tx_watermark_d = (tx_fifo_depth < 6'd4);
      2'h2:       tx_watermark_d = (tx_fifo_depth < 6'd8);
      default:    tx_watermark_d = (tx_fifo_depth < 6'd16);
    endcase
  end
  assign event_tx_watermark = tx_watermark_d & ~tx_watermark_prev_q;

  always_comb begin
    unique case(uart_fifo_rxilvl)
      3'h0:       rx_watermark_d = (rx_fifo_depth >= 6'd1);
      3'h1:       rx_watermark_d = (rx_fifo_depth >= 6'd4);
      3'h2:       rx_watermark_d = (rx_fifo_depth >= 6'd8);
      3'h3:       rx_watermark_d = (rx_fifo_depth >= 6'd16);
      3'h4:       rx_watermark_d = (rx_fifo_depth >= 6'd30);
      default:    rx_watermark_d = 1'b0;
    endcase
  end

  assign event_rx_watermark = rx_watermark_d & ~rx_watermark_prev_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      tx_watermark_prev_q  <= 1'b1; // by default watermark condition is true
      rx_watermark_prev_q  <= 1'b0; // by default watermark condition is false
    end else begin
      tx_watermark_prev_q  <= tx_watermark_d;
      rx_watermark_prev_q  <= rx_watermark_d;
    end
  end

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

  // synced to clk_i

  prim_pulse_sync sync_rx_oflw (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_rx_oflw),
    .dst_pulse_o (sys_rx_oflw)
  );

  prim_flop_2sync #(
    .Width (15) // frame is 11 bits
  ) cdc_usb_to_sys (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d_i    ({usb_pwr_sense_i, usb_host_lost, usb_link_reset, usb_suspend_o,    usb_frame}),
    .q_o    ({sys_pwr_sense,   sys_host_lost, sys_link_reset, sys_link_suspend, sys_frame})
  );

  assign hw2reg.usbstat.host_lost.d = sys_host_lost;
  assign hw2reg.usbstat.link_reset.d = sys_link_reset;
  assign hw2reg.usbstat.link_suspend.d = sys_link_suspend;
  assign hw2reg.usbstat.pwr_sense.d = sys_pwr_sense;
  assign hw2reg.usbstat.frame.d = sys_frame;

  assign event_rx_overflow  = sys_rx_oflw;
  assign event_rx_break_err = sys_host_lost;
  assign event_rx_frame_err = 0; // TODO is there a related USB error?
  assign event_rx_parity_err = 0; // TODO is there a related USB error?

  // Interrupt regiser bolierplate below this point
  // Note: event uses UART terminology but interrupt matches USBDEV

  prim_intr_hw #(.Width(1)) intr_hw_pkt_received (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_tx_watermark),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.pkt_received.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.pkt_received.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.pkt_received.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.pkt_received.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.pkt_received.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.pkt_received.d),
    .intr_o                 (intr_pkt_received_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_pkt_sent (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_watermark),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.pkt_sent.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.pkt_sent.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.pkt_sent.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.pkt_sent.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.pkt_sent.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.pkt_sent.d),
    .intr_o                 (intr_pkt_sent_o)
  );

  prim_intr_hw #(.Width(1)) intr_disconnected (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_tx_empty),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.disconnected.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.disconnected.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.disconnected.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.disconnected.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.disconnected.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.disconnected.d),
    .intr_o                 (intr_disconnected_o)
  );

  prim_intr_hw #(.Width(1)) intr_connected (
    .clk_i,
    .rst_ni,
    .event_intr_i           (1'b0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.connected.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.connected.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.connected.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.connected.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.connected.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.connected.d),
    .intr_o                 (intr_connected_o)
  );

  prim_intr_hw #(.Width(1)) intr_host_lost (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_overflow),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.host_lost.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.host_lost.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.host_lost.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.host_lost.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.host_lost.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.host_lost.d),
    .intr_o                 (intr_host_lost_o)
  );

  prim_intr_hw #(.Width(1)) intr_link_reset (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_frame_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_reset.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_reset.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_reset.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_reset.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_reset.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_reset.d),
    .intr_o                 (intr_link_reset_o)
  );

  prim_intr_hw #(.Width(1)) intr_link_suspend (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_break_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_suspend.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_suspend.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_suspend.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_suspend.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_suspend.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_suspend.d),
    .intr_o                 (intr_link_suspend_o)
  );

  prim_intr_hw #(.Width(1)) intr_link_resume (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_timeout),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_resume.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_resume.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_resume.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_resume.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_resume.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_resume.d),
    .intr_o                 (intr_link_resume_o)
  );

  prim_intr_hw #(.Width(1)) intr_av_empty (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_rx_parity_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.av_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.av_empty.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.av_empty.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.av_empty.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.av_empty.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.av_empty.d),
    .intr_o                 (intr_av_empty_o)
  );

  prim_intr_hw #(.Width(1)) intr_rx_full (
    .clk_i,
    .rst_ni,
    .event_intr_i           (1'b0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_full.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_full.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_full.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_full.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_full.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_full.d),
    .intr_o                 (intr_rx_full_o)
  );

  prim_intr_hw #(.Width(1)) intr_av_overflow (
    .clk_i,
    .rst_ni,
    .event_intr_i           (1'b0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.av_overflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.av_overflow.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.av_overflow.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.av_overflow.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.av_overflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.av_overflow.d),
    .intr_o                 (intr_av_overflow_o)
  );

  prim_intr_hw #(.Width(1)) intr_link_in_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (1'b0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_in_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_in_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_in_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_in_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_in_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_in_err.d),
    .intr_o                 (intr_link_in_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_link_out_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (1'b0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_out_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_out_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_out_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_out_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_out_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_out_err.d),
    .intr_o                 (intr_link_out_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_rx_crc_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (1'b0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_crc_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_crc_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_crc_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_crc_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_crc_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_crc_err.d),
    .intr_o                 (intr_rx_crc_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_rx_pid_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (1'b0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_pid_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_pid_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_pid_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_pid_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_pid_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_pid_err.d),
    .intr_o                 (intr_rx_pid_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_rx_bitstuff_err (
    .clk_i,
    .rst_ni,
    .event_intr_i           (1'b0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_bitstuff_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_bitstuff_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_bitstuff_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_bitstuff_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_bitstuff_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_bitstuff_err.d),
    .intr_o                 (intr_rx_bitstuff_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_frame (
    .clk_i,
    .rst_ni,
    .event_intr_i           (1'b0),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.frame.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.frame.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.frame.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.frame.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.frame.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.frame.d),
    .intr_o                 (intr_frame_o)
  );

endmodule
