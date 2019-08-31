// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB Full-Speed Device Interface (usbdev).
//
//


module usbdev (
  input        clk_i,
  input        rst_ni,
  input        clk_usb_48mhz_i, // use usb_ prefix for signals in this clk
  // TODO: add a reset signal for the USB-48MHz clock domain here

  // Register interface
  input        tlul_pkg::tl_h2d_t tl_d_i,
  output       tlul_pkg::tl_d2h_t tl_d_o,

  // USB Interface
  input        cio_usb_dp_i,
  output logic cio_usb_dp_o,
  output logic cio_usb_dp_en_o,

  input        cio_usb_dn_i,
  output logic cio_usb_dn_o,
  output logic cio_usb_dn_en_o,

  input        cio_usb_sense_i,

  output logic cio_usb_pullup_o,
  output logic cio_usb_pullup_en_o,

  // Interrupts
  output logic intr_pkt_received_o, // Packet received
  output logic intr_pkt_sent_o, // Packet sent
  output logic intr_disconnected_o,
  output logic intr_host_lost_o,
  output logic intr_link_reset_o,
  output logic intr_link_suspend_o,
  output logic intr_link_resume_o,
  output logic intr_av_empty_o,
  output logic intr_rx_full_o,
  output logic intr_av_overflow_o
);

  import usbdev_reg_pkg::*;

  // Could make SramDepth, MaxPktSizeByte, AVFifoDepth and RXFifoDepth
  // module parameters but may need to fix register def for the first two
  localparam int SramDw = 32; // Places packing bytes to SRAM assume this
  localparam int SramDepth = 512; // 2kB, SRAM Width is DW
  localparam int MaxPktSizeByte = 64;

  localparam int SramAw = $clog2(SramDepth);
  localparam int SizeWidth = $clog2(MaxPktSizeByte);
  localparam int NBuf = (SramDepth * SramDw) / (MaxPktSizeByte * 8);
  localparam int NBufWidth = $clog2(NBuf);

  // AV fifo just stores buffer numbers
  localparam int AVFifoWidth = NBufWidth;
  localparam int AVFifoDepth = 4;

  // RX fifo stores              buf# +  size(0-MaxPktSizeByte)  + EP# + Type
  localparam int RXFifoWidth = NBufWidth + (1+SizeWidth)         +  4  + 1;
  localparam int RXFifoDepth = 4;

  usbdev_reg2hw_t reg2hw;
  usbdev_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t tl_sram_h2d [1];
  tlul_pkg::tl_d2h_t tl_sram_d2h [1];

  // Dual-port SRAM Interface: Refer prim_ram_2p_wrapper.sv
  logic              mem_a_req;
  logic              mem_a_write;
  logic [SramAw-1:0] mem_a_addr;
  logic [SramDw-1:0] mem_a_wdata;
  logic              mem_a_rvalid;
  logic [SramDw-1:0] mem_a_rdata;
  logic [1:0]        mem_a_rerror;

  logic              usb_mem_b_req;
  logic              usb_mem_b_write;
  logic [SramAw-1:0] usb_mem_b_addr;
  logic [SramDw-1:0] usb_mem_b_wdata;
  logic [SramDw-1:0] usb_mem_b_rdata;

  logic              usb_clr_devaddr;
  logic              event_av_empty, event_av_overflow, event_rx_full;
  logic              usb_event_link_reset, usb_event_link_suspend, usb_event_link_resume;
  logic              usb_event_host_lost, usb_event_disconnect;
  logic              event_link_reset, event_link_suspend, event_link_resume;
  logic              event_host_lost, event_disconnect;

  //=======================================================================
  // Receive interface fifos
  //

  logic              av_fifo_wready;
  logic              event_pkt_received;
  logic              usbdev_rst_n;
  logic              usb_av_rvalid, usb_av_rready;
  logic              usb_rx_wvalid, usb_rx_wready;
  logic              rx_fifo_rvalid;

  logic [AVFifoWidth - 1:0] usb_av_rdata;
  logic [RXFifoWidth - 1:0] usb_rx_wdata, rx_rdata;

  assign event_av_overflow = reg2hw.avbuffer.qe & (~av_fifo_wready);
  assign usbdev_rst_n = rst_ni;
  assign hw2reg.usbstat.av_full.d = ~av_fifo_wready;
  assign hw2reg.usbstat.rx_empty.d = ~rx_fifo_rvalid;

  prim_fifo_async #(
    .Width(AVFifoWidth),
    .Depth(AVFifoDepth)
  ) usbdev_avfifo (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (usbdev_rst_n),

    .wvalid    (reg2hw.avbuffer.qe),
    .wready    (av_fifo_wready),
    .wdata     (reg2hw.avbuffer.q),
    .wdepth    (hw2reg.usbstat.av_depth.d),

    .clk_rd_i  (clk_usb_48mhz_i),
    .rst_rd_ni (usbdev_rst_n), // CDC: rely on it being there a long time
    .rvalid    (usb_av_rvalid),
    .rready    (usb_av_rready),
    .rdata     (usb_av_rdata),
    .rdepth    () // only using empty
  );

  prim_fifo_async #(
    .Width(RXFifoWidth),
    .Depth(RXFifoDepth)
  ) usbdev_rxfifo (
    .clk_wr_i  (clk_usb_48mhz_i),
    .rst_wr_ni (usbdev_rst_n),  // CDC: rely on it being there a long time

    .wvalid    (usb_rx_wvalid),
    .wready    (usb_rx_wready),
    .wdata     (usb_rx_wdata),
    .wdepth    (),

    .clk_rd_i  (clk_i),
    .rst_rd_ni (usbdev_rst_n),
    .rvalid    (rx_fifo_rvalid),
    .rready    (reg2hw.rxfifo.buffer.re),
    .rdata     (rx_rdata),
    .rdepth    (hw2reg.usbstat.rx_depth.d)
  );
  assign hw2reg.rxfifo.ep.d = rx_rdata[16:13];
  assign hw2reg.rxfifo.setup.d = rx_rdata[12];
  assign hw2reg.rxfifo.size.d = rx_rdata[11:5];
  assign hw2reg.rxfifo.buffer.d = rx_rdata[4:0];
  assign event_pkt_received = rx_fifo_rvalid;
  logic [2:0]               unused_re;
  assign unused_re = {reg2hw.rxfifo.ep.re, reg2hw.rxfifo.setup.re, reg2hw.rxfifo.size.re};
  //======================================================================
  // IN (Transmit) interface config
  //
  logic [NBufWidth - 1:0] usb_in_buf [12];
  logic [SizeWidth:0] usb_in_size [12];
  logic [3:0]         usb_in_endpoint;
  logic [11:0] ep_stall, usb_in_rdy;
  logic [11:0] clear_rdybit, set_sentbit, update_pend;
  logic        usb_out_clear_rdy, out_clear_rdy, usb_set_sent, set_sent;
  logic [11:0] enable_setup, enable_out;

  assign enable_setup =  {
      reg2hw.rxenable.setup11.q, reg2hw.rxenable.setup10.q,
      reg2hw.rxenable.setup9.q, reg2hw.rxenable.setup8.q,
      reg2hw.rxenable.setup7.q, reg2hw.rxenable.setup6.q,
      reg2hw.rxenable.setup5.q, reg2hw.rxenable.setup4.q,
      reg2hw.rxenable.setup3.q, reg2hw.rxenable.setup2.q,
      reg2hw.rxenable.setup1.q, reg2hw.rxenable.setup0.q};
  assign enable_out =  {
      reg2hw.rxenable.out11.q, reg2hw.rxenable.out10.q,
      reg2hw.rxenable.out9.q, reg2hw.rxenable.out8.q,
      reg2hw.rxenable.out7.q, reg2hw.rxenable.out6.q,
      reg2hw.rxenable.out5.q, reg2hw.rxenable.out4.q,
      reg2hw.rxenable.out3.q, reg2hw.rxenable.out2.q,
      reg2hw.rxenable.out1.q, reg2hw.rxenable.out0.q};

  // STALL for both directions
  assign ep_stall =  {
      reg2hw.stall.stall11.q, reg2hw.stall.stall10.q,
      reg2hw.stall.stall9.q, reg2hw.stall.stall8.q,
      reg2hw.stall.stall7.q, reg2hw.stall.stall6.q,
      reg2hw.stall.stall5.q, reg2hw.stall.stall4.q,
      reg2hw.stall.stall3.q, reg2hw.stall.stall2.q,
      reg2hw.stall.stall1.q, reg2hw.stall.stall0.q};

  // Clock domain crossing fifo for ready bit covers others so assigns are ok
  assign usb_in_buf[0] = reg2hw.configin0.buffer0.q;
  assign usb_in_size[0] = reg2hw.configin0.size0.q;
  assign usb_in_buf[1] = reg2hw.configin1.buffer1.q;
  assign usb_in_size[1] = reg2hw.configin1.size1.q;
  assign usb_in_buf[2] = reg2hw.configin2.buffer2.q;
  assign usb_in_size[2] = reg2hw.configin2.size2.q;
  assign usb_in_buf[3] = reg2hw.configin3.buffer3.q;
  assign usb_in_size[3] = reg2hw.configin3.size3.q;
  assign usb_in_buf[4] = reg2hw.configin4.buffer4.q;
  assign usb_in_size[4] = reg2hw.configin4.size4.q;
  assign usb_in_buf[5] = reg2hw.configin5.buffer5.q;
  assign usb_in_size[5] = reg2hw.configin5.size5.q;
  assign usb_in_buf[6] = reg2hw.configin6.buffer6.q;
  assign usb_in_size[6] = reg2hw.configin6.size6.q;
  assign usb_in_buf[7] = reg2hw.configin7.buffer7.q;
  assign usb_in_size[7] = reg2hw.configin7.size7.q;
  assign usb_in_buf[8] = reg2hw.configin8.buffer8.q;
  assign usb_in_size[8] = reg2hw.configin8.size8.q;
  assign usb_in_buf[9] = reg2hw.configin9.buffer9.q;
  assign usb_in_size[9] = reg2hw.configin9.size9.q;
  assign usb_in_buf[10] = reg2hw.configin10.buffer10.q;
  assign usb_in_size[10] = reg2hw.configin10.size10.q;
  assign usb_in_buf[11] = reg2hw.configin11.buffer11.q;
  assign usb_in_size[11] = reg2hw.configin11.size11.q;

  prim_flop_2sync #(
    .Width(12)
  ) usbdev_rdysync (
    .clk_i (clk_usb_48mhz_i),
    .rst_ni (rst_ni),
    .d( {reg2hw.configin11.rdy11.q, reg2hw.configin10.rdy10.q,
         reg2hw.configin9.rdy9.q,   reg2hw.configin8.rdy8.q,
         reg2hw.configin7.rdy7.q,   reg2hw.configin6.rdy6.q,
         reg2hw.configin5.rdy5.q,   reg2hw.configin4.rdy4.q,
         reg2hw.configin3.rdy3.q,   reg2hw.configin2.rdy2.q,
         reg2hw.configin1.rdy1.q,   reg2hw.configin0.rdy0.q }),
    .q(usb_in_rdy)
  );

  // Clear of ready and set of sent is a pulse in USB clock domain
  // but needs to ensure register bit is cleared/set in TLUL domain
  // usbdev_pulsesync takes pulse in clk_src to pulse in clk_dst
  prim_pulse_sync usbdev_setsent (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_set_sent),
    .dst_pulse_o (set_sent)
  );

  always_comb begin
    set_sentbit = 12'b0;
    if (set_sent) begin
      // syncronization of set_sent ensures usb_endpoint is stable
      set_sentbit[usb_in_endpoint] = 1; // lint: usb_in_endpoint range was checked
    end
  end
  assign {hw2reg.in_sent.sent11.de,  hw2reg.in_sent.sent10.de,
         hw2reg.in_sent.sent9.de,   hw2reg.in_sent.sent8.de,
         hw2reg.in_sent.sent7.de,   hw2reg.in_sent.sent6.de,
         hw2reg.in_sent.sent5.de,   hw2reg.in_sent.sent4.de,
         hw2reg.in_sent.sent3.de,   hw2reg.in_sent.sent2.de,
         hw2reg.in_sent.sent1.de,   hw2reg.in_sent.sent0.de } = set_sentbit;
  assign {hw2reg.in_sent.sent11.d,  hw2reg.in_sent.sent10.d,
          hw2reg.in_sent.sent9.d,   hw2reg.in_sent.sent8.d,
          hw2reg.in_sent.sent7.d,   hw2reg.in_sent.sent6.d,
          hw2reg.in_sent.sent5.d,   hw2reg.in_sent.sent4.d,
          hw2reg.in_sent.sent3.d,   hw2reg.in_sent.sent2.d,
          hw2reg.in_sent.sent1.d,   hw2reg.in_sent.sent0.d } = 12'hfff;

  prim_pulse_sync usbdev_outrdyclr (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_out_clear_rdy),
    .dst_pulse_o (out_clear_rdy)
  );

  logic event_link_reset_q;

  always_ff @(posedge clk_usb_48mhz_i or negedge rst_ni) begin
    if (!rst_ni) begin
      event_link_reset_q <= 0;
    end else begin
      event_link_reset_q <= event_link_reset;
    end
  end

  always_comb begin
    clear_rdybit = 12'b0;
    update_pend  = 12'b0;
    if (event_link_reset && !event_link_reset_q) begin
      clear_rdybit = 12'hfff;
      update_pend  = 12'hfff;
    end else begin
      clear_rdybit[usb_in_endpoint] = set_sent | out_clear_rdy;  // lint: usb_in_endpoint range was checked
      update_pend[usb_in_endpoint]  = out_clear_rdy;  // lint: usb_in_endpoint range was checked
    end
  end
  assign {hw2reg.configin11.rdy11.de, hw2reg.configin10.rdy10.de,
          hw2reg.configin9.rdy9.de,   hw2reg.configin8.rdy8.de,
          hw2reg.configin7.rdy7.de,   hw2reg.configin6.rdy6.de,
          hw2reg.configin5.rdy5.de,   hw2reg.configin4.rdy4.de,
          hw2reg.configin3.rdy3.de,   hw2reg.configin2.rdy2.de,
          hw2reg.configin1.rdy1.de,   hw2reg.configin0.rdy0.de } = clear_rdybit;

  assign {hw2reg.configin11.rdy11.d, hw2reg.configin10.rdy10.d,
          hw2reg.configin9.rdy9.d,   hw2reg.configin8.rdy8.d,
          hw2reg.configin7.rdy7.d,   hw2reg.configin6.rdy6.d,
          hw2reg.configin5.rdy5.d,   hw2reg.configin4.rdy4.d,
          hw2reg.configin3.rdy3.d,   hw2reg.configin2.rdy2.d,
          hw2reg.configin1.rdy1.d,   hw2reg.configin0.rdy0.d } = 12'b0;

  // Update the pending bit by copying the ready bit that is about to clear
  assign {hw2reg.configin11.pend11.de, hw2reg.configin10.pend10.de,
          hw2reg.configin9.pend9.de,   hw2reg.configin8.pend8.de,
          hw2reg.configin7.pend7.de,   hw2reg.configin6.pend6.de,
          hw2reg.configin5.pend5.de,   hw2reg.configin4.pend4.de,
          hw2reg.configin3.pend3.de,   hw2reg.configin2.pend2.de,
          hw2reg.configin1.pend1.de,   hw2reg.configin0.pend0.de } = update_pend;

  assign hw2reg.configin11.pend11.d = reg2hw.configin11.rdy11.q | reg2hw.configin11.pend11.q;
  assign hw2reg.configin10.pend10.d = reg2hw.configin10.rdy10.q | reg2hw.configin10.pend10.q;
  assign hw2reg.configin9.pend9.d   = reg2hw.configin9.rdy9.q   | reg2hw.configin9.pend9.q;
  assign hw2reg.configin8.pend8.d   = reg2hw.configin8.rdy8.q   | reg2hw.configin8.pend8.q;
  assign hw2reg.configin7.pend7.d   = reg2hw.configin7.rdy7.q   | reg2hw.configin7.pend7.q;
  assign hw2reg.configin6.pend6.d   = reg2hw.configin6.rdy6.q   | reg2hw.configin6.pend6.q;
  assign hw2reg.configin5.pend5.d   = reg2hw.configin5.rdy5.q   | reg2hw.configin5.pend5.q;
  assign hw2reg.configin4.pend4.d   = reg2hw.configin4.rdy4.q   | reg2hw.configin4.pend4.q;
  assign hw2reg.configin3.pend3.d   = reg2hw.configin3.rdy3.q   | reg2hw.configin3.pend3.q;
  assign hw2reg.configin2.pend2.d   = reg2hw.configin2.rdy2.q   | reg2hw.configin2.pend2.q;
  assign hw2reg.configin1.pend1.d   = reg2hw.configin1.rdy1.q   | reg2hw.configin1.pend1.q;
  assign hw2reg.configin0.pend0.d   = reg2hw.configin0.rdy0.q   | reg2hw.configin0.pend0.q;

  //======================================================================
  // USB interface -- everything is in USB clock domain

  assign hw2reg.usbstat.usb_sense.d = cio_usb_sense_i;

  usbdev_usbif #(
    .AVFifoWidth    (AVFifoWidth),
    .RXFifoWidth    (RXFifoWidth),
    .MaxPktSizeByte (MaxPktSizeByte),
    .NBuf           (NBuf),
    .SramAw         (SramAw)
  ) usbdev_impl (
    .clk_48mhz_i     (clk_usb_48mhz_i),
    .rst_ni          (usbdev_rst_n),

    // Pins
    .usb_dp_i        (cio_usb_dp_i),
    .usb_dp_o        (cio_usb_dp_o),
    .usb_dp_en_o     (cio_usb_dp_en_o),
    .usb_dn_i        (cio_usb_dn_i),
    .usb_dn_o        (cio_usb_dn_o),
    .usb_dn_en_o     (cio_usb_dn_en_o),
    .usb_sense_i     (cio_usb_sense_i),
    .usb_pullup_o    (cio_usb_pullup_o),
    .usb_pullup_en_o (cio_usb_pullup_en_o),

    // receive side
    .rx_setup_i      (enable_setup),
    .rx_out_i        (enable_out),
    .rx_stall_i      (ep_stall),
    .av_rvalid_i     (usb_av_rvalid),
    .av_rready_o     (usb_av_rready),
    .av_rdata_i      (usb_av_rdata),
    .event_av_empty_o(event_av_empty),

    .rx_wvalid_o     (usb_rx_wvalid),
    .rx_wready_i     (usb_rx_wready),
    .rx_wdata_o      (usb_rx_wdata),
    .event_rx_full_o (event_rx_full),
    .out_clear_rdy_o (usb_out_clear_rdy),
    .out_endpoint_o  (),

    // transmit side
    .in_buf_i        (usb_in_buf[usb_in_endpoint]),  // lint: usb_in_endpoint range was checked
    .in_size_i       (usb_in_size[usb_in_endpoint]),  // lint: usb_in_endpoint range was checked
    .in_stall_i      (ep_stall),
    .in_rdy_i        (usb_in_rdy),
    .set_sent_o      (usb_set_sent),
    .in_endpoint_o   (usb_in_endpoint),

    // memory
    .mem_req_o       (usb_mem_b_req),
    .mem_write_o     (usb_mem_b_write),
    .mem_addr_o      (usb_mem_b_addr),
    .mem_wdata_o     (usb_mem_b_wdata),
    .mem_rdata_i     (usb_mem_b_rdata),

    // control
    .enable_i        (reg2hw.usbctrl.enable.q),
    .devaddr_i       (reg2hw.usbctrl.device_address.q),
    .clr_devaddr_o   (usb_clr_devaddr),

    // status
    .frame_o         (hw2reg.usbstat.frame.d),
    .link_state_o    (hw2reg.usbstat.link_state.d),
    .link_disconnect_o(usb_event_disconnect),
    .link_reset_o    (usb_event_link_reset),
    .link_suspend_o  (usb_event_link_suspend),
    .link_resume_o   (usb_event_link_resume),
    .host_lost_o     (usb_event_host_lost)
  );

  // CDC for event signals (arguably they are there for a long time so would be ok)
  // Just want a pulse to ensure only one interrupt for an event
  usbdev_flop_2syncpulse #(.Width(4)) syncevent (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d      ({usb_event_disconnect, usb_event_link_reset, usb_event_link_suspend,
              usb_event_host_lost}),
    .q      ({event_disconnect, event_link_reset, event_link_suspend, event_host_lost})
  );

  // Resume is a single pulse so needs pulsesync
  prim_pulse_sync usbdev_resume (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_link_resume),
    .dst_pulse_o (event_link_resume)
  );

  assign hw2reg.usbstat.host_lost.d = event_host_lost;

  // resets etc cause the device address to clear
  prim_pulse_sync usbdev_devclr (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_clr_devaddr),
    .dst_pulse_o (hw2reg.usbctrl.device_address.de)
  );
  assign hw2reg.usbctrl.device_address.d = '0;


  //======================================================================

  logic        unused_mem_a_rerror_d;

  tlul_adapter_sram #(
    .SramAw(SramAw)
  ) u_tlul2sram (
    .clk_i,
    .rst_ni,

    .tl_i     (tl_sram_h2d [0]),
    .tl_o     (tl_sram_d2h [0]),

    .req_o    (mem_a_req),
    .gnt_i    (mem_a_req),  //Always grant when request
    .we_o     (mem_a_write),
    .addr_o   (mem_a_addr),
    .wdata_o  (mem_a_wdata),
    .wmask_o  (),           // Not used
    .rdata_i  (mem_a_rdata),
    .rvalid_i (mem_a_rvalid),
    .rerror_i (mem_a_rerror)
  );

  assign unused_mem_a_rerror_d = mem_a_rerror[1] ; // Only uncorrectable error

  // SRAM Wrapper
  prim_ram_2p_async_adv #(
    .Depth (SramDepth),
    .Width (SramDw),    // 32 x 512 --> 2kB
    .CfgW  (8),

    .EnableECC           (1), // No Protection
    .EnableParity        (0),
    .EnableInputPipeline (0),
    .EnableOutputPipeline(0),

    .MemT ("REGISTER")
  ) u_memory_2p (
    .clk_a_i    (clk_i),
    .clk_b_i    (clk_usb_48mhz_i),
    .rst_ni     (rst_ni),
    .a_req_i    (mem_a_req),
    .a_write_i  (mem_a_write),
    .a_addr_i   (mem_a_addr),
    .a_wdata_i  (mem_a_wdata),
    .a_rvalid_o (mem_a_rvalid),
    .a_rdata_o  (mem_a_rdata),
    .a_rerror_o (mem_a_rerror),

    .b_req_i    (usb_mem_b_req),
    .b_write_i  (usb_mem_b_write),
    .b_addr_i   (usb_mem_b_addr),
    .b_wdata_i  (usb_mem_b_wdata),
    .b_rvalid_o (),
    .b_rdata_o  (usb_mem_b_rdata),
    .b_rerror_o (),

    .cfg_i      ('0)
  );

  // Register module
  usbdev_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i (tl_d_i),
    .tl_o (tl_d_o),

    .tl_win_o (tl_sram_h2d),
    .tl_win_i (tl_sram_d2h),

    .reg2hw,
    .hw2reg
  );

  prim_intr_hw #(.Width(1)) intr_hw_pkt_received (
    .event_intr_i           (event_pkt_received),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.pkt_received.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.pkt_received.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.pkt_received.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.pkt_received.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.pkt_received.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.pkt_received.d),
    .intr_o                 (intr_pkt_received_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_pkt_sent (
    .event_intr_i           (set_sent),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.pkt_sent.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.pkt_sent.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.pkt_sent.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.pkt_sent.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.pkt_sent.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.pkt_sent.d),
    .intr_o                 (intr_pkt_sent_o)
  );

  prim_intr_hw #(.Width(1)) intr_disconnected (
    .event_intr_i           (event_disconnect),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.disconnected.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.disconnected.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.disconnected.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.disconnected.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.disconnected.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.disconnected.d),
    .intr_o                 (intr_disconnected_o)
  );

  prim_intr_hw #(.Width(1)) intr_host_lost (
    .event_intr_i           (event_host_lost),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.host_lost.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.host_lost.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.host_lost.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.host_lost.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.host_lost.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.host_lost.d),
    .intr_o                 (intr_host_lost_o)
  );

  prim_intr_hw #(.Width(1)) intr_link_reset (
    .event_intr_i           (event_link_reset),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_reset.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_reset.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_reset.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_reset.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_reset.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_reset.d),
    .intr_o                 (intr_link_reset_o)
  );

  prim_intr_hw #(.Width(1)) intr_link_suspend (
    .event_intr_i           (event_link_suspend),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_suspend.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_suspend.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_suspend.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_suspend.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_suspend.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_suspend.d),
    .intr_o                 (intr_link_suspend_o)
  );

  prim_intr_hw #(.Width(1)) intr_link_resume (
    .event_intr_i           (event_link_resume),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_resume.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_resume.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_resume.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_resume.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_resume.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_resume.d),
    .intr_o                 (intr_link_resume_o)
  );

  prim_intr_hw #(.Width(1)) intr_av_empty (
    .event_intr_i           (event_av_empty),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.av_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.av_empty.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.av_empty.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.av_empty.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.av_empty.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.av_empty.d),
    .intr_o                 (intr_av_empty_o)
  );

  prim_intr_hw #(.Width(1)) intr_rx_full (
    .event_intr_i           (event_rx_full),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_full.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_full.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_full.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_full.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_full.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_full.d),
    .intr_o                 (intr_rx_full_o)
  );

  prim_intr_hw #(.Width(1)) intr_av_overflow (
    .event_intr_i           (event_av_overflow),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.av_overflow.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.av_overflow.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.av_overflow.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.av_overflow.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.av_overflow.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.av_overflow.d),
    .intr_o                 (intr_av_overflow_o)
  );

endmodule
