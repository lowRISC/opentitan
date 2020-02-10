// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB Full-Speed Device Interface (usbdev).
//
//


module usbdev (
  input  logic       clk_i,
  input  logic       rst_ni,
  input  logic       clk_usb_48mhz_i, // use usb_ prefix for signals in this clk
  input  logic       rst_usb_48mhz_ni, // async reset, with relase sync to clk_usb_48_mhz_i

  // Register interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // USB Interface
  input  logic       cio_d_i,
  input  logic       cio_dp_i,
  input  logic       cio_dn_i,

  output logic       cio_d_o,
  output logic       cio_se0_o,
  output logic       cio_dp_o,
  output logic       cio_dn_o,
  output logic       cio_oe_o,

  output logic       cio_tx_mode_se_o,
  input  logic       cio_sense_i,
  output logic       cio_pullup_en_o,
  output logic       cio_suspend_o,

  // Interrupts
  output logic       intr_pkt_received_o, // Packet received
  output logic       intr_pkt_sent_o, // Packet sent
  output logic       intr_connected_o,
  output logic       intr_disconnected_o,
  output logic       intr_host_lost_o,
  output logic       intr_link_reset_o,
  output logic       intr_link_suspend_o,
  output logic       intr_link_resume_o,
  output logic       intr_av_empty_o,
  output logic       intr_rx_full_o,
  output logic       intr_av_overflow_o,
  output logic       intr_link_in_err_o,
  output logic       intr_rx_crc_err_o,
  output logic       intr_rx_pid_err_o,
  output logic       intr_rx_bitstuff_err_o,
  output logic       intr_frame_o
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

  // Number of endpoints
  localparam int NEndpoints = usbdev_reg_pkg::NEndpoints;

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
  logic              usb_event_av_empty, event_av_overflow, usb_event_rx_full;
  logic              event_av_empty, event_rx_full;
  logic              usb_event_link_reset, usb_event_link_suspend, usb_event_link_resume;
  logic              usb_event_host_lost, usb_event_disconnect, usb_event_connect;
  logic              usb_event_rx_crc_err, usb_event_rx_pid_err;
  logic              usb_event_rx_bitstuff_err;
  logic              usb_event_in_err;
  logic              usb_event_frame;

  logic              event_link_reset, event_link_suspend, event_link_resume;
  logic              event_host_lost, event_disconnect, event_connect;
  logic              event_rx_crc_err, event_rx_pid_err;
  logic              event_rx_bitstuff_err;
  logic              event_in_err;
  logic              event_frame;

  // CDC signals
  logic [10:0]       usb_frame;
  logic [2:0]        usb_link_state;
  logic              usb_enable;
  logic [6:0]        usb_device_addr;

  logic                  usb_data_toggle_clear_en;
  logic [NEndpoints-1:0] usb_data_toggle_clear;


  /////////////////////////////////
  // USB IO after CDC & muxing   //
  /////////////////////////////////
  logic usb_rx_d;
  logic usb_rx_se0;
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_tx_oe;
  logic usb_pwr_sense;
  logic usb_pullup_en;

  /////////////////////////////
  // Receive interface fifos //
  /////////////////////////////

  logic              av_fifo_wready;
  logic              event_pkt_received;
  logic              usb_av_rvalid, usb_av_rready;
  logic              usb_rx_wvalid, usb_rx_wready;
  logic              rx_fifo_rvalid;

  logic [AVFifoWidth - 1:0] usb_av_rdata;
  logic [RXFifoWidth - 1:0] usb_rx_wdata, rx_rdata_raw, rx_rdata;

  assign event_av_overflow = reg2hw.avbuffer.qe & (~av_fifo_wready);
  assign hw2reg.usbstat.av_full.d = ~av_fifo_wready;
  assign hw2reg.usbstat.rx_empty.d = ~rx_fifo_rvalid;

  prim_fifo_async #(
    .Width(AVFifoWidth),
    .Depth(AVFifoDepth)
  ) usbdev_avfifo (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),

    .wvalid    (reg2hw.avbuffer.qe),
    .wready    (av_fifo_wready),
    .wdata     (reg2hw.avbuffer.q),
    .wdepth    (hw2reg.usbstat.av_depth.d),

    .clk_rd_i  (clk_usb_48mhz_i),
    .rst_rd_ni (rst_usb_48mhz_ni),
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
    .rst_wr_ni (rst_usb_48mhz_ni),

    .wvalid    (usb_rx_wvalid),
    .wready    (usb_rx_wready),
    .wdata     (usb_rx_wdata),
    .wdepth    (),

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .rvalid    (rx_fifo_rvalid),
    .rready    (reg2hw.rxfifo.buffer.re),
    .rdata     (rx_rdata_raw),
    .rdepth    (hw2reg.usbstat.rx_depth.d)
  );

  // Return all zero if the FIFO is empty (instead of X)
  assign rx_rdata = rx_fifo_rvalid ? rx_rdata_raw : '0;
  assign hw2reg.rxfifo.ep.d = rx_rdata[16:13];
  assign hw2reg.rxfifo.setup.d = rx_rdata[12];
  assign hw2reg.rxfifo.size.d = rx_rdata[11:5];
  assign hw2reg.rxfifo.buffer.d = rx_rdata[4:0];
  assign event_pkt_received = rx_fifo_rvalid;
  logic [2:0]               unused_re;
  assign unused_re = {reg2hw.rxfifo.ep.re, reg2hw.rxfifo.setup.re, reg2hw.rxfifo.size.re};

  ////////////////////////////////////
  // IN (Transmit) interface config //
  ////////////////////////////////////
  logic [NBufWidth-1:0]  usb_in_buf [NEndpoints];
  logic [SizeWidth:0]    usb_in_size [NEndpoints];
  logic [3:0]            usb_in_endpoint;
  logic [NEndpoints-1:0] usb_in_rdy;
  logic [NEndpoints-1:0] clear_rdybit, set_sentbit, update_pend;
  logic                  usb_setup_received, setup_received, usb_set_sent, set_sent;
  logic [NEndpoints-1:0] ep_iso;
  logic [NEndpoints-1:0] enable_setup, enable_out, ep_stall;
  logic [NEndpoints-1:0] usb_enable_setup, usb_enable_out, usb_ep_stall;
  logic [NEndpoints-1:0] in_rdy_async;
  logic [3:0]            usb_out_endpoint;

  // RX enables
  always_comb begin : proc_map_rxenable
    for (int i = 0; i < NEndpoints; i++) begin
      enable_setup[i] = reg2hw.rxenable_setup[i].q;
      enable_out[i]   = reg2hw.rxenable_out[i].q;
    end
  end

  // STALL for both directions
  always_comb begin : proc_map_stall
    for (int i = 0; i < NEndpoints; i++) begin
      ep_stall[i] = reg2hw.stall[i];
    end
  end

  prim_flop_2sync #(
    .Width(3*NEndpoints)
  ) usbdev_sync_ep_cfg (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d      ({enable_setup, enable_out, ep_stall}),
    .q      ({usb_enable_setup, usb_enable_out, usb_ep_stall})
  );

  // CDC: ok, quasi-static
  always_comb begin : proc_map_iso
    for (int i = 0; i < NEndpoints; i++) begin
      ep_iso[i] = reg2hw.iso[i].q;
    end
  end

  // CDC: flop_2sync for ready bit covers others so assigns are ok
  always_comb begin : proc_map_buf_size
    for (int i = 0; i < NEndpoints; i++) begin
      usb_in_buf[i]  = reg2hw.configin[i].buffer.q;
      usb_in_size[i] = reg2hw.configin[i].size.q;
    end
  end

  always_comb begin : proc_map_rdy_reg2hw
    for (int i = 0; i < NEndpoints; i++) begin
      in_rdy_async[i] = reg2hw.configin[i].rdy.q;
    end
  end

  prim_flop_2sync #(
    .Width (NEndpoints)
  ) usbdev_rdysync (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d      (in_rdy_async),
    .q      (usb_in_rdy)
  );

  // CDC: We synchronize the qe (write pulse) and assume that the
  // rest of the register remains stable
  prim_pulse_sync usbdev_data_toggle_clear (
    .clk_src_i   (clk_i),
    .clk_dst_i   (clk_usb_48mhz_i),
    .rst_src_ni  (rst_ni),
    .rst_dst_ni  (rst_usb_48mhz_ni),
    .src_pulse_i (reg2hw.data_toggle_clear[0].qe),
    .dst_pulse_o (usb_data_toggle_clear_en)
  );

  always_comb begin : proc_usb_data_toggle_clear
    usb_data_toggle_clear = '0;
    for (int i = 0; i < NEndpoints; i++) begin
      if (usb_data_toggle_clear_en) begin
        usb_data_toggle_clear[i] = reg2hw.data_toggle_clear[i].q;
      end
    end
  end

  // Clear of ready and set of sent is a pulse in USB clock domain
  // but needs to ensure register bit is cleared/set in TLUL domain
  // usbdev_pulsesync takes pulse in clk_src to pulse in clk_dst
  prim_pulse_sync usbdev_setsent (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_set_sent),
    .dst_pulse_o (set_sent)
  );

  always_comb begin
    set_sentbit = '0;
    if (set_sent) begin
      // synchronization of set_sent ensures usb_endpoint is stable
      set_sentbit[usb_in_endpoint] = 1'b1;
    end
  end

  always_comb begin : proc_map_sent
    for (int i = 0; i < NEndpoints; i++) begin
      hw2reg.in_sent[i].de = set_sentbit[i];
      hw2reg.in_sent[i].d  = 1'b1;
    end
  end

  // Event (pulse) synchronization
  prim_pulse_sync usbdev_sync_in_err (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_in_err),
    .dst_pulse_o (event_in_err)
  );

  prim_pulse_sync usbdev_outrdyclr (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_setup_received),
    .dst_pulse_o (setup_received)
  );

  prim_pulse_sync sync_usb_event_rx_crc_err (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_rx_crc_err),
    .dst_pulse_o (event_rx_crc_err)
  );

  prim_pulse_sync sync_usb_event_rx_pid_err (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_rx_pid_err),
    .dst_pulse_o (event_rx_pid_err)
  );

  prim_pulse_sync sync_usb_event_rx_bitstuff_err (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_rx_bitstuff_err),
    .dst_pulse_o (event_rx_bitstuff_err)
  );

  prim_pulse_sync sync_usb_event_frame (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_frame),
    .dst_pulse_o (event_frame)
  );

  logic event_link_reset_q;

  always_ff @(posedge clk_usb_48mhz_i or negedge rst_usb_48mhz_ni) begin
    if (!rst_usb_48mhz_ni) begin
      event_link_reset_q <= 0;
    end else begin
      event_link_reset_q <= event_link_reset;
    end
  end

  always_comb begin
    clear_rdybit = '0;
    update_pend  = '0;
    if (event_link_reset && !event_link_reset_q) begin
      clear_rdybit = {NEndpoints{1'b1}};
      update_pend  = {NEndpoints{1'b1}};
    end else begin
      // Clear pending when a SETUP is received
      // CDC: usb_out_endpoint is synchronized implicitly by
      // setup_received, as it is stable
      clear_rdybit[usb_out_endpoint] = setup_received;
      update_pend[usb_out_endpoint]  = setup_received;

      // Clear when a IN transmission was sucessful
      // CDC: usb_in_endpoint is synchronzied implicitly by
      // set_sent
      clear_rdybit[usb_in_endpoint] = set_sent;
    end
  end

  always_comb begin : proc_map_rdy_hw2reg
    for (int i = 0; i < NEndpoints; i++) begin
      hw2reg.configin[i].rdy.de = clear_rdybit[i];
      hw2reg.configin[i].rdy.d  = 1'b0;
    end
  end

  // Update the pending bit by copying the ready bit that is about to clear
  always_comb begin : proc_map_pend
    for (int i = 0; i < NEndpoints; i++) begin
      hw2reg.configin[i].pend.de = update_pend[i];
      hw2reg.configin[i].pend.d  = reg2hw.configin[i].rdy.q | reg2hw.configin[i].pend.q;
    end
  end

  ////////////////////////////////////////////////////////
  // USB interface -- everything is in USB clock domain //
  ////////////////////////////////////////////////////////

  usbdev_usbif #(
    .NEndpoints     (NEndpoints),
    .AVFifoWidth    (AVFifoWidth),
    .RXFifoWidth    (RXFifoWidth),
    .MaxPktSizeByte (MaxPktSizeByte),
    .NBuf           (NBuf),
    .SramAw         (SramAw)
  ) usbdev_impl (
    .clk_48mhz_i          (clk_usb_48mhz_i),
    .rst_ni               (rst_usb_48mhz_ni),

    // Pins
    .usb_d_i              (usb_rx_d),
    .usb_se0_i            (usb_rx_se0),
    .usb_oe_o             (usb_tx_oe),
    .usb_d_o              (usb_tx_d),
    .usb_se0_o            (usb_tx_se0),
    .usb_sense_i          (usb_pwr_sense),
    .usb_pullup_en_o      (usb_pullup_en),

    // receive side
    .rx_setup_i           (usb_enable_setup),
    .rx_out_i             (usb_enable_out),
    .rx_stall_i           (usb_ep_stall),
    .av_rvalid_i          (usb_av_rvalid),
    .av_rready_o          (usb_av_rready),
    .av_rdata_i           (usb_av_rdata),
    .event_av_empty_o     (usb_event_av_empty),

    .rx_wvalid_o          (usb_rx_wvalid),
    .rx_wready_i          (usb_rx_wready),
    .rx_wdata_o           (usb_rx_wdata),
    .event_rx_full_o      (usb_event_rx_full),
    .setup_received_o     (usb_setup_received),
    .out_endpoint_o       (usb_out_endpoint),  // will be stable for several cycles

    // transmit side
    .in_buf_i             (usb_in_buf[usb_in_endpoint]),
    .in_size_i            (usb_in_size[usb_in_endpoint]),
    .in_stall_i           (usb_ep_stall),
    .in_rdy_i             (usb_in_rdy),
    .set_sent_o           (usb_set_sent),
    .in_endpoint_o        (usb_in_endpoint),

    // memory
    .mem_req_o            (usb_mem_b_req),
    .mem_write_o          (usb_mem_b_write),
    .mem_addr_o           (usb_mem_b_addr),
    .mem_wdata_o          (usb_mem_b_wdata),
    .mem_rdata_i          (usb_mem_b_rdata),

    // control
    .enable_i             (usb_enable),
    .devaddr_i            (usb_device_addr),
    .clr_devaddr_o        (usb_clr_devaddr),
    .ep_iso_i             (ep_iso), // cdc ok, quasi-static
    .cfg_eop_single_bit_i (reg2hw.phy_config.eop_single_bit.q), // cdc ok: quasi-static
    .tx_osc_test_mode_i   (1'b0), // cdc ok: quasi-static & testmode only
    .data_toggle_clear_i  (usb_data_toggle_clear),

    // status
    .frame_o              (usb_frame),
    .frame_start_o        (usb_event_frame),
    .link_state_o         (usb_link_state),
    .link_disconnect_o    (usb_event_disconnect),
    .link_connect_o       (usb_event_connect),
    .link_reset_o         (usb_event_link_reset),
    .link_suspend_o       (usb_event_link_suspend),
    .link_resume_o        (usb_event_link_resume),
    .host_lost_o          (usb_event_host_lost),
    .link_in_err_o        (usb_event_in_err),
    .rx_crc_err_o         (usb_event_rx_crc_err),
    .rx_pid_err_o         (usb_event_rx_pid_err),
    .rx_bitstuff_err_o    (usb_event_rx_bitstuff_err)
  );

  /////////////////////////////////
  // Control signal / status CDC //
  /////////////////////////////////

  // USB clk -> sys clk
  prim_flop_2sync #(
    .Width      (3+11)
  ) cdc_usb_to_sys (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d      ({usb_link_state,              usb_frame}),
    .q      ({hw2reg.usbstat.link_state.d, hw2reg.usbstat.frame.d})
  );

  // sys clk -> USB clk
  prim_flop_2sync #(
    .Width      (1+7)
  ) cdc_sys_to_usb (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d      ({reg2hw.usbctrl.enable.q, reg2hw.usbctrl.device_address.q}),
    .q      ({usb_enable,              usb_device_addr})
  );

  // CDC for event signals (arguably they are there for a long time so would be ok)
  // Just want a pulse to ensure only one interrupt for an event
  usbdev_flop_2syncpulse #(.Width(5)) syncevent (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d      ({usb_event_disconnect, usb_event_link_reset, usb_event_link_suspend,
              usb_event_host_lost, usb_event_connect}),
    .q      ({event_disconnect, event_link_reset, event_link_suspend,
              event_host_lost, event_connect})
  );

  // Resume is a single pulse so needs pulsesync
  prim_pulse_sync usbdev_resume (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_link_resume),
    .dst_pulse_o (event_link_resume)
  );

  assign hw2reg.usbstat.host_lost.d = event_host_lost;

  // resets etc cause the device address to clear
  prim_pulse_sync usbdev_devclr (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_clr_devaddr),
    .dst_pulse_o (hw2reg.usbctrl.device_address.de)
  );
  assign hw2reg.usbctrl.device_address.d = '0;

  // AV empty is a single pulse so needs pulsesync
  prim_pulse_sync sync_usb_event_av_empty (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_av_empty),
    .dst_pulse_o (event_av_empty)
  );

  // RX full is a single pulse so needs pulsesync
  prim_pulse_sync sync_usb_event_rx_full (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_rx_full),
    .dst_pulse_o (event_rx_full)
  );

  // Clear the stall flag when a SETUP is received

  // CDC: usb_out_endpoint is synchronized implicitly by
  // setup_received, as it is stable
  always_comb begin : proc_stall_tieoff
    for (int i = 0; i < NEndpoints; i++) begin
      hw2reg.stall[i].d  = 1'b0;
      if (setup_received && usb_out_endpoint == 4'(i)) begin
        hw2reg.stall[i].de = 1'b1;
      end else begin
        hw2reg.stall[i].de = 1'b0;
      end
    end
  end

  logic        unused_mem_a_rerror_d;

  // TL-UL to SRAM adapter
  tlul_adapter_sram #(
    .SramAw(SramAw),
    .ByteAccess(0)
  ) u_tlul2sram (
    .clk_i    (clk_i),
    .rst_ni   (rst_ni),

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

    .EnableECC           (0), // No Protection
    .EnableParity        (0),
    .EnableInputPipeline (0),
    .EnableOutputPipeline(0),

    // large memory, implement with SRAMs
    .MemT ("SRAM")
  ) u_memory_2p (
    .clk_a_i    (clk_i),
    .clk_b_i    (clk_usb_48mhz_i),
    .rst_a_ni   (rst_ni),
    .rst_b_ni   (rst_usb_48mhz_ni),
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

    .cfg_i      (8'h0)
  );

  // Register module
  usbdev_reg_top u_reg (
    .clk_i,
    .rst_ni,

    .tl_i (tl_i),
    .tl_o (tl_o),

    .tl_win_o (tl_sram_h2d),
    .tl_win_i (tl_sram_d2h),

    .reg2hw,
    .hw2reg,
    .devmode_i (1'b1)
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

  prim_intr_hw #(.Width(1)) intr_connected (
    .event_intr_i           (event_connect),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.connected.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.connected.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.connected.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.connected.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.connected.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.connected.d),
    .intr_o                 (intr_connected_o)
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

  prim_intr_hw #(.Width(1)) intr_link_in_err (
    .event_intr_i           (event_in_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_in_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_in_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_in_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_in_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_in_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_in_err.d),
    .intr_o                 (intr_link_in_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_rx_crc_err (
    .event_intr_i           (event_rx_crc_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_crc_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_crc_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_crc_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_crc_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_crc_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_crc_err.d),
    .intr_o                 (intr_rx_crc_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_rx_pid_err (
    .event_intr_i           (event_rx_pid_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_pid_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_pid_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_pid_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_pid_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_pid_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_pid_err.d),
    .intr_o                 (intr_rx_pid_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_rx_bitstuff_err (
    .event_intr_i           (event_rx_bitstuff_err),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_bitstuff_err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_bitstuff_err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_bitstuff_err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_bitstuff_err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_bitstuff_err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_bitstuff_err.d),
    .intr_o                 (intr_rx_bitstuff_err_o)
  );

  prim_intr_hw #(.Width(1)) intr_frame (
    .event_intr_i           (event_frame),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.frame.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.frame.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.frame.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.frame.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.frame.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.frame.d),
    .intr_o                 (intr_frame_o)
  );

  /////////////////////////////////
  // USB IO Muxing               //
  /////////////////////////////////

  usbdev_iomux i_usbdev_iomux (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .clk_usb_48mhz_i        (clk_usb_48mhz_i),
    .rst_usb_48mhz_ni             (rst_usb_48mhz_ni),
    .rx_differential_mode_i (reg2hw.phy_config.rx_differential_mode),
    .tx_differential_mode_i (reg2hw.phy_config.tx_differential_mode),
    .sys_reg2hw_config_i    (reg2hw.phy_config),
    .sys_usb_sense_o        (hw2reg.usbstat.usb_sense.d),

    // Chip IO
    .cio_usb_d_i            (cio_d_i),
    .cio_usb_dp_i           (cio_dp_i),
    .cio_usb_dn_i           (cio_dn_i),
    .cio_usb_d_o            (cio_d_o),
    .cio_usb_se0_o          (cio_se0_o),
    .cio_usb_dp_o           (cio_dp_o),
    .cio_usb_dn_o           (cio_dn_o),
    .cio_usb_oe_o           (cio_oe_o),
    .cio_usb_tx_mode_se_o   (cio_tx_mode_se_o),
    .cio_usb_sense_i        (cio_sense_i),
    .cio_usb_pullup_en_o    (cio_pullup_en_o),
    .cio_usb_suspend_o      (cio_suspend_o),

    // Internal interface
    .usb_rx_d_o             (usb_rx_d),
    .usb_rx_se0_o           (usb_rx_se0),
    .usb_tx_d_i             (usb_tx_d),
    .usb_tx_se0_i           (usb_tx_se0),
    .usb_tx_oe_i            (usb_tx_oe),
    .usb_pwr_sense_o        (usb_pwr_sense),
    .usb_pullup_en_i        (usb_pullup_en),
    .usb_suspend_i          (usb_event_link_suspend)
  );

endmodule
