// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB Full-Speed Device Interface (usbdev).
//
//

`include "prim_assert.sv"

module usbdev
  import usbdev_pkg::*;
  import usbdev_reg_pkg::*;
  import prim_util_pkg::vbits;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // Max time (in microseconds) from rx_enable_o high to the
  // external differential receiver outputting valid data (when
  // configured to use one).
  parameter int unsigned RcvrWakeTimeUs = 1
) (
  input  logic       clk_i,
  input  logic       rst_ni,
  input  logic       clk_aon_i,
  input  logic       rst_aon_ni,
  input  logic       clk_usb_48mhz_i, // use usb_ prefix for signals in this clk
  input  logic       rst_usb_48mhz_ni, // async reset, with relase sync to clk_usb_48_mhz_i

  // Register interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Data inputs
  input  logic       cio_usb_dp_i, // differential P, can be used in single-ended mode to detect SE0
  input  logic       cio_usb_dn_i, // differential N, can be used in single-ended mode to detect SE0
  input  logic       usb_rx_d_i, // single-ended input from the differential receiver

  // Data outputs
  output logic       cio_usb_dp_o,
  output logic       cio_usb_dp_en_o,
  output logic       cio_usb_dn_o,
  output logic       cio_usb_dn_en_o,
  output logic       usb_tx_se0_o, // single-ended zero output
  output logic       usb_tx_d_o,

  // Non-data I/O
  input  logic       cio_sense_i,
  output logic       usb_dp_pullup_o,
  output logic       usb_dn_pullup_o,
  output logic       usb_rx_enable_o,
  output logic       usb_tx_use_d_se0_o,

  // Direct pinmux aon detect connections
  output logic       usb_aon_suspend_req_o,
  output logic       usb_aon_wake_ack_o,

  // Events and state from wakeup module
  input  logic       usb_aon_bus_reset_i,
  input  logic       usb_aon_sense_lost_i,
  input  logic       usb_aon_wake_detect_active_i,

  // SOF reference for clock calibration
  output logic       usb_ref_val_o,
  output logic       usb_ref_pulse_o,

  // memory configuration
  input prim_ram_2p_pkg::ram_2p_cfg_t ram_cfg_i,

  // Interrupts
  output logic       intr_pkt_received_o, // Packet received
  output logic       intr_pkt_sent_o, // Packet sent
  output logic       intr_powered_o,
  output logic       intr_disconnected_o,
  output logic       intr_host_lost_o,
  output logic       intr_link_reset_o,
  output logic       intr_link_suspend_o,
  output logic       intr_link_resume_o,
  output logic       intr_av_empty_o,
  output logic       intr_rx_full_o,
  output logic       intr_av_overflow_o,
  output logic       intr_link_in_err_o,
  output logic       intr_link_out_err_o,
  output logic       intr_rx_crc_err_o,
  output logic       intr_rx_pid_err_o,
  output logic       intr_rx_bitstuff_err_o,
  output logic       intr_frame_o
);

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

  tlul_pkg::tl_h2d_t tl_sram_h2d;
  tlul_pkg::tl_d2h_t tl_sram_d2h;

  // Dual-port SRAM Interface: Refer prim_ram_2p_async_adv.sv
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
  logic              usb_event_host_lost, usb_event_disconnect, usb_event_powered;
  logic              usb_event_rx_crc_err, usb_event_rx_pid_err;
  logic              usb_event_rx_bitstuff_err;
  logic              usb_event_in_err;
  logic              usb_event_out_err;
  logic              usb_event_frame, usb_event_sof;
  logic              usb_link_active;

  logic              event_link_reset, event_link_suspend, event_link_resume;
  logic              event_host_lost, event_disconnect, event_powered;
  logic              event_rx_crc_err, event_rx_pid_err;
  logic              event_rx_bitstuff_err;
  logic              event_in_err;
  logic              event_out_err;
  logic              event_frame;

  // CDC signals
  logic [10:0]       usb_frame;
  logic [2:0]        usb_link_state;
  logic              usb_enable;
  logic [6:0]        usb_device_addr;
  logic              usb_resume_link_active;

  logic                  data_toggle_clear_qe;
  logic                  usb_data_toggle_clear_en;
  logic [NEndpoints-1:0] usb_data_toggle_clear;


  /////////////////////////////////
  // USB RX after CDC & muxing   //
  /////////////////////////////////
  logic usb_rx_d;
  logic usb_rx_dp;
  logic usb_rx_dn;
  /////////////////////////////////
  // USB TX after CDC & muxing   //
  /////////////////////////////////
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_tx_dp;
  logic usb_tx_dn;
  logic usb_tx_oe;
  /////////////////////////////////
  // USB contol pins after CDC   //
  /////////////////////////////////
  logic usb_pwr_sense;
  logic usb_pullup_en;
  logic usb_dp_pullup_en;
  logic usb_dn_pullup_en;

  //////////////////////////////////
  // Microsecond timing reference //
  //////////////////////////////////
  // us_tick ticks for one cycle every us, and it is based off a free-running
  // counter.
  logic [5:0]   ns_cnt;
  logic         us_tick;

  assign us_tick = (ns_cnt == 6'd48);
  always_ff @(posedge clk_usb_48mhz_i or negedge rst_usb_48mhz_ni) begin
    if (!rst_usb_48mhz_ni) begin
      ns_cnt <= '0;
    end else begin
      if (us_tick) begin
        ns_cnt <= '0;
      end else begin
        ns_cnt <= ns_cnt + 1'b1;
      end
    end
  end

  /////////////////////////////
  // Receive interface fifos //
  /////////////////////////////

  logic              av_fifo_wready;
  logic              event_pkt_received;
  logic              usb_av_rvalid, usb_av_rready;
  logic              usb_rx_wvalid, usb_rx_wready;
  logic              rx_fifo_rvalid;
  logic              rx_fifo_re;

  logic [AVFifoWidth - 1:0] usb_av_rdata;
  logic [RXFifoWidth - 1:0] usb_rx_wdata, rx_rdata_raw, rx_rdata;

  logic [NEndpoints-1:0] clear_rxenable_out;

  assign event_av_overflow = reg2hw.avbuffer.qe & (~av_fifo_wready);
  assign hw2reg.usbstat.av_full.d = ~av_fifo_wready;
  assign hw2reg.usbstat.rx_empty.d = ~rx_fifo_rvalid;

  prim_fifo_async #(
    .Width(AVFifoWidth),
    .Depth(AVFifoDepth)
  ) usbdev_avfifo (
    .clk_wr_i  (clk_i),
    .rst_wr_ni (rst_ni),

    .wvalid_i  (reg2hw.avbuffer.qe),
    .wready_o  (av_fifo_wready),
    .wdata_i   (reg2hw.avbuffer.q),
    .wdepth_o  (hw2reg.usbstat.av_depth.d),

    .clk_rd_i  (clk_usb_48mhz_i),
    .rst_rd_ni (rst_usb_48mhz_ni),
    .rvalid_o  (usb_av_rvalid),
    .rready_i  (usb_av_rready),
    .rdata_o   (usb_av_rdata),
    .rdepth_o  () // only using empty
  );

  assign rx_fifo_re = reg2hw.rxfifo.ep.re | reg2hw.rxfifo.setup.re |
                      reg2hw.rxfifo.size.re | reg2hw.rxfifo.buffer.re;

  prim_fifo_async #(
    .Width(RXFifoWidth),
    .Depth(RXFifoDepth)
  ) usbdev_rxfifo (
    .clk_wr_i  (clk_usb_48mhz_i),
    .rst_wr_ni (rst_usb_48mhz_ni),

    .wvalid_i  (usb_rx_wvalid),
    .wready_o  (usb_rx_wready),
    .wdata_i   (usb_rx_wdata),
    .wdepth_o  (),

    .clk_rd_i  (clk_i),
    .rst_rd_ni (rst_ni),
    .rvalid_o  (rx_fifo_rvalid),
    .rready_i  (rx_fifo_re),
    .rdata_o   (rx_rdata_raw),
    .rdepth_o  (hw2reg.usbstat.rx_depth.d)
  );

  // Return all zero if the FIFO is empty (instead of X)
  assign rx_rdata = rx_fifo_rvalid ? rx_rdata_raw : '0;
  assign hw2reg.rxfifo.ep.d = rx_rdata[16:13];
  assign hw2reg.rxfifo.setup.d = rx_rdata[12];
  assign hw2reg.rxfifo.size.d = rx_rdata[11:5];
  assign hw2reg.rxfifo.buffer.d = rx_rdata[4:0];
  assign event_pkt_received = rx_fifo_rvalid;

  // The rxfifo register is hrw, but we just need the read enables.
  logic [16:0] unused_rxfifo_q;
  assign unused_rxfifo_q = {reg2hw.rxfifo.ep.q, reg2hw.rxfifo.setup.q,
                            reg2hw.rxfifo.size.q, reg2hw.rxfifo.buffer.q};

  ////////////////////////////////////
  // IN (Transmit) interface config //
  ////////////////////////////////////
  logic [NBufWidth-1:0]  usb_in_buf [NEndpoints];
  logic [SizeWidth:0]    usb_in_size [NEndpoints];
  logic [3:0]            usb_in_endpoint;
  logic                  usb_in_endpoint_val;
  logic [NEndpoints-1:0] usb_in_rdy;
  logic [NEndpoints-1:0] clear_rdybit, set_sentbit, update_pend;
  logic                  usb_setup_received, setup_received, usb_set_sent, set_sent;
  logic [NEndpoints-1:0] ep_out_iso, ep_in_iso;
  logic [NEndpoints-1:0] enable_setup, in_ep_stall, out_ep_stall;
  logic [NEndpoints-1:0] usb_enable_setup, usb_enable_out, ep_set_nak_on_out;
  logic [NEndpoints-1:0] usb_in_ep_stall, usb_out_ep_stall;
  logic [NEndpoints-1:0] ep_in_enable, ep_out_enable, usb_ep_in_enable, usb_ep_out_enable;
  logic [NEndpoints-1:0] in_rdy_async;
  logic [3:0]            usb_out_endpoint;
  logic                  usb_out_endpoint_val;
  logic                  usb_use_diff_rcvr, usb_diff_rx_ok;

  // Endpoint enables
  always_comb begin : proc_map_ep_enable
    for (int i = 0; i < NEndpoints; i++) begin
      ep_in_enable[i] = reg2hw.ep_in_enable[i].q;
      ep_out_enable[i] = reg2hw.ep_out_enable[i].q;
    end
  end

  // RX enables
  always_comb begin : proc_map_rxenable
    for (int i = 0; i < NEndpoints; i++) begin
      enable_setup[i]   = reg2hw.rxenable_setup[i].q;
      usb_enable_out[i] = reg2hw.rxenable_out[i].q;
    end
  end

  // STALL for both directions
  always_comb begin : proc_map_stall
    for (int i = 0; i < NEndpoints; i++) begin
      in_ep_stall[i] = reg2hw.in_stall[i];
      out_ep_stall[i] = reg2hw.out_stall[i];
    end
  end

  prim_flop_2sync #(
    .Width(3*NEndpoints)
  ) usbdev_sync_ep_cfg (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d_i    ({enable_setup, in_ep_stall, out_ep_stall}),
    .q_o    ({usb_enable_setup, usb_in_ep_stall, usb_out_ep_stall})
  );

  prim_flop_2sync #(
    .Width(2*NEndpoints)
  ) usbdev_sync_ep_enable (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d_i    ({ep_in_enable, ep_out_enable}),
    .q_o    ({usb_ep_in_enable, usb_ep_out_enable})
  );

  // CDC: ok, quasi-static
  always_comb begin : proc_map_iso
    for (int i = 0; i < NEndpoints; i++) begin
      ep_out_iso[i] = reg2hw.out_iso[i].q;
      ep_in_iso[i] = reg2hw.in_iso[i].q;
      ep_set_nak_on_out[i] = reg2hw.set_nak_out[i].q;
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
    .d_i    (in_rdy_async),
    .q_o    (usb_in_rdy)
  );

  // CDC: We synchronize the qe (write pulse) and assume that the
  // rest of the register remains stable
  always_comb begin : proc_data_toggle_clear_qe
    data_toggle_clear_qe = 1'b0;
    for (int i = 0; i < NEndpoints; i++) begin
      data_toggle_clear_qe |= reg2hw.data_toggle_clear[i].qe;
    end
  end

  prim_pulse_sync usbdev_data_toggle_clear (
    .clk_src_i   (clk_i),
    .clk_dst_i   (clk_usb_48mhz_i),
    .rst_src_ni  (rst_ni),
    .rst_dst_ni  (rst_usb_48mhz_ni),
    .src_pulse_i (data_toggle_clear_qe),
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
    if (set_sent && usb_in_endpoint_val) begin
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

  // Clear of rxenable_out bit
  // If so configured, for every received transaction on a given endpoint, clear
  // the rxenable_out bit. In this configuration, hardware defaults to NAKing
  // any subsequent transaction, so software has time to decide the next
  // response.
  always_comb begin
    clear_rxenable_out = '0;
    if (usb_rx_wvalid && usb_out_endpoint_val) begin
      clear_rxenable_out[usb_out_endpoint] = ep_set_nak_on_out[usb_out_endpoint];
    end
  end

  always_comb begin
    for (int i = 0; i < NEndpoints; i++) begin
      hw2reg.rxenable_out[i].d = 1'b0;
      hw2reg.rxenable_out[i].de = clear_rxenable_out[i];
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

  prim_pulse_sync usbdev_sync_out_err (
    .clk_src_i   (clk_usb_48mhz_i),
    .clk_dst_i   (clk_i),
    .rst_src_ni  (rst_usb_48mhz_ni),
    .rst_dst_ni  (rst_ni),
    .src_pulse_i (usb_event_out_err),
    .dst_pulse_o (event_out_err)
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
      if (usb_out_endpoint_val) begin
        // Clear pending when a SETUP is received
        // CDC: usb_out_endpoint is synchronized implicitly by
        // setup_received, as it is stable
        clear_rdybit[usb_out_endpoint] = setup_received;
        update_pend[usb_out_endpoint]  = setup_received;
      end

      if (usb_in_endpoint_val) begin
        // Clear when a IN transmission was sucessful
        // CDC: usb_in_endpoint is synchronzied implicitly by
        // set_sent
        clear_rdybit[usb_in_endpoint] = set_sent;
      end
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
  wire cfg_pinflip = reg2hw.phy_config.pinflip.q; // cdc ok: quasi-static
  assign usb_dp_pullup_en = cfg_pinflip ? 1'b0 : usb_pullup_en;
  assign usb_dn_pullup_en = !cfg_pinflip ? 1'b0 : usb_pullup_en;


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
    .usb_dp_i             (usb_rx_dp),
    .usb_dn_i             (usb_rx_dn),
    .usb_oe_o             (usb_tx_oe),
    .usb_d_o              (usb_tx_d),
    .usb_se0_o            (usb_tx_se0),
    .usb_dp_o             (usb_tx_dp),
    .usb_dn_o             (usb_tx_dn),
    .usb_sense_i          (usb_pwr_sense),
    .usb_pullup_en_o      (usb_pullup_en),

    // receive side
    .rx_setup_i           (usb_enable_setup),
    .rx_out_i             (usb_enable_out),
    .rx_stall_i           (usb_out_ep_stall),
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
    .out_endpoint_val_o   (usb_out_endpoint_val),

    // transmit side
    .in_buf_i             (usb_in_buf[usb_in_endpoint]),
    .in_size_i            (usb_in_size[usb_in_endpoint]),
    .in_stall_i           (usb_in_ep_stall),
    .in_rdy_i             (usb_in_rdy),
    .set_sent_o           (usb_set_sent),
    .in_endpoint_o        (usb_in_endpoint),
    .in_endpoint_val_o    (usb_in_endpoint_val),

    // memory
    .mem_req_o            (usb_mem_b_req),
    .mem_write_o          (usb_mem_b_write),
    .mem_addr_o           (usb_mem_b_addr),
    .mem_wdata_o          (usb_mem_b_wdata),
    .mem_rdata_i          (usb_mem_b_rdata),

    // time reference
    .us_tick_i            (us_tick),

    // control
    .enable_i             (usb_enable),
    .devaddr_i            (usb_device_addr),
    .clr_devaddr_o        (usb_clr_devaddr),
    .in_ep_enabled_i      (usb_ep_in_enable),
    .out_ep_enabled_i     (usb_ep_out_enable),
    .out_ep_iso_i         (ep_out_iso), // cdc ok, quasi-static
    .in_ep_iso_i          (ep_in_iso), // cdc ok, quasi-static
    .diff_rx_ok_i         (usb_diff_rx_ok),
    .cfg_eop_single_bit_i (reg2hw.phy_config.eop_single_bit.q), // cdc ok: quasi-static
    .tx_osc_test_mode_i   (reg2hw.phy_config.tx_osc_test_mode.q), // cdc ok: quasi-static
    .cfg_use_diff_rcvr_i  (usb_rx_enable_o),
    .cfg_pinflip_i        (cfg_pinflip),
    .data_toggle_clear_i  (usb_data_toggle_clear),
    .resume_link_active_i (usb_resume_link_active),

    // status
    .frame_o              (usb_frame),
    .frame_start_o        (usb_event_frame),
    .sof_valid_o          (usb_event_sof),
    .link_state_o         (usb_link_state),
    .link_disconnect_o    (usb_event_disconnect),
    .link_powered_o       (usb_event_powered),
    .link_reset_o         (usb_event_link_reset),
    .link_active_o        (usb_link_active),
    .link_suspend_o       (usb_event_link_suspend),
    .link_resume_o        (usb_event_link_resume),
    .host_lost_o          (usb_event_host_lost),
    .link_in_err_o        (usb_event_in_err),
    .link_out_err_o       (usb_event_out_err),
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
    .d_i    ({usb_link_state,              usb_frame}),
    .q_o    ({hw2reg.usbstat.link_state.d, hw2reg.usbstat.frame.d})
  );

  assign usb_enable = reg2hw.usbctrl.enable.q;
  assign usb_device_addr = reg2hw.usbctrl.device_address.q;
  assign usb_resume_link_active = reg2hw.usbctrl.resume_link_active.qe &
                                  reg2hw.usbctrl.resume_link_active.q;

  // CDC for event signals (arguably they are there for a long time so would be ok)
  // Just want a pulse to ensure only one interrupt for an event
  usbdev_flop_2syncpulse #(.Width(5)) syncevent (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .d_i    ({usb_event_disconnect, usb_event_link_reset, usb_event_link_suspend,
              usb_event_host_lost, usb_event_powered}),
    .q_o    ({event_disconnect, event_link_reset, event_link_suspend,
              event_host_lost, event_powered})
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
  assign hw2reg.usbctrl.device_address.de = usb_clr_devaddr;
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
      hw2reg.in_stall[i].d  = 1'b0;
      hw2reg.out_stall[i].d  = 1'b0;
      if (setup_received && usb_out_endpoint_val && usb_out_endpoint == 4'(unsigned'(i))) begin
        hw2reg.out_stall[i].de = 1'b1;
        hw2reg.in_stall[i].de = 1'b1;
      end else begin
        hw2reg.out_stall[i].de = 1'b0;
        hw2reg.in_stall[i].de = 1'b0;
      end
    end
  end

  // TL-UL to SRAM adapter
  tlul_adapter_sram #(
    .SramAw(SramAw),
    .ByteAccess(0)
  ) u_tlul2sram (
    .clk_i       (clk_i),
    .rst_ni      (rst_ni),

    .tl_i        (tl_sram_h2d),
    .tl_o        (tl_sram_d2h),
    .en_ifetch_i (prim_mubi_pkg::MuBi4False),
    .req_o       (mem_a_req),
    .req_type_o  (),
    .gnt_i       (mem_a_req),  //Always grant when request
    .we_o        (mem_a_write),
    .addr_o      (mem_a_addr),
    .wdata_o     (mem_a_wdata),
    .wmask_o     (),           // Not used
    .intg_error_o(),
    .rdata_i     (mem_a_rdata),
    .rvalid_i    (mem_a_rvalid),
    .rerror_i    (mem_a_rerror)
  );

  // SRAM Wrapper
  prim_ram_2p_async_adv #(
    .Depth (SramDepth),
    .Width (SramDw),    // 32 x 512 --> 2kB
    .DataBitsPerMask(8),

    .EnableECC           (0), // No Protection
    .EnableParity        (0),
    .EnableInputPipeline (0),
    .EnableOutputPipeline(0)
  ) u_memory_2p (
    .clk_a_i    (clk_i),
    .clk_b_i    (clk_usb_48mhz_i),
    .rst_a_ni   (rst_ni),
    .rst_b_ni   (rst_usb_48mhz_ni),
    .a_req_i    (mem_a_req),
    .a_write_i  (mem_a_write),
    .a_addr_i   (mem_a_addr),
    .a_wdata_i  (mem_a_wdata),
    .a_wmask_i  ({SramDw{1'b1}}),
    .a_rvalid_o (mem_a_rvalid),
    .a_rdata_o  (mem_a_rdata),
    .a_rerror_o (mem_a_rerror),

    .b_req_i    (usb_mem_b_req),
    .b_write_i  (usb_mem_b_write),
    .b_addr_i   (usb_mem_b_addr),
    .b_wdata_i  (usb_mem_b_wdata),
    .b_wmask_i  ({SramDw{1'b1}}),
    .b_rvalid_o (),
    .b_rdata_o  (usb_mem_b_rdata),
    .b_rerror_o (),
    .cfg_i      (ram_cfg_i)
  );

  logic [NumAlerts-1:0] alert_test, alerts;

  // Register module
  usbdev_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .clk_aon_i,
    .rst_aon_ni,
    .clk_usb_48mhz_i,
    .rst_usb_48mhz_ni,

    .tl_i (tl_i),
    .tl_o (tl_o),

    .tl_win_o (tl_sram_h2d),
    .tl_win_i (tl_sram_d2h),

    .reg2hw,
    .hw2reg,

    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (alerts[0]),
    .devmode_i (1'b1)
  );

  // Alerts
  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(i)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // Interrupts
  prim_intr_hw #(.Width(1)) intr_hw_pkt_received (
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_disconnect),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.disconnected.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.disconnected.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.disconnected.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.disconnected.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.disconnected.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.disconnected.d),
    .intr_o                 (intr_disconnected_o)
  );

  prim_intr_hw #(.Width(1)) intr_powered (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_powered),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.powered.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.powered.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.powered.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.powered.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.powered.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.powered.d),
    .intr_o                 (intr_powered_o)
  );

  prim_intr_hw #(.Width(1)) intr_host_lost (
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_in_err),
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
    .event_intr_i           (event_out_err),
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
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
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
    .clk_i,
    .rst_ni,
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
  logic cio_usb_oe;
  logic usb_rx_enable;
  assign cio_usb_dp_en_o = cio_usb_oe;
  assign cio_usb_dn_en_o = cio_usb_oe;
  assign usb_tx_use_d_se0_o = reg2hw.phy_config.tx_use_d_se0.q; // cdc ok: quasi-static

  usbdev_iomux i_usbdev_iomux (
    .clk_i                  (clk_i),
    .rst_ni                 (rst_ni),
    .clk_usb_48mhz_i        (clk_usb_48mhz_i),
    .rst_usb_48mhz_ni       (rst_usb_48mhz_ni),

    // Register interface
    .sys_hw2reg_sense_o     (hw2reg.phy_pins_sense),
    .sys_reg2hw_drive_i     (reg2hw.phy_pins_drive),
    .sys_usb_sense_o        (hw2reg.usbstat.sense.d),

    // Chip IO
    .usb_rx_d_i             (usb_rx_d_i),
    .usb_rx_dp_i            (cio_usb_dp_i),
    .usb_rx_dn_i            (cio_usb_dn_i),
    .usb_tx_d_o             (usb_tx_d_o),
    .usb_tx_se0_o           (usb_tx_se0_o),
    .usb_tx_dp_o            (cio_usb_dp_o),
    .usb_tx_dn_o            (cio_usb_dn_o),
    .usb_tx_oe_o            (cio_usb_oe),
    .cio_usb_sense_i        (cio_sense_i),
    .usb_dp_pullup_en_o     (usb_dp_pullup_o),
    .usb_dn_pullup_en_o     (usb_dn_pullup_o),
    .usb_rx_enable_o        (usb_rx_enable_o),

    // Internal interface
    .usb_rx_d_o             (usb_rx_d),
    .usb_rx_dp_o            (usb_rx_dp),
    .usb_rx_dn_o            (usb_rx_dn),
    .usb_tx_d_i             (usb_tx_d),
    .usb_tx_se0_i           (usb_tx_se0),
    .usb_tx_dp_i            (usb_tx_dp),
    .usb_tx_dn_i            (usb_tx_dn),
    .usb_tx_oe_i            (usb_tx_oe),
    .usb_pwr_sense_o        (usb_pwr_sense),
    .usb_dp_pullup_en_i     (usb_dp_pullup_en),
    .usb_dn_pullup_en_i     (usb_dn_pullup_en),
    .usb_rx_enable_i        (usb_rx_enable)
  );

  // Differential receiver enable
  prim_flop_2sync #(
    .Width      (1)
  ) usbdev_sync_rcvr_enable (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d_i    (reg2hw.phy_config.use_diff_rcvr.q),
    .q_o    (usb_use_diff_rcvr)
  );
  // enable rx only when the single-ended input is enabled and the device is
  // not suspended (unless it is forced on in the I/O mux).
  assign usb_rx_enable = usb_use_diff_rcvr & ~usb_event_link_suspend;

  // Symbols from the differential receiver are invalid until it has finished
  // waking up / powering on
  // Add 1 to the specified time to account for uncertainty in the
  // free-running counter for us_tick.
  localparam int RcvrWakeTimeWidth = vbits(RcvrWakeTimeUs + 2);
  logic [RcvrWakeTimeWidth-1:0] usb_rcvr_ok_counter_d, usb_rcvr_ok_counter_q;

  assign usb_diff_rx_ok = (usb_rcvr_ok_counter_q == '0);
  always_comb begin
    // When don't need to use a differential receiver, RX is always ready
    usb_rcvr_ok_counter_d = '0;
    if (usb_use_diff_rcvr & !usb_rx_enable_o) begin
      usb_rcvr_ok_counter_d = RcvrWakeTimeWidth'(RcvrWakeTimeUs + 1);
    end else if (us_tick && (usb_rcvr_ok_counter_q > '0)) begin
      usb_rcvr_ok_counter_d = usb_rcvr_ok_counter_q - 1;
    end
  end

  always_ff @(posedge clk_usb_48mhz_i or negedge rst_usb_48mhz_ni) begin
    if (!rst_usb_48mhz_ni) begin
      usb_rcvr_ok_counter_q <= RcvrWakeTimeWidth'(RcvrWakeTimeUs + 1);
    end else begin
      usb_rcvr_ok_counter_q <= usb_rcvr_ok_counter_d;
    end
  end

  /////////////////////////////////////////
  // SOF Reference for Clock Calibration //
  /////////////////////////////////////////

  logic usb_ref_val_d, usb_ref_val_q;
  logic usb_ref_disable;

  // sys clk -> USB clk
  prim_flop_2sync #(
    .Width      (1)
  ) usbdev_sync_phy_config (
    .clk_i  (clk_usb_48mhz_i),
    .rst_ni (rst_usb_48mhz_ni),
    .d_i    (reg2hw.phy_config.usb_ref_disable.q),
    .q_o    (usb_ref_disable)
  );

  // Directly forward the pulse unless disabled.
  assign usb_ref_pulse_o = usb_ref_disable ? 1'b0 : usb_event_sof;

  // The first pulse is always ignored, but causes the valid to be asserted.
  // The valid signal is deasserted when:
  // - The link is no longer active.
  // - The host is lost (no SOF for 4ms).
  // - The reference generation is disabled.
  assign usb_ref_val_d = usb_ref_pulse_o                           ? 1'b1 :
      (!usb_link_active || usb_event_host_lost || usb_ref_disable) ? 1'b0 : usb_ref_val_q;

  always_ff @(posedge clk_usb_48mhz_i or negedge rst_usb_48mhz_ni) begin
    if (!rst_usb_48mhz_ni) begin
      usb_ref_val_q <= 1'b0;
    end else begin
      usb_ref_val_q <= usb_ref_val_d;
    end
  end

  assign usb_ref_val_o = usb_ref_val_q;

  /////////////////////////////////////////
  // USB aon detector signaling          //
  /////////////////////////////////////////
  assign usb_aon_suspend_req_o = reg2hw.wake_control.suspend_req.qe &
                                 reg2hw.wake_control.suspend_req.q;
  assign usb_aon_wake_ack_o = reg2hw.wake_control.wake_ack.qe &
                              reg2hw.wake_control.wake_ack.q;

  /////////////////////////////////////////
  // capture async event and debug info  //
  /////////////////////////////////////////

  assign hw2reg.wake_events.module_active.de = 1'b1;
  assign hw2reg.wake_events.module_active.d = usb_aon_wake_detect_active_i;
  assign hw2reg.wake_events.disconnected.de = 1'b1;
  assign hw2reg.wake_events.disconnected.d = usb_aon_sense_lost_i;
  assign hw2reg.wake_events.bus_reset.de = 1'b1;
  assign hw2reg.wake_events.bus_reset.d = usb_aon_bus_reset_i;

  /////////////////////////////////
  // Xprop assertions on outputs //
  /////////////////////////////////

  `ASSERT_KNOWN(TlODValidKnown_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown_A, tl_o.a_ready)
  // These pins are not necessarily associated with any clock but it probably makes most sense to
  // check them on the fastest clock.
  `ASSERT_KNOWN(USBTxDKnown_A, usb_tx_d_o)
  `ASSERT_KNOWN(CIODpKnown_A, cio_usb_dp_o)
  `ASSERT_KNOWN(CIODpEnKnown_A, cio_usb_dp_en_o)
  `ASSERT_KNOWN(CIODnKnown_A, cio_usb_dn_o)
  `ASSERT_KNOWN(CIODnEnKnown_A, cio_usb_dn_en_o)
  `ASSERT_KNOWN(USBTxSe0Known_A, usb_tx_se0_o)
  `ASSERT_KNOWN(USBDpPUKnown_A, usb_dp_pullup_o)
  `ASSERT_KNOWN(USBDnPUKnown_A, usb_dn_pullup_o)
  `ASSERT_KNOWN(USBRxEnableKnown_A, usb_rx_enable_o)
  `ASSERT_KNOWN(USBAonSuspendReqKnown_A, usb_aon_suspend_req_o)
  `ASSERT_KNOWN(USBAonWakeAckKnown_A, usb_aon_wake_ack_o)
  `ASSERT_KNOWN(USBRefValKnown_A, usb_ref_val_o, clk_usb_48mhz_i, !rst_usb_48mhz_ni)
  `ASSERT_KNOWN(USBRefPulseKnown_A, usb_ref_pulse_o, clk_usb_48mhz_i, !rst_usb_48mhz_ni)
  // Assert Known for alerts
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)
  //Interrupt signals
  `ASSERT_KNOWN(USBIntrPktRcvdKnown_A, intr_pkt_received_o)
  `ASSERT_KNOWN(USBIntrPktSentKnown_A, intr_pkt_sent_o)
  `ASSERT_KNOWN(USBIntrPwrdKnown_A, intr_powered_o)
  `ASSERT_KNOWN(USBIntrDisConKnown_A, intr_disconnected_o)
  `ASSERT_KNOWN(USBIntrHostLostKnown_A, intr_host_lost_o)
  `ASSERT_KNOWN(USBIntrLinkRstKnown_A, intr_link_reset_o)
  `ASSERT_KNOWN(USBIntrLinkSusKnown_A, intr_link_suspend_o)
  `ASSERT_KNOWN(USBIntrLinkResKnown_A, intr_link_resume_o)
  `ASSERT_KNOWN(USBIntrAvEmptyKnown_A, intr_av_empty_o)
  `ASSERT_KNOWN(USBIntrRxFullKnown_A, intr_rx_full_o)
  `ASSERT_KNOWN(USBIntrAvOverKnown_A, intr_av_overflow_o)
  `ASSERT_KNOWN(USBIntrLinkInErrKnown_A, intr_link_in_err_o)
  `ASSERT_KNOWN(USBIntrLinkOutErrKnown_A, intr_link_out_err_o)
  `ASSERT_KNOWN(USBIntrRxCrCErrKnown_A, intr_rx_crc_err_o)
  `ASSERT_KNOWN(USBIntrRxPidErrKnown_A, intr_rx_pid_err_o)
  `ASSERT_KNOWN(USBIntrRxBitstuffErrKnown_A, intr_rx_bitstuff_err_o)
  `ASSERT_KNOWN(USBIntrFrameKnown_A, intr_frame_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
