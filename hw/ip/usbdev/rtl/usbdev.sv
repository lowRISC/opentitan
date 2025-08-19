// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// USB Full Speed Device Interface (usbdev).

`include "prim_assert.sv"

module usbdev
  import usbdev_pkg::*;
  import usbdev_reg_pkg::*;
  import prim_util_pkg::vbits;
#(
  parameter bit Stub = 1'b0,
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  // Number of cycles of differential skew tolerated on the alert signal.
  parameter int unsigned AlertSkewCycles = 1,
  // Max time (in microseconds) from rx_enable_o high to the
  // external differential receiver outputting valid data (when
  // configured to use one).
  parameter int unsigned RcvrWakeTimeUs = 1
) (
  input  logic       clk_i,
  input  logic       rst_ni,
  input  logic       clk_aon_i,
  input  logic       rst_aon_ni,

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
  input  logic       usb_aon_bus_not_idle_i,
  input  logic       usb_aon_wake_detect_active_i,

  // SOF reference for clock calibration
  output logic       usb_ref_val_o,
  output logic       usb_ref_pulse_o,

  // memory configuration
  input  prim_ram_1p_pkg::ram_1p_cfg_t     ram_cfg_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t ram_cfg_rsp_o,

  // Interrupts
  output logic       intr_pkt_received_o, // Packet received
  output logic       intr_pkt_sent_o, // Packet sent
  output logic       intr_powered_o,
  output logic       intr_disconnected_o,
  output logic       intr_host_lost_o,
  output logic       intr_link_reset_o,
  output logic       intr_link_suspend_o,
  output logic       intr_link_resume_o,
  output logic       intr_av_out_empty_o,
  output logic       intr_rx_full_o,
  output logic       intr_av_overflow_o,
  output logic       intr_link_in_err_o,
  output logic       intr_link_out_err_o,
  output logic       intr_rx_crc_err_o,
  output logic       intr_rx_pid_err_o,
  output logic       intr_rx_bitstuff_err_o,
  output logic       intr_frame_o,
  output logic       intr_av_setup_empty_o
);

  // Could make SramDepth, MaxPktSizeByte, AVSetupFifoDepth, AVOutFifoDepth and RXFifoDepth
  // module parameters but may need to fix register def for the first two
  localparam int SramDw = 32; // Places packing bytes to SRAM assume this
  localparam int SramDepth = 512; // 2kB, SRAM Width is DW
  localparam int MaxPktSizeByte = 64;

  localparam int SramAw = $clog2(SramDepth);
  localparam int SizeWidth = $clog2(MaxPktSizeByte);
  localparam int NBuf = (SramDepth * SramDw) / (MaxPktSizeByte * 8);
  localparam int NBufWidth = $clog2(NBuf);

  // AV SETUP and AV OUT fifos just store buffer numbers
  localparam int AVFifoWidth = NBufWidth;
  localparam int AVSetupFifoDepth = 4;
  localparam int AVOutFifoDepth = 8;

  // RX fifo stores              buf# +  size(0-MaxPktSizeByte)  + EP# + Type
  localparam int RXFifoWidth = NBufWidth + (1+SizeWidth)         +  4  + 1;
  localparam int RXFifoDepth = 8;
  // derived parameter
  localparam int RXFifoDepthW = prim_util_pkg::vbits(RXFifoDepth+1);

  usbdev_reg2hw_t reg2hw, reg2hw_regtop;
  usbdev_hw2reg_t hw2reg, hw2reg_regtop;

  logic rst_n;
  if (Stub) begin : gen_stubbed_reset
    assign rst_n = '0;
  end else begin : gen_no_stubbed_reset
    assign rst_n = rst_ni;
  end

  tlul_pkg::tl_h2d_t tl_sram_h2d;
  tlul_pkg::tl_d2h_t tl_sram_d2h;

  // Software access to the Packet Buffer RAM
  logic              sw_mem_a_req;
  logic              sw_mem_a_gnt;
  logic              sw_mem_a_write;
  logic [SramAw-1:0] sw_mem_a_addr;
  logic [SramDw-1:0] sw_mem_a_wdata;
  logic              sw_mem_a_rvalid;
  logic [SramDw-1:0] sw_mem_a_rdata;
  logic [1:0]        sw_mem_a_rerror;

  // usbdev hardware access to the Packet Buffer RAM
  logic              usb_mem_b_req;
  logic              usb_mem_b_write;
  logic [SramAw-1:0] usb_mem_b_addr;
  logic [SramDw-1:0] usb_mem_b_wdata;
  logic [SramDw-1:0] usb_mem_b_rdata;

  logic              clr_devaddr;
  logic              event_av_setup_empty, event_av_out_empty, event_av_overflow, event_rx_full;
  logic              link_reset, link_suspend;
  logic              host_lost, link_disconnect, link_powered;
  logic              event_link_reset, event_link_suspend, event_link_resume;
  logic              event_host_lost, event_disconnect, event_powered;
  logic              event_rx_crc5_err, event_rx_crc16_err;
  logic              event_rx_crc_err, event_rx_pid_err;
  logic              event_rx_bitstuff_err;
  logic              event_in_err;
  logic              event_out_err;
  logic              event_frame, event_sof;
  logic              link_active;

  // Diagnostic visibility of OUT-side exceptional events
  logic              event_ign_avsetup, event_drop_avout, event_drop_rx, event_datatog_out;
  // Diagnostic visibility of IN-side exceptional events
  logic              event_timeout_in, event_nak_in, event_nodata_in;

  // Interrupt to software reports both types of CRC error; they are separated only for the
  // purpose of diagnostic event counting.
  assign event_rx_crc_err = event_rx_crc5_err | event_rx_crc16_err;

  logic [10:0]       frame;
  logic [2:0]        link_state;
  logic              connect_en;
  logic              resume_link_active;

  // Current state of OUT data toggles
  logic [NEndpoints-1:0] out_data_toggle;
  // Write strobe from register interface
  logic                  out_datatog_we;
  // Write data from register interface
  logic [NEndpoints-1:0] out_datatog_status;
  logic [NEndpoints-1:0] out_datatog_mask;

  // Current state of IN data toggles
  logic [NEndpoints-1:0] in_data_toggle;
  // Write strobe from register interface
  logic                  in_datatog_we;
  // Write data from register interface
  logic [NEndpoints-1:0] in_datatog_status;
  logic [NEndpoints-1:0] in_datatog_mask;

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
  // USB control pins after CDC  //
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

  assign us_tick = (ns_cnt == 6'd47);
  always_ff @(posedge clk_i or negedge rst_n) begin
    if (!rst_n) begin
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

  logic              avsetup_fifo_rst;
  logic              avsetup_fifo_wready;
  logic              avout_fifo_rst;
  logic              avout_fifo_wready;
  logic              event_pkt_received;
  logic              avsetup_rvalid, avsetup_rready;
  logic              avout_rvalid, avout_rready;
  logic              rx_fifo_rst;
  logic              rx_wvalid, rx_wready;
  logic              rx_wready_setup, rx_wready_out;
  logic              rx_fifo_rvalid;
  logic              rx_fifo_re;

  logic [AVFifoWidth - 1:0] avsetup_rdata;
  logic [AVFifoWidth - 1:0] avout_rdata;
  logic [RXFifoWidth - 1:0] rx_wdata, rx_rdata;

  logic [NEndpoints-1:0] clear_rxenable_out;

  // Software reset signals
  assign avsetup_fifo_rst = reg2hw.fifo_ctrl.avsetup_rst.qe & reg2hw.fifo_ctrl.avsetup_rst.q;
  assign avout_fifo_rst = reg2hw.fifo_ctrl.avout_rst.qe & reg2hw.fifo_ctrl.avout_rst.q;
  assign rx_fifo_rst = reg2hw.fifo_ctrl.rx_rst.qe & reg2hw.fifo_ctrl.rx_rst.q;

  // Separate 'FIFO empty' interrupts for the OUT and SETUP FIFOs because each interrupt cannot be
  // cleared without writing a buffer into the FIFO
  assign event_av_setup_empty = connect_en & ~avsetup_rvalid;
  assign event_av_out_empty = connect_en & ~avout_rvalid;
  // A single 'overflow' interrupt suffices since this indicates a programming error
  assign event_av_overflow = (reg2hw.avsetupbuffer.qe & (~avsetup_fifo_wready))
                           | (reg2hw.avoutbuffer.qe   & (~avout_fifo_wready));
  assign hw2reg.usbstat.rx_empty.d = connect_en & ~rx_fifo_rvalid;

  // Available SETUP Buffer FIFO
  prim_fifo_sync #(
    .Width(AVFifoWidth),
    .Pass(1'b0),
    .Depth(AVSetupFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) usbdev_avsetupfifo (
    .clk_i,
    .rst_ni    (rst_n),
    .clr_i     (avsetup_fifo_rst),

    .wvalid_i  (reg2hw.avsetupbuffer.qe),
    .wready_o  (avsetup_fifo_wready),
    .wdata_i   (reg2hw.avsetupbuffer.q),

    .rvalid_o  (avsetup_rvalid),
    .rready_i  (avsetup_rready),
    .rdata_o   (avsetup_rdata),
    .full_o    (hw2reg.usbstat.av_setup_full.d),
    .depth_o   (hw2reg.usbstat.av_setup_depth.d),
    .err_o     ()
  );

  // Available OUT Buffer FIFO
  prim_fifo_sync #(
    .Width(AVFifoWidth),
    .Pass(1'b0),
    .Depth(AVOutFifoDepth),
    .OutputZeroIfEmpty(1'b0)
  ) usbdev_avoutfifo (
    .clk_i,
    .rst_ni    (rst_n),
    .clr_i     (avout_fifo_rst),

    .wvalid_i  (reg2hw.avoutbuffer.qe),
    .wready_o  (avout_fifo_wready),
    .wdata_i   (reg2hw.avoutbuffer.q),

    .rvalid_o  (avout_rvalid),
    .rready_i  (avout_rready),
    .rdata_o   (avout_rdata),
    .full_o    (hw2reg.usbstat.av_out_full.d),
    .depth_o   (hw2reg.usbstat.av_out_depth.d),
    .err_o     ()
  );

  assign rx_fifo_re = reg2hw.rxfifo.ep.re | reg2hw.rxfifo.setup.re |
                      reg2hw.rxfifo.size.re | reg2hw.rxfifo.buffer.re;

  // The number of used entries in the Received Buffer FIFO is presented to the software
  logic [RXFifoDepthW-1:0] rx_depth;
  assign hw2reg.usbstat.rx_depth.d = rx_depth;

  // We can always accept a SETUP packet if the Received Buffer FIFO is not full...
  assign rx_wready_setup = rx_wready;
  // ... but regular OUT packets are not permitted to use the final entry; still qualified
  // with 'rx_wready' for when reset is asserted.
  assign rx_wready_out   = rx_wready & (rx_depth < RXFifoDepthW'(RXFifoDepth - 1));

  // Received Buffer FIFO
  prim_fifo_sync #(
    .Width(RXFifoWidth),
    .Pass(1'b0),
    .Depth(RXFifoDepth),
    .OutputZeroIfEmpty(1'b1)
  ) usbdev_rxfifo (
    .clk_i,
    .rst_ni    (rst_n),
    .clr_i     (rx_fifo_rst),

    .wvalid_i  (rx_wvalid),
    .wready_o  (rx_wready),
    .wdata_i   (rx_wdata),

    .rvalid_o  (rx_fifo_rvalid),
    .rready_i  (rx_fifo_re),
    .rdata_o   (rx_rdata),
    .full_o    (event_rx_full),
    .depth_o   (rx_depth),
    .err_o     ()
  );

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
  logic [NBufWidth-1:0]  in_buf [NEndpoints];
  logic [SizeWidth:0]    in_size [NEndpoints];
  logic [3:0]            in_endpoint;
  logic                  in_endpoint_val;
  logic [NEndpoints-1:0] in_rdy;
  logic [NEndpoints-1:0] clear_rdybit, set_sentbit, update_pend, set_sending;
  logic                  setup_received, in_ep_xact_end;
  logic [NEndpoints-1:0] ep_out_iso, ep_in_iso;
  logic [NEndpoints-1:0] enable_out, enable_setup, in_ep_stall, out_ep_stall;
  logic [NEndpoints-1:0] ep_set_nak_on_out;
  logic [NEndpoints-1:0] ep_in_enable, ep_out_enable;
  logic [3:0]            out_endpoint;
  logic                  out_endpoint_val;
  logic                  use_diff_rcvr, usb_diff_rx_ok;

  // Endpoint enables
  always_comb begin : proc_map_ep_enable
    for (int i = 0; i < NEndpoints; i++) begin
      ep_in_enable[i] = reg2hw.ep_in_enable[i].q;
      ep_out_enable[i] = reg2hw.ep_out_enable[i].q;
    end
  end

  // RX enables
  logic [NEndpoints-1:0] rxenable_out;
  always_comb begin : proc_map_rxenable
    for (int i = 0; i < NEndpoints; i++) begin
      enable_setup[i] = reg2hw.rxenable_setup[i].q;
      enable_out[i]   = rxenable_out[i];
      ep_set_nak_on_out[i] = reg2hw.set_nak_out[i].q;
    end
  end

  // STALL for both directions
  always_comb begin : proc_map_stall
    for (int i = 0; i < NEndpoints; i++) begin
      in_ep_stall[i] = reg2hw.in_stall[i];
      out_ep_stall[i] = reg2hw.out_stall[i];
    end
  end

  always_comb begin : proc_map_iso
    for (int i = 0; i < NEndpoints; i++) begin
      ep_out_iso[i] = reg2hw.out_iso[i].q;
      ep_in_iso[i] = reg2hw.in_iso[i].q;
    end
  end

  always_comb begin : proc_map_buf_size
    for (int i = 0; i < NEndpoints; i++) begin
      in_buf[i]  = reg2hw.configin[i].buffer.q;
      in_size[i] = reg2hw.configin[i].size.q;
    end
  end

  always_comb begin : proc_map_rdy_reg2hw
    for (int i = 0; i < NEndpoints; i++) begin
      in_rdy[i] = reg2hw.configin[i].rdy.q;
    end
  end

  // Captured properties of current IN buffer, maintained throughout packet collection as
  // protection against change during packet retraction by FW.
  logic [NBufWidth-1:0] in_buf_q, in_buf_d;
  logic [SizeWidth:0] in_size_q, in_size_d;
  logic       in_xact_starting;
  logic [3:0] in_xact_start_ep;

  always_ff @(posedge clk_i or negedge rst_n) begin
    if (!rst_n) begin
      in_buf_q  <= '0;
      in_size_q <= '0;
    end else begin
      in_buf_q  <= in_buf_d;
      in_size_q <= in_size_d;
    end
  end
  assign in_buf_d  = in_xact_starting ? in_buf[in_xact_start_ep]  : in_buf_q;
  assign in_size_d = in_xact_starting ? in_size[in_xact_start_ep] : in_size_q;

  // OUT data toggles are maintained with the packet engine but may be set or
  // cleared by software
  assign out_datatog_we = reg2hw.out_data_toggle.status.qe & reg2hw.out_data_toggle.mask.qe;
  assign out_datatog_status = reg2hw.out_data_toggle.status.q;
  assign out_datatog_mask = reg2hw.out_data_toggle.mask.q;
  // Software may read tham at any time
  assign hw2reg.out_data_toggle.status.d = out_data_toggle;
  assign hw2reg.out_data_toggle.mask.d = {NEndpoints{1'b0}};

  // IN data toggles are maintained with the packet engine but may be set or
  // cleared by software
  assign in_datatog_we = reg2hw.in_data_toggle.status.qe & reg2hw.in_data_toggle.mask.qe;
  assign in_datatog_status = reg2hw.in_data_toggle.status.q;
  assign in_datatog_mask = reg2hw.in_data_toggle.mask.q;
  // Software may read them at any time
  assign hw2reg.in_data_toggle.status.d = in_data_toggle;
  assign hw2reg.in_data_toggle.mask.d = {NEndpoints{1'b0}};

  always_comb begin
    set_sentbit = '0;
    if (in_ep_xact_end && in_endpoint_val) begin
      set_sentbit[in_endpoint] = 1'b1;
    end
  end

  always_comb begin : proc_map_sent
    for (int i = 0; i < NEndpoints; i++) begin
      hw2reg.in_sent[i].de = set_sentbit[i];
      hw2reg.in_sent[i].d  = 1'b1;
    end
  end

  // This must be held level for the interrupt, so no sent packets are missed.
  logic sent_event_pending;
  always_comb begin
    sent_event_pending = 1'b0;
    for (int i = 0; i < NEndpoints; i++) begin
      sent_event_pending |= reg2hw.in_sent[i].q;
    end
  end

  // rxenable_out register must be implemented as 'hwext' so that we can treat each endpoint
  // individually and prevent sw/hw races from inadvertently re-enabling an endpoint that was
  // recently disabled by the hardware.
  logic [NEndpoints-1:0] rxenable_out_we;
  assign rxenable_out_we = {NEndpoints{reg2hw.rxenable_out.out.qe &
                                       reg2hw.rxenable_out.preserve.qe}} &
                           ~reg2hw.rxenable_out.preserve.q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rxenable_out <= 'b0;
    end else begin
      for (int unsigned i = 0; i < NEndpoints; i++) begin
        if (rxenable_out_we[i]) begin
          // Software wins for backwards compatibility; an earlier implementation employed the
          // module `prim_subreg_arb` which exhibits this behavior.
          rxenable_out[i] <= reg2hw.rxenable_out.out.q[i];
        end else if (clear_rxenable_out[i]) begin
          rxenable_out[i] <= 1'b0;
        end
      end
    end
  end
  assign hw2reg.rxenable_out.out.d = rxenable_out;

  // Clear of rxenable_out bit
  // If so configured, for every received transaction on a given endpoint, clear
  // the rxenable_out bit. In this configuration, hardware defaults to NAKing
  // any subsequent transaction, so software has time to decide the next
  // response.
  always_comb begin
    clear_rxenable_out = '0;
    if (rx_wvalid && out_endpoint_val) begin
      clear_rxenable_out[out_endpoint] = ep_set_nak_on_out[out_endpoint];
    end
  end

  always_comb begin
    clear_rdybit = '0;
    update_pend  = '0;
    if (event_link_reset) begin
      clear_rdybit = {NEndpoints{1'b1}};
      update_pend  = {NEndpoints{1'b1}};
    end else begin
      if (setup_received & out_endpoint_val) begin
        // Clear pending when a SETUP is received
        clear_rdybit[out_endpoint]   = 1'b1;
        update_pend[out_endpoint]    = 1'b1;
      end else if (in_ep_xact_end & in_endpoint_val) begin
        // Clear rdy and sending when an IN transmission was successful
        clear_rdybit[in_endpoint]   = 1'b1;
      end
    end
  end

  // IN transaction starting on any endpoint?
  always_comb begin
    set_sending = '0;
    if (in_xact_starting) set_sending[in_xact_start_ep] = 1'b1;
  end

  // Clearing of rdy bit in response to successful IN packet transmission or packet cancellation
  // through link reset or SETUP packet reception.
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

  // Update the sending bit to mark that collection of the packet by the USB host has been
  // attempted and FW shall not attempt retraction of the packet.
  always_comb begin : proc_map_sending
    for (int i = 0; i < NEndpoints; i++) begin
      hw2reg.configin[i].sending.de = set_sending[i] | set_sentbit[i] | update_pend[i];
      hw2reg.configin[i].sending.d  = ~set_sentbit[i] & ~update_pend[i];
    end
  end

  ////////////////////////////////////////////////////////
  // USB interface -- everything is in USB clock domain //
  ////////////////////////////////////////////////////////
  logic cfg_pinflip;
  assign cfg_pinflip = reg2hw.phy_config.pinflip.q;
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
    .clk_48mhz_i          (clk_i),
    .rst_ni               (rst_n),

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
    .rx_setup_i           (enable_setup),
    .rx_out_i             (enable_out),
    .rx_stall_i           (out_ep_stall),
    .avsetup_rvalid_i     (avsetup_rvalid),
    .avsetup_rready_o     (avsetup_rready),
    .avsetup_rdata_i      (avsetup_rdata),
    .avout_rvalid_i       (avout_rvalid),
    .avout_rready_o       (avout_rready),
    .avout_rdata_i        (avout_rdata),

    .rx_wvalid_o          (rx_wvalid),
    .rx_wready_setup_i    (rx_wready_setup),
    .rx_wready_out_i      (rx_wready_out),
    .rx_wdata_o           (rx_wdata),
    .setup_received_o     (setup_received),
    .out_endpoint_o       (out_endpoint),  // will be stable for several cycles
    .out_endpoint_val_o   (out_endpoint_val),

    // transmit side
    .in_xact_starting_o   (in_xact_starting),
    .in_xact_start_ep_o   (in_xact_start_ep),
    .in_buf_i             (in_buf_q),
    .in_size_i            (in_size_q),
    .in_stall_i           (in_ep_stall),
    .in_rdy_i             (in_rdy),
    .in_ep_xact_end_o     (in_ep_xact_end),
    .in_endpoint_o        (in_endpoint),
    .in_endpoint_val_o    (in_endpoint_val),

    // memory
    .mem_req_o            (usb_mem_b_req),
    .mem_write_o          (usb_mem_b_write),
    .mem_addr_o           (usb_mem_b_addr),
    .mem_wdata_o          (usb_mem_b_wdata),
    .mem_rdata_i          (usb_mem_b_rdata),

    // time reference
    .us_tick_i            (us_tick),

    // control
    .connect_en_i         (connect_en),
    .devaddr_i            (reg2hw.usbctrl.device_address.q),
    .clr_devaddr_o        (clr_devaddr),
    .in_ep_enabled_i      (ep_in_enable),
    .out_ep_enabled_i     (ep_out_enable),
    .out_ep_iso_i         (ep_out_iso),
    .in_ep_iso_i          (ep_in_iso),
    .diff_rx_ok_i         (usb_diff_rx_ok),
    .cfg_eop_single_bit_i (reg2hw.phy_config.eop_single_bit.q), // cdc ok: quasi-static
    .tx_osc_test_mode_i   (reg2hw.phy_config.tx_osc_test_mode.q), // cdc ok: quasi-static
    .cfg_use_diff_rcvr_i  (usb_rx_enable_o),
    .cfg_pinflip_i        (cfg_pinflip),
    .out_data_toggle_o    (out_data_toggle),
    .out_datatog_we_i     (out_datatog_we),
    .out_datatog_status_i (out_datatog_status),
    .out_datatog_mask_i   (out_datatog_mask),
    .in_data_toggle_o     (in_data_toggle),
    .in_datatog_we_i      (in_datatog_we),
    .in_datatog_status_i  (in_datatog_status),
    .in_datatog_mask_i    (in_datatog_mask),

    .resume_link_active_i (resume_link_active),

    // status
    .frame_o              (frame),
    .frame_start_o        (event_frame),
    .sof_detected_o       (event_sof),
    .link_state_o         (link_state),
    .link_disconnect_o    (link_disconnect),
    .link_powered_o       (link_powered),
    .link_reset_o         (link_reset),
    .link_active_o        (link_active),
    .link_suspend_o       (link_suspend),
    .link_resume_o        (event_link_resume),
    .host_lost_o          (host_lost),
    .link_in_err_o        (event_in_err),
    .link_out_err_o       (event_out_err),
    .rx_crc5_err_o        (event_rx_crc5_err),
    .rx_crc16_err_o       (event_rx_crc16_err),
    .rx_pid_err_o         (event_rx_pid_err),
    .rx_bitstuff_err_o    (event_rx_bitstuff_err),

    // event counters
    .event_ign_avsetup_o  (event_ign_avsetup),
    .event_drop_avout_o   (event_drop_avout),
    .event_drop_rx_o      (event_drop_rx),
    .event_datatog_out_o  (event_datatog_out),
    .event_timeout_in_o   (event_timeout_in),
    .event_nak_in_o       (event_nak_in),
    .event_nodata_in_o    (event_nodata_in)
  );

  /////////////////////////////////
  // Control signal / status CDC //
  /////////////////////////////////

  assign hw2reg.usbstat.link_state.d = link_state;
  assign hw2reg.usbstat.frame.d = frame;

  assign connect_en = reg2hw.usbctrl.enable.q;
  assign resume_link_active = reg2hw.usbctrl.resume_link_active.qe &
                              reg2hw.usbctrl.resume_link_active.q;

  // Just want a pulse to ensure only one interrupt for an event
  prim_edge_detector #(
    .Width(5),
    .EnSync(1'b0)
  ) gen_event (
    .clk_i,
    .rst_ni           (rst_n),
    .d_i              ({link_disconnect, link_reset, link_suspend,
                        host_lost, link_powered}),
    .q_sync_o         (),
    .q_posedge_pulse_o({event_disconnect, event_link_reset, event_link_suspend,
                        event_host_lost, event_powered}),
    .q_negedge_pulse_o()
  );

  assign hw2reg.usbstat.host_lost.d = host_lost;

  // resets etc cause the device address to clear
  assign hw2reg.usbctrl.device_address.de = clr_devaddr;
  assign hw2reg.usbctrl.device_address.d = '0;

  // Clear the stall flag when a SETUP is received

  always_comb begin : proc_stall_tieoff
    for (int i = 0; i < NEndpoints; i++) begin
      hw2reg.in_stall[i].d  = 1'b0;
      hw2reg.out_stall[i].d  = 1'b0;
      if (setup_received && out_endpoint_val && out_endpoint == 4'(unsigned'(i))) begin
        hw2reg.out_stall[i].de = 1'b1;
        hw2reg.in_stall[i].de = 1'b1;
      end else begin
        hw2reg.out_stall[i].de = 1'b0;
        hw2reg.in_stall[i].de = 1'b0;
      end
    end
  end

  if (Stub) begin : gen_stubbed_memory
    // Stub this window off with an error responder if stubbed.
    tlul_err_resp u_tlul_err_resp (
      .clk_i,
      .rst_ni,
      .tl_h_i(tl_sram_h2d),
      .tl_h_o(tl_sram_d2h)
    );

    // Tie off unused signals
    assign sw_mem_a_req    = '0;
    assign sw_mem_a_gnt    = '0;
    assign sw_mem_a_write  = '0;
    assign sw_mem_a_addr   = '0;
    assign sw_mem_a_wdata  = '0;
    assign sw_mem_a_rvalid = '0;
    assign sw_mem_a_rdata  = '0;
    assign sw_mem_a_rerror = '0;

    assign usb_mem_b_rdata = '0;
    assign ram_cfg_rsp_o   = '0;

    logic unused_usb_mem_b_sigs;
    assign unused_usb_mem_b_sigs = ^{
      ram_cfg_i,
      usb_mem_b_req,
      usb_mem_b_write,
      usb_mem_b_addr,
      usb_mem_b_wdata,
      usb_mem_b_rdata
    };
  end else begin : gen_no_stubbed_memory
    // TL-UL to SRAM adapter
    tlul_adapter_sram #(
      .SramAw(SramAw),
      .ByteAccess(0)
    ) u_tlul2sram (
      .clk_i,
      .rst_ni,

      .tl_i                       (tl_sram_h2d),
      .tl_o                       (tl_sram_d2h),
      .en_ifetch_i                (prim_mubi_pkg::MuBi4False),
      .req_o                      (sw_mem_a_req),
      .req_type_o                 (),
      .gnt_i                      (sw_mem_a_gnt),
      .we_o                       (sw_mem_a_write),
      .addr_o                     (sw_mem_a_addr),
      .wdata_o                    (sw_mem_a_wdata),
      .wmask_o                    (),           // Not used
      .intg_error_o               (),
      .user_rsvd_o                (),
      .rdata_i                    (sw_mem_a_rdata),
      .rvalid_i                   (sw_mem_a_rvalid),
      .rerror_i                   (sw_mem_a_rerror),
      .compound_txn_in_progress_o (),
      .readback_en_i              (prim_mubi_pkg::MuBi4False),
      .readback_error_o           (),
      .wr_collision_i             (1'b0),
      .write_pending_i            (1'b0)
    );

    // Single Port RAM implementation, which will award the `usb` port absolute priority and
    // delay `sw` access by in the event of a collision.
    //
    // In practice the `usb` access to memory is sporadic (4x oversampling of bits, and read/write
    // operations transfer 32 bits so on average the probability of collision is just 1/128 even
    // during active USB traffic, if the TL-UL interface were active on every cycle).

    // usb access has absolute priority, followed by any deferred write, and then any sw access.
    logic               mem_req;
    logic               mem_write;
    logic  [SramAw-1:0] mem_addr;
    logic  [SramDw-1:0] mem_wdata;
    assign mem_req   = usb_mem_b_req | sw_mem_a_req;
    assign mem_write = usb_mem_b_req ? usb_mem_b_write : sw_mem_a_write;
    assign mem_addr  = usb_mem_b_req ? usb_mem_b_addr  : sw_mem_a_addr;
    assign mem_wdata = usb_mem_b_req ? usb_mem_b_wdata : sw_mem_a_wdata;

    logic              mem_rvalid;
    logic [SramDw-1:0] mem_rdata;
    logic [1:0]        mem_rerror;
    logic              mem_rsteering;

    // Always grant when no `usb` request.
    assign sw_mem_a_gnt = !usb_mem_b_req;

    // `usb` relies upon its read data remaining static after read.
    logic              mem_b_read_q;
    logic [SramDw-1:0] mem_b_rdata_q;

    // Remember granted read accesses.
    // NOTE: No pipelining within the RAM model.
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        mem_rsteering <= 1'b0;
        mem_b_read_q  <= 1'b0;
        mem_b_rdata_q <= {SramDw{1'b0}};
      end else begin
        mem_rsteering <= usb_mem_b_req;
        mem_b_read_q  <= usb_mem_b_req & !usb_mem_b_write;
        // Capture the `usb` read data.
        if (mem_b_read_q)
          mem_b_rdata_q <= mem_rdata;
      end
    end

    // Read responses.
    assign sw_mem_a_rvalid  = mem_rvalid & !mem_rsteering;
    assign sw_mem_a_rerror  = {2{sw_mem_a_rvalid}} & mem_rerror;
    // We may safely return the read data to both (no security implications), but `usb` rdata
    // must be held static after the read, and be unaffected by `sw` reads.
    assign sw_mem_a_rdata  = mem_rdata;
    assign usb_mem_b_rdata = mem_b_read_q ? mem_rdata : mem_b_rdata_q;

    // SRAM Wrapper
    prim_ram_1p_adv #(
      .Depth (SramDepth),
      .Width (SramDw),    // 32 x 512 --> 2kB
      .DataBitsPerMask(8),

      .EnableECC           (0), // No Protection
      .EnableParity        (0),
      .EnableInputPipeline (0),
      .EnableOutputPipeline(0)
    ) u_memory_1p (
      .clk_i,
      .rst_ni,

      .req_i      (mem_req),
      .write_i    (mem_write),
      .addr_i     (mem_addr),
      .wdata_i    (mem_wdata),
      .wmask_i    ({SramDw{1'b1}}),
      .rdata_o    (mem_rdata),
      .rvalid_o   (mem_rvalid),
      .rerror_o   (mem_rerror),
      .cfg_i      (ram_cfg_i),
      .cfg_rsp_o  (ram_cfg_rsp_o),
      .alert_o    ()
    );
  end : gen_no_stubbed_memory

  logic [NumAlerts-1:0] alert_test, alerts;

  // Register module
  usbdev_reg_top u_reg (
    .clk_i,
    .rst_ni, // this reset is not stubbed off so that the registers are still accessible.
    .clk_aon_i,
    .rst_aon_ni, // this reset is not stubbed off so that the registers are still accessible.

    .tl_i (tl_i),
    .tl_o (tl_o),

    .tl_win_o (tl_sram_h2d),
    .tl_win_i (tl_sram_d2h),

    .reg2hw(reg2hw_regtop),
    .hw2reg(hw2reg_regtop),

    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (alerts[0])
  );

  // Stub off all register connections to reg_top.
  if (Stub) begin : gen_stubbed
    logic unused_sigs;
    assign reg2hw = '0;
    assign hw2reg_regtop = '0;
    assign unused_sigs = ^{reg2hw_regtop, hw2reg};
  end else begin : gen_not_stubbed
    assign reg2hw = reg2hw_regtop;
    assign hw2reg_regtop = hw2reg;
  end

  // Alerts
  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  // Alerts not stubbed off because registers and T-L access still present.
  localparam logic [NumAlerts-1:0] AlertIsFatal = {NumAlerts{1'b1}};
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .SkewCycles(AlertSkewCycles),
      .IsFatal(AlertIsFatal[i])
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni, // this reset is not stubbed off so that the pings still work.
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // Interrupts
  prim_intr_hw #(.Width(1), .IntrT("Status")) intr_hw_pkt_received (
    .clk_i,
    .rst_ni, // not stubbed off so that the interrupt regs still work.
    .event_intr_i           (event_pkt_received),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.pkt_received.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.pkt_received.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.pkt_received.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.pkt_received.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.pkt_received.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.pkt_received.d),
    .intr_o                 (intr_pkt_received_o)
  );

  prim_intr_hw #(.Width(1), .IntrT("Status")) intr_hw_pkt_sent (
    .clk_i,
    .rst_ni, // not stubbed off so that the interrupt regs still work.
    .event_intr_i           (sent_event_pending),
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
    .event_intr_i           (event_link_resume),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.link_resume.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.link_resume.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.link_resume.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.link_resume.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.link_resume.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.link_resume.d),
    .intr_o                 (intr_link_resume_o)
  );

  prim_intr_hw #(.Width(1), .IntrT("Status")) intr_av_out_empty (
    .clk_i,
    .rst_ni, // not stubbed off so that the interrupt regs still work.
    .event_intr_i           (event_av_out_empty),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.av_out_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.av_out_empty.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.av_out_empty.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.av_out_empty.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.av_out_empty.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.av_out_empty.d),
    .intr_o                 (intr_av_out_empty_o)
  );

  prim_intr_hw #(.Width(1), .IntrT("Status")) intr_rx_full (
    .clk_i,
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
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
    .rst_ni, // not stubbed off so that the interrupt regs still work.
    .event_intr_i           (event_frame),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.frame.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.frame.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.frame.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.frame.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.frame.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.frame.d),
    .intr_o                 (intr_frame_o)
  );

  prim_intr_hw #(.Width(1), .IntrT("Status")) intr_av_setup_empty (
    .clk_i,
    .rst_ni, // not stubbed off so that the interrupt regs still work.
    .event_intr_i           (event_av_setup_empty),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.av_setup_empty.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.av_setup_empty.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.av_setup_empty.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.av_setup_empty.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.av_setup_empty.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.av_setup_empty.d),
    .intr_o                 (intr_av_setup_empty_o)
  );

  /////////////////////////////////
  // USB IO Muxing               //
  /////////////////////////////////
  logic cio_usb_oe;
  logic usb_rx_enable;
  assign cio_usb_dp_en_o = cio_usb_oe;
  assign cio_usb_dn_en_o = cio_usb_oe;
  assign usb_tx_use_d_se0_o = reg2hw.phy_config.tx_use_d_se0.q; // cdc ok: quasi-static
  assign hw2reg.usbstat.sense.d = usb_pwr_sense;

  usbdev_iomux i_usbdev_iomux (
    .clk_i,
    .rst_ni             (rst_n),

    // Register interface
    .hw2reg_sense_o     (hw2reg.phy_pins_sense),
    .reg2hw_drive_i     (reg2hw.phy_pins_drive),

    // Chip IO
    .usb_rx_d_i             (usb_rx_d_i),
    .usb_rx_dp_i            (cio_usb_dp_i),
    .usb_rx_dn_i            (cio_usb_dn_i),
    .cio_usb_sense_i        (cio_sense_i),
    .usb_tx_d_o             (usb_tx_d_o),
    .usb_tx_se0_o           (usb_tx_se0_o),
    .usb_tx_dp_o            (cio_usb_dp_o),
    .usb_tx_dn_o            (cio_usb_dn_o),
    .usb_tx_oe_o            (cio_usb_oe),
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
  assign use_diff_rcvr = reg2hw.phy_config.use_diff_rcvr.q;
  // enable rx only when the single-ended input is enabled and the device is
  // not suspended (unless it is forced on in the I/O mux).
  assign usb_rx_enable = use_diff_rcvr & ~link_suspend;

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
    if (use_diff_rcvr & !usb_rx_enable_o) begin
      usb_rcvr_ok_counter_d = RcvrWakeTimeWidth'(RcvrWakeTimeUs + 1);
    end else if (us_tick && (usb_rcvr_ok_counter_q > '0)) begin
      usb_rcvr_ok_counter_d = usb_rcvr_ok_counter_q - 1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_n) begin
    if (!rst_n) begin
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
  assign usb_ref_disable = reg2hw.phy_config.usb_ref_disable.q;

  // Directly forward the pulse unless disabled.
  assign usb_ref_pulse_o = usb_ref_disable ? 1'b0 : event_sof;

  // The first pulse is always ignored, but causes the valid to be asserted.
  // The valid signal is deasserted when:
  // - The link is no longer active.
  // - The host is lost (no SOF for 4ms).
  // - The reference generation is disabled.
  assign usb_ref_val_d = usb_ref_pulse_o                           ? 1'b1 :
      (!link_active || host_lost || usb_ref_disable) ? 1'b0 : usb_ref_val_q;

  always_ff @(posedge clk_i or negedge rst_n) begin
    if (!rst_n) begin
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
  assign hw2reg.wake_events.bus_not_idle.de = 1'b1;
  assign hw2reg.wake_events.bus_not_idle.d = usb_aon_bus_not_idle_i;
  assign hw2reg.wake_events.disconnected.de = 1'b1;
  assign hw2reg.wake_events.disconnected.d = usb_aon_sense_lost_i;
  assign hw2reg.wake_events.bus_reset.de = 1'b1;
  assign hw2reg.wake_events.bus_reset.d = usb_aon_bus_reset_i;

  /////////////////////////////////////
  // Diagnostic/performance counters //
  /////////////////////////////////////

  // SW write strobes for the event enables of the counters.
  logic ctr_out_ev_qe;
  logic ctr_in_ev_qe;
  logic ctr_errors_ev_qe;
  assign ctr_out_ev_qe = &{reg2hw.count_out.ign_avsetup.qe,
                           reg2hw.count_out.drop_avout.qe,
                           reg2hw.count_out.drop_rx.qe,
                           reg2hw.count_out.datatog_out.qe};
  assign ctr_in_ev_qe = &{reg2hw.count_in.timeout.qe,
                          reg2hw.count_in.nak.qe,
                          reg2hw.count_in.nodata.qe};
  assign ctr_errors_ev_qe = &{reg2hw.count_errors.crc5.qe,
                              reg2hw.count_errors.crc16.qe,
                              reg2hw.count_errors.bitstuff.qe,
                              reg2hw.count_errors.pid_invalid.qe};

  // Counters use 'rst_n' and remain at zero in Stubbed implementation
  usbdev_counter #(.NEndpoints(NEndpoints), .NEvents(4)) u_ctr_out(
    .clk_i        (clk_i),
    .rst_ni       (rst_n),
    .reset_i      (reg2hw.count_out.rst.qe & reg2hw.count_out.rst.q),
    .event_i      ({event_ign_avsetup,
                    event_drop_avout,
                    event_drop_rx,
                    event_datatog_out}),
    .ep_i         (out_endpoint),
    // Set of events being counted.
    .ev_qe_i      (ctr_out_ev_qe),
    .ev_i         ({reg2hw.count_out.ign_avsetup.q,
                    reg2hw.count_out.drop_avout.q,
                    reg2hw.count_out.drop_rx.q,
                    reg2hw.count_out.datatog_out.q}),
    .ev_o         ({hw2reg.count_out.ign_avsetup.d,
                    hw2reg.count_out.drop_avout.d,
                    hw2reg.count_out.drop_rx.d,
                    hw2reg.count_out.datatog_out.d}),
    // Endpoints being monitored.
    .endp_qe_i    (reg2hw.count_out.endpoints.qe),
    .endpoints_i  (reg2hw.count_out.endpoints.q),
    .endpoints_o  (hw2reg.count_out.endpoints.d),
    .count_o      (hw2reg.count_out.count.d)
  );

  usbdev_counter #(.NEndpoints(NEndpoints), .NEvents(3)) u_ctr_in(
    .clk_i        (clk_i),
    .rst_ni       (rst_n),
    .reset_i      (reg2hw.count_in.rst.qe & reg2hw.count_in.rst.q),
    .event_i      ({event_timeout_in,
                    event_nak_in,
                    event_nodata_in}),
    .ep_i         (in_endpoint),
    // Set of events being counted.
    .ev_qe_i      (ctr_in_ev_qe),
    .ev_i         ({reg2hw.count_in.timeout.q,
                    reg2hw.count_in.nak.q,
                    reg2hw.count_in.nodata.q}),
    .ev_o         ({hw2reg.count_in.timeout.d,
                    hw2reg.count_in.nak.d,
                    hw2reg.count_in.nodata.d}),
    // Endpoints being monitored.
    .endp_qe_i    (reg2hw.count_in.endpoints.qe),
    .endpoints_i  (reg2hw.count_in.endpoints.q),
    .endpoints_o  (hw2reg.count_in.endpoints.d),
    .count_o      (hw2reg.count_in.count.d)
  );

  usbdev_counter #(.NEndpoints(NEndpoints), .NEvents(1)) u_ctr_nodata_in(
    .clk_i        (clk_i),
    .rst_ni       (rst_n),
    .reset_i      (reg2hw.count_nodata_in.rst.qe & reg2hw.count_nodata_in.rst.q),
    .event_i      (event_nodata_in),
    .ep_i         (in_endpoint),
    // Single event for this counter, so enables not required.
    .ev_qe_i      (1'b1),
    .ev_i         (1'b1),
    .ev_o         (), // not used
    // Endpoints being monitored.
    .endp_qe_i    (reg2hw.count_nodata_in.endpoints.qe),
    .endpoints_i  (reg2hw.count_nodata_in.endpoints.q),
    .endpoints_o  (hw2reg.count_nodata_in.endpoints.d),
    .count_o      (hw2reg.count_nodata_in.count.d)
  );

  usbdev_counter #(.NEndpoints(1), .NEvents(4)) u_ctr_errors(
    .clk_i        (clk_i),
    .rst_ni       (rst_n),
    .reset_i      (reg2hw.count_errors.rst.qe & reg2hw.count_errors.rst.q),
    .event_i      ({event_rx_crc5_err,
                    event_rx_crc16_err,
                    event_rx_bitstuff_err,
                    event_rx_pid_err}),
    .ep_i         (1'b0),
    // Set of events being counted.
    .ev_qe_i      (ctr_errors_ev_qe),
    .ev_i         ({reg2hw.count_errors.crc5.q,
                    reg2hw.count_errors.crc16.q,
                    reg2hw.count_errors.bitstuff.q,
                    reg2hw.count_errors.pid_invalid.q}),
    .ev_o         ({hw2reg.count_errors.crc5.d,
                    hw2reg.count_errors.crc16.d,
                    hw2reg.count_errors.bitstuff.d,
                    hw2reg.count_errors.pid_invalid.d}),
    // This events are not reliably associated with specific endpoints, so no endpoint enables.
    .endp_qe_i    (1'b1),
    .endpoints_i  (1'b1),
    .endpoints_o  (), // not used
    .count_o      (hw2reg.count_errors.count.d)
  );

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
  `ASSERT_KNOWN(USBRefValKnown_A, usb_ref_val_o, clk_i, !rst_ni)
  `ASSERT_KNOWN(USBRefPulseKnown_A, usb_ref_pulse_o, clk_i, !rst_ni)
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
  `ASSERT_KNOWN(USBIntrAvOutEmptyKnown_A, intr_av_out_empty_o)
  `ASSERT_KNOWN(USBIntrRxFullKnown_A, intr_rx_full_o)
  `ASSERT_KNOWN(USBIntrAvOverKnown_A, intr_av_overflow_o)
  `ASSERT_KNOWN(USBIntrLinkInErrKnown_A, intr_link_in_err_o)
  `ASSERT_KNOWN(USBIntrLinkOutErrKnown_A, intr_link_out_err_o)
  `ASSERT_KNOWN(USBIntrRxCrCErrKnown_A, intr_rx_crc_err_o)
  `ASSERT_KNOWN(USBIntrRxPidErrKnown_A, intr_rx_pid_err_o)
  `ASSERT_KNOWN(USBIntrRxBitstuffErrKnown_A, intr_rx_bitstuff_err_o)
  `ASSERT_KNOWN(USBIntrFrameKnown_A, intr_frame_o)
  `ASSERT_KNOWN(USBIntrAvSetupEmptyKnown_A, intr_av_setup_empty_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
