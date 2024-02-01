// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: I2C core module

module i2c_core import i2c_pkg::*;
(
  input                               clk_i,
  input                               rst_ni,
  input prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

  input i2c_reg_pkg::i2c_reg2hw_t  reg2hw,
  output i2c_reg_pkg::i2c_hw2reg_t hw2reg,

  input                            scl_i,
  output logic                     scl_o,
  input                            sda_i,
  output logic                     sda_o,

  output logic                     intr_fmt_threshold_o,
  output logic                     intr_rx_threshold_o,
  output logic                     intr_acq_threshold_o,
  output logic                     intr_rx_overflow_o,
  output logic                     intr_nak_o,
  output logic                     intr_scl_interference_o,
  output logic                     intr_sda_interference_o,
  output logic                     intr_stretch_timeout_o,
  output logic                     intr_sda_unstable_o,
  output logic                     intr_cmd_complete_o,
  output logic                     intr_tx_stretch_o,
  output logic                     intr_tx_threshold_o,
  output logic                     intr_acq_full_o,
  output logic                     intr_unexp_stop_o,
  output logic                     intr_host_timeout_o
);

  import i2c_reg_pkg::FifoDepth;
  import i2c_reg_pkg::AcqFifoDepth;

  // Number of bits required to represent the FIFO level/depth.
  localparam int unsigned FifoDepthW = $clog2(FifoDepth + 1);
  localparam int unsigned AcqFifoDepthW = $clog2(AcqFifoDepth+1);

  // Maximum number of bits required to represent the level/depth of any FIFO.
  localparam int unsigned MaxFifoDepthW = 12;

  logic [15:0] thigh;
  logic [15:0] tlow;
  logic [15:0] t_r;
  logic [15:0] t_f;
  logic [15:0] thd_sta;
  logic [15:0] tsu_sta;
  logic [15:0] tsu_sto;
  logic [15:0] tsu_dat;
  logic [15:0] thd_dat;
  logic [15:0] t_buf;
  logic [30:0] stretch_timeout;
  logic        timeout_enable;
  logic [31:0] host_timeout;
  logic [30:0] nack_timeout;
  logic        nack_timeout_en;
  logic [30:0] host_nack_handler_timeout;
  logic        host_nack_handler_timeout_en;

  logic scl_sync;
  logic sda_sync;
  logic scl_out_fsm;
  logic sda_out_fsm;

  logic event_rx_overflow;
  logic event_nak;
  logic event_scl_interference;
  logic event_sda_interference;
  logic event_stretch_timeout;
  logic event_sda_unstable;
  logic event_cmd_complete;
  logic event_target_nack;
  logic event_tx_stretch;
  logic event_unexp_stop;
  logic event_host_timeout;

  logic target_sr_p_cond;
  logic unhandled_unexp_nak;
  logic status_host_disabled_nack_timeout_d;
  logic status_host_disabled_nack_timeout_de;

  logic [15:0] scl_rx_val;
  logic [15:0] sda_rx_val;

  logic override;

  logic                      fmt_fifo_wvalid;
  logic                      fmt_fifo_wready;
  logic [FMT_FIFO_WIDTH-1:0] fmt_fifo_wdata;
  logic [FifoDepthW-1:0]     fmt_fifo_depth;
  logic                      fmt_fifo_rvalid;
  logic                      fmt_fifo_rready;
  logic [FMT_FIFO_WIDTH-1:0] fmt_fifo_rdata;
  logic [7:0]                fmt_byte;
  logic                      fmt_flag_start_before;
  logic                      fmt_flag_stop_after;
  logic                      fmt_flag_read_bytes;
  logic                      fmt_flag_read_continue;
  logic                      fmt_flag_nak_ok;

  logic                     i2c_fifo_rxrst;
  logic                     i2c_fifo_fmtrst;
  logic [MaxFifoDepthW-1:0] i2c_fifo_rx_thresh;
  logic [MaxFifoDepthW-1:0] i2c_fifo_fmt_thresh;

  logic                     rx_fifo_wvalid;
  logic                     rx_fifo_wready;
  logic [RX_FIFO_WIDTH-1:0] rx_fifo_wdata;
  logic [FifoDepthW-1:0]    rx_fifo_depth;
  logic                     rx_fifo_rvalid;
  logic                     rx_fifo_rready;
  logic [RX_FIFO_WIDTH-1:0] rx_fifo_rdata;

  // FMT FIFO level below programmed threshold?
  logic                     fmt_lt_threshold;
  // Rx FIFO level above programmed threshold?
  logic                     rx_gt_threshold;

  logic                     tx_fifo_wvalid;
  logic                     tx_fifo_wready;
  logic [TX_FIFO_WIDTH-1:0] tx_fifo_wdata;
  logic [FifoDepthW-1:0]    tx_fifo_depth;
  logic                     tx_fifo_rvalid;
  logic                     tx_fifo_rready;
  logic [TX_FIFO_WIDTH-1:0] tx_fifo_rdata;

  logic                      acq_fifo_wvalid;
  logic                      acq_fifo_wready;
  logic [ACQ_FIFO_WIDTH-1:0] acq_fifo_wdata;
  logic [AcqFifoDepthW-1:0]  acq_fifo_depth;
  logic                      acq_fifo_rvalid;
  logic                      acq_fifo_rready;
  logic [ACQ_FIFO_WIDTH-1:0] acq_fifo_rdata;

  logic                     i2c_fifo_txrst;
  logic                     i2c_fifo_acqrst;
  logic [MaxFifoDepthW-1:0] i2c_fifo_tx_thresh;
  logic [MaxFifoDepthW-1:0] i2c_fifo_acq_thresh;

  // Tx FIFO level below programmed threshold?
  logic        tx_lt_threshold;
  // ACQ FIFO level above programmed threshold?
  logic        acq_gt_threshold;

  logic        host_idle;
  logic        target_idle;

  logic        host_enable;
  logic        target_enable;
  logic        host_disable;
  logic        line_loopback;
  logic        target_loopback;

  logic [6:0]  target_address0;
  logic [6:0]  target_mask0;
  logic [6:0]  target_address1;
  logic [6:0]  target_mask1;

  // Unused parts of exposed bits
  logic        unused_ctrl_bits;
  logic        unused_rx_thr_qe;
  logic        unused_fmt_thr_qe;
  logic        unused_tx_thr_qe;
  logic        unused_acq_thr_qe;
  logic [7:0]  unused_rx_fifo_rdata_q;
  logic [7:0]  unused_acq_fifo_adata_q;
  logic [ACQ_FIFO_WIDTH-9:0] unused_acq_fifo_signal_q;
  logic        unused_alert_test_qe;
  logic        unused_alert_test_q;
  logic        unused_txrst_on_cond_qe;

  assign hw2reg.ctrl.enablehost.d = 1'b0;
  assign hw2reg.ctrl.enablehost.de = host_disable;
  assign hw2reg.ctrl.enabletarget.d = 1'b0;
  assign hw2reg.ctrl.enabletarget.de = 1'b0;
  assign hw2reg.ctrl.llpbk.d = 1'b0;
  assign hw2reg.ctrl.llpbk.de = 1'b0;

  assign hw2reg.status.fmtfull.d = ~fmt_fifo_wready;
  assign hw2reg.status.rxfull.d = ~rx_fifo_wready;
  assign hw2reg.status.fmtempty.d = ~fmt_fifo_rvalid;
  assign hw2reg.status.hostidle.d = host_idle;
  assign hw2reg.status.targetidle.d = target_idle;
  assign hw2reg.status.rxempty.d = ~rx_fifo_rvalid;

  assign hw2reg.rdata.d = rx_fifo_rdata;
  assign hw2reg.host_fifo_status.fmtlvl.d = MaxFifoDepthW'(fmt_fifo_depth);
  assign hw2reg.host_fifo_status.rxlvl.d = MaxFifoDepthW'(rx_fifo_depth);
  assign hw2reg.val.scl_rx.d = scl_rx_val;
  assign hw2reg.val.sda_rx.d = sda_rx_val;

  assign hw2reg.status.txfull.d = ~tx_fifo_wready;
  assign hw2reg.status.acqfull.d = ~acq_fifo_wready;
  assign hw2reg.status.txempty.d = ~tx_fifo_rvalid;
  assign hw2reg.status.acqempty.d = ~acq_fifo_rvalid;
  assign hw2reg.target_fifo_status.txlvl.d = MaxFifoDepthW'(tx_fifo_depth);
  assign hw2reg.target_fifo_status.acqlvl.d = MaxFifoDepthW'(acq_fifo_depth);
  assign hw2reg.acqdata.abyte.d = acq_fifo_rdata[7:0];
  assign hw2reg.acqdata.signal.d = acq_fifo_rdata[ACQ_FIFO_WIDTH-1:8];

  // Add one to the target NACK count if this target has sent a NACK and if
  // counter has not saturated.
  assign hw2reg.target_nack_count.de = event_target_nack && (reg2hw.target_nack_count.q < 8'hFF);
  assign hw2reg.target_nack_count.d  = reg2hw.target_nack_count.q + 1;

  assign override = reg2hw.ovrd.txovrden;

  assign scl_o = override ? reg2hw.ovrd.sclval : scl_out_fsm;
  assign sda_o = override ? reg2hw.ovrd.sdaval : sda_out_fsm;

  assign host_enable = reg2hw.ctrl.enablehost.q;
  assign target_enable = reg2hw.ctrl.enabletarget.q;
  assign line_loopback = reg2hw.ctrl.llpbk.q;

  // Target loopback simply plays back whatever is received from the external host
  // back to it.
  assign target_loopback = target_enable & line_loopback;

  assign target_address0 = reg2hw.target_id.address0.q;
  assign target_mask0 = reg2hw.target_id.mask0.q;
  assign target_address1 = reg2hw.target_id.address1.q;
  assign target_mask1 = reg2hw.target_id.mask1.q;

  // Sample scl_i and sda_i at system clock
  always_ff @ (posedge clk_i or negedge rst_ni) begin : rx_oversampling
    if(!rst_ni) begin
       scl_rx_val <= 16'h0;
       sda_rx_val <= 16'h0;
    end else begin
       scl_rx_val <= {scl_rx_val[14:0], scl_i};
       sda_rx_val <= {sda_rx_val[14:0], sda_i};
    end
  end

  assign thigh                        = reg2hw.timing0.thigh.q;
  assign tlow                         = reg2hw.timing0.tlow.q;
  assign t_r                          = reg2hw.timing1.t_r.q;
  assign t_f                          = reg2hw.timing1.t_f.q;
  assign tsu_sta                      = reg2hw.timing2.tsu_sta.q;
  assign thd_sta                      = reg2hw.timing2.thd_sta.q;
  assign tsu_dat                      = reg2hw.timing3.tsu_dat.q;
  assign thd_dat                      = reg2hw.timing3.thd_dat.q;
  assign tsu_sto                      = reg2hw.timing4.tsu_sto.q;
  assign t_buf                        = reg2hw.timing4.t_buf.q;
  assign stretch_timeout              = reg2hw.timeout_ctrl.val.q;
  assign timeout_enable               = reg2hw.timeout_ctrl.en.q;
  assign host_timeout                 = reg2hw.host_timeout_ctrl.q;
  assign nack_timeout                 = reg2hw.target_timeout_ctrl.val.q;
  assign nack_timeout_en              = reg2hw.target_timeout_ctrl.en.q;
  assign host_nack_handler_timeout    = reg2hw.host_nack_handler_timeout.val.q;
  assign host_nack_handler_timeout_en = reg2hw.host_nack_handler_timeout.en.q;

  assign i2c_fifo_rxrst      = reg2hw.fifo_ctrl.rxrst.q & reg2hw.fifo_ctrl.rxrst.qe;
  assign i2c_fifo_fmtrst     = reg2hw.fifo_ctrl.fmtrst.q & reg2hw.fifo_ctrl.fmtrst.qe;
  assign i2c_fifo_rx_thresh  = reg2hw.host_fifo_config.rx_thresh.q;
  assign i2c_fifo_fmt_thresh = reg2hw.host_fifo_config.fmt_thresh.q;

  assign i2c_fifo_txrst      = (reg2hw.fifo_ctrl.txrst.q & reg2hw.fifo_ctrl.txrst.qe) ||
                               (reg2hw.target_fifo_config.txrst_on_cond.q & target_sr_p_cond);
  assign i2c_fifo_acqrst     = reg2hw.fifo_ctrl.acqrst.q & reg2hw.fifo_ctrl.acqrst.qe;
  assign i2c_fifo_tx_thresh  = reg2hw.target_fifo_config.tx_thresh.q;
  assign i2c_fifo_acq_thresh = reg2hw.target_fifo_config.acq_thresh.q;

  // FMT FIFO level below programmed threshold?
  assign fmt_lt_threshold = (MaxFifoDepthW'(fmt_fifo_depth) < i2c_fifo_fmt_thresh);
  // Rx FIFO level above programmed threshold?
  assign rx_gt_threshold  = (MaxFifoDepthW'(rx_fifo_depth)  > i2c_fifo_rx_thresh);
  // Tx FIFO level below programmed threshold?
  assign tx_lt_threshold  = (MaxFifoDepthW'(tx_fifo_depth)  < i2c_fifo_tx_thresh);
  // ACQ FIFO level above programmed threshold?
  assign acq_gt_threshold = (MaxFifoDepthW'(acq_fifo_depth) > i2c_fifo_acq_thresh);

  assign event_rx_overflow = rx_fifo_wvalid & ~rx_fifo_wready;

  // The fifo write enable is controlled by fbyte, start, stop, read, rcont,
  // and nakok field qe bits.
  // When all qe bits are asserted, fdata is injected into the fifo.
  assign fmt_fifo_wvalid     = reg2hw.fdata.fbyte.qe &
                               reg2hw.fdata.start.qe &
                               reg2hw.fdata.stop.qe  &
                               reg2hw.fdata.readb.qe  &
                               reg2hw.fdata.rcont.qe &
                               reg2hw.fdata.nakok.qe;
  assign fmt_fifo_wdata[7:0] = reg2hw.fdata.fbyte.q;
  assign fmt_fifo_wdata[8]   = reg2hw.fdata.start.q;
  assign fmt_fifo_wdata[9]   = reg2hw.fdata.stop.q;
  assign fmt_fifo_wdata[10]  = reg2hw.fdata.readb.q;
  assign fmt_fifo_wdata[11]  = reg2hw.fdata.rcont.q;
  assign fmt_fifo_wdata[12]  = reg2hw.fdata.nakok.q;

  assign fmt_byte               = fmt_fifo_rvalid ? fmt_fifo_rdata[7:0] : '0;
  assign fmt_flag_start_before  = fmt_fifo_rvalid ? fmt_fifo_rdata[8] : '0;
  assign fmt_flag_stop_after    = fmt_fifo_rvalid ? fmt_fifo_rdata[9] : '0;
  assign fmt_flag_read_bytes    = fmt_fifo_rvalid ? fmt_fifo_rdata[10] : '0;
  assign fmt_flag_read_continue = fmt_fifo_rvalid ? fmt_fifo_rdata[11] : '0;
  assign fmt_flag_nak_ok        = fmt_fifo_rvalid ? fmt_fifo_rdata[12] : '0;

  // Operating this HWIP as a controller-transmitter, the addressed Target device
  // may NACK our bytes. In Byte-Formatted Programming Mode, each FDATA format indicator
  // can set the 'NAKOK' bit to ignore the Target's NACK and proceed to the next item in
  // the FMTFIFO. If 'NAKOK' is not set, the 'nak' interrupt is asserted, and the FSM
  // halts until software intervenes.
  // To acknowledge the 'NACK', software should acknowledge the interrupt using the
  // standard W1C mechanism to the INTR_STATE register.
  assign unhandled_unexp_nak = reg2hw.intr_state.nak.q;

  // Unused parts of exposed bits
  assign unused_ctrl_bits = ^{
    reg2hw.ctrl.enabletarget.qe,
    reg2hw.ctrl.llpbk.qe
  };
  assign unused_rx_thr_qe  = reg2hw.host_fifo_config.rx_thresh.qe;
  assign unused_fmt_thr_qe = reg2hw.host_fifo_config.fmt_thresh.qe;
  assign unused_tx_thr_qe  = reg2hw.target_fifo_config.tx_thresh.qe;
  assign unused_acq_thr_qe = reg2hw.target_fifo_config.acq_thresh.qe;
  assign unused_rx_fifo_rdata_q = reg2hw.rdata.q;
  assign unused_acq_fifo_adata_q = reg2hw.acqdata.abyte.q;
  assign unused_acq_fifo_signal_q = reg2hw.acqdata.signal.q;
  assign unused_alert_test_qe = reg2hw.alert_test.qe;
  assign unused_alert_test_q = reg2hw.alert_test.q;
  assign unused_txrst_on_cond_qe = reg2hw.target_fifo_config.txrst_on_cond.qe;

  i2c_fifos u_fifos (
    .clk_i,
    .rst_ni,
    .ram_cfg_i,

    .fmt_fifo_clr_i   (i2c_fifo_fmtrst),
    .fmt_fifo_depth_o (fmt_fifo_depth),
    .fmt_fifo_wvalid_i(fmt_fifo_wvalid),
    .fmt_fifo_wready_o(fmt_fifo_wready),
    .fmt_fifo_wdata_i (fmt_fifo_wdata),
    .fmt_fifo_rvalid_o(fmt_fifo_rvalid),
    .fmt_fifo_rready_i(fmt_fifo_rready),
    .fmt_fifo_rdata_o (fmt_fifo_rdata),

    .rx_fifo_clr_i   (i2c_fifo_rxrst),
    .rx_fifo_depth_o (rx_fifo_depth),
    .rx_fifo_wvalid_i(rx_fifo_wvalid),
    .rx_fifo_wready_o(rx_fifo_wready),
    .rx_fifo_wdata_i (rx_fifo_wdata),
    .rx_fifo_rvalid_o(rx_fifo_rvalid),
    .rx_fifo_rready_i(rx_fifo_rready),
    .rx_fifo_rdata_o (rx_fifo_rdata),

    .tx_fifo_clr_i   (i2c_fifo_txrst),
    .tx_fifo_depth_o (tx_fifo_depth),
    .tx_fifo_wvalid_i(tx_fifo_wvalid),
    .tx_fifo_wready_o(tx_fifo_wready),
    .tx_fifo_wdata_i (tx_fifo_wdata),
    .tx_fifo_rvalid_o(tx_fifo_rvalid),
    .tx_fifo_rready_i(tx_fifo_rready),
    .tx_fifo_rdata_o (tx_fifo_rdata),

    .acq_fifo_clr_i   (i2c_fifo_acqrst),
    .acq_fifo_depth_o (acq_fifo_depth),
    .acq_fifo_wvalid_i(acq_fifo_wvalid),
    .acq_fifo_wready_o(),
    .acq_fifo_wdata_i (acq_fifo_wdata),
    .acq_fifo_rvalid_o(acq_fifo_rvalid),
    .acq_fifo_rready_i(acq_fifo_rready),
    .acq_fifo_rdata_o (acq_fifo_rdata)
  );

  assign rx_fifo_rready = reg2hw.rdata.re;

  // Need to add a valid qualification to write only payload bytes
  logic valid_target_lb_wr;
  i2c_acq_byte_id_e acq_type;
  assign acq_type = i2c_acq_byte_id_e'(acq_fifo_rdata[ACQ_FIFO_WIDTH-1:8]);

  assign valid_target_lb_wr = target_enable & (acq_type == AcqData);

  // only write into tx fifo if it's payload
  assign tx_fifo_wvalid = target_loopback ? acq_fifo_rvalid & valid_target_lb_wr : reg2hw.txdata.qe;
  assign tx_fifo_wdata  = target_loopback ? acq_fifo_rdata[7:0] : reg2hw.txdata.q;

  // During line loopback, pop from acquisition fifo only when there is space in
  // the tx_fifo.  We are also allowed to pop even if there is no space if th acq entry
  // is not data payload.
  assign acq_fifo_rready = (reg2hw.acqdata.abyte.re & reg2hw.acqdata.signal.re) |
                           (target_loopback & (tx_fifo_wready | (acq_type != AcqData)));

  // sync the incoming SCL and SDA signals
  prim_flop_2sync #(
    .Width(1),
    .ResetValue(1'b1)
  ) u_i2c_sync_scl (
    .clk_i,
    .rst_ni,
    .d_i (scl_i),
    .q_o (scl_sync)
  );

  prim_flop_2sync #(
    .Width(1),
    .ResetValue(1'b1)
  ) u_i2c_sync_sda (
    .clk_i,
    .rst_ni,
    .d_i (sda_i),
    .q_o (sda_sync)
  );

  i2c_fsm #(
    .FifoDepth(FifoDepth),
    .AcqFifoDepth(AcqFifoDepth)
  ) u_i2c_fsm (
    .clk_i,
    .rst_ni,

    .scl_i                          (scl_sync),
    .scl_o                          (scl_out_fsm),
    .sda_i                          (sda_sync),
    .sda_o                          (sda_out_fsm),

    .host_enable_i                  (host_enable),
    .target_enable_i                (target_enable),
    .host_disable_o                 (host_disable),

    .fmt_fifo_rvalid_i       (fmt_fifo_rvalid),
    .fmt_fifo_depth_i        (fmt_fifo_depth),
    .fmt_fifo_rready_o       (fmt_fifo_rready),

    .fmt_byte_i                     (fmt_byte),
    .fmt_flag_start_before_i        (fmt_flag_start_before),
    .fmt_flag_stop_after_i          (fmt_flag_stop_after),
    .fmt_flag_read_bytes_i          (fmt_flag_read_bytes),
    .fmt_flag_read_continue_i       (fmt_flag_read_continue),
    .fmt_flag_nak_ok_i              (fmt_flag_nak_ok),
    .unhandled_unexp_nak_i          (unhandled_unexp_nak),

    .rx_fifo_wvalid_o               (rx_fifo_wvalid),
    .rx_fifo_wdata_o                (rx_fifo_wdata),

    .tx_fifo_rvalid_i        (tx_fifo_rvalid),
    .tx_fifo_rready_o        (tx_fifo_rready),
    .tx_fifo_rdata_i         (tx_fifo_rdata),

    .acq_fifo_wready_o              (acq_fifo_wready),
    .acq_fifo_wvalid_o              (acq_fifo_wvalid),
    .acq_fifo_wdata_o               (acq_fifo_wdata),
    .acq_fifo_rdata_i               (acq_fifo_rdata),
    .acq_fifo_depth_i               (acq_fifo_depth),

    .host_idle_o                    (host_idle),
    .target_idle_o                  (target_idle),

    .thigh_i                        (thigh),
    .tlow_i                         (tlow),
    .t_r_i                          (t_r),
    .t_f_i                          (t_f),
    .thd_sta_i                      (thd_sta),
    .tsu_sta_i                      (tsu_sta),
    .tsu_sto_i                      (tsu_sto),
    .tsu_dat_i                      (tsu_dat),
    .thd_dat_i                      (thd_dat),
    .t_buf_i                        (t_buf),
    .stretch_timeout_i              (stretch_timeout),
    .timeout_enable_i               (timeout_enable),
    .host_timeout_i                 (host_timeout),
    .nack_timeout_i                 (nack_timeout),
    .nack_timeout_en_i              (nack_timeout_en),
    .host_nack_handler_timeout_i    (host_nack_handler_timeout),
    .host_nack_handler_timeout_en_i (host_nack_handler_timeout_en),
    .target_address0_i              (target_address0),
    .target_mask0_i                 (target_mask0),
    .target_address1_i              (target_address1),
    .target_mask1_i                 (target_mask1),
    .target_sr_p_cond_o             (target_sr_p_cond),
    .event_target_nack_o            (event_target_nack),
    .event_nak_o                    (event_nak),
    .event_scl_interference_o       (event_scl_interference),
    .event_sda_interference_o       (event_sda_interference),
    .event_stretch_timeout_o        (event_stretch_timeout),
    .event_sda_unstable_o           (event_sda_unstable),
    .event_cmd_complete_o           (event_cmd_complete),
    .event_tx_stretch_o             (event_tx_stretch),
    .event_unexp_stop_o             (event_unexp_stop),
    .event_host_timeout_o           (event_host_timeout)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT("Status")
  ) intr_hw_fmt_threshold (
    .clk_i,
    .rst_ni,
    .event_intr_i           (fmt_lt_threshold),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.fmt_threshold.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.fmt_threshold.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.fmt_threshold.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.fmt_threshold.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.fmt_threshold.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.fmt_threshold.d),
    .intr_o                 (intr_fmt_threshold_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT("Status")
  ) intr_hw_rx_threshold (
    .clk_i,
    .rst_ni,
    .event_intr_i           (rx_gt_threshold),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.rx_threshold.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.rx_threshold.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.rx_threshold.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.rx_threshold.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.rx_threshold.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.rx_threshold.d),
    .intr_o                 (intr_rx_threshold_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT("Status")
  ) intr_hw_acq_threshold (
    .clk_i,
    .rst_ni,
    .event_intr_i           (acq_gt_threshold),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.acq_threshold.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.acq_threshold.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.acq_threshold.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.acq_threshold.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.acq_threshold.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.acq_threshold.d),
    .intr_o                 (intr_acq_threshold_o)
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

  prim_intr_hw #(.Width(1)) intr_hw_nak (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_nak),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.nak.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.nak.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.nak.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.nak.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.nak.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.nak.d),
    .intr_o                 (intr_nak_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_scl_interference (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_scl_interference),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.scl_interference.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.scl_interference.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.scl_interference.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.scl_interference.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.scl_interference.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.scl_interference.d),
    .intr_o                 (intr_scl_interference_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_sda_interference (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_sda_interference),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.sda_interference.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.sda_interference.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.sda_interference.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.sda_interference.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.sda_interference.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.sda_interference.d),
    .intr_o                 (intr_sda_interference_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_stretch_timeout (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_stretch_timeout),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.stretch_timeout.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.stretch_timeout.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.stretch_timeout.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.stretch_timeout.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.stretch_timeout.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.stretch_timeout.d),
    .intr_o                 (intr_stretch_timeout_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_sda_unstable (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_sda_unstable),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.sda_unstable.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.sda_unstable.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.sda_unstable.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.sda_unstable.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.sda_unstable.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.sda_unstable.d),
    .intr_o                 (intr_sda_unstable_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_cmd_complete (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_cmd_complete),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.cmd_complete.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.cmd_complete.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.cmd_complete.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.cmd_complete.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.cmd_complete.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.cmd_complete.d),
    .intr_o                 (intr_cmd_complete_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT("Status")
  ) intr_hw_tx_stretch (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_tx_stretch),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tx_stretch.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tx_stretch.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tx_stretch.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tx_stretch.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tx_stretch.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tx_stretch.d),
    .intr_o                 (intr_tx_stretch_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT("Status")
  ) intr_hw_tx_threshold (
    .clk_i,
    .rst_ni,
    .event_intr_i           (tx_lt_threshold),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.tx_threshold.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.tx_threshold.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.tx_threshold.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.tx_threshold.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.tx_threshold.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.tx_threshold.d),
    .intr_o                 (intr_tx_threshold_o)
  );

  prim_intr_hw #(
    .Width(1),
    .IntrT("Status")
  ) intr_hw_acq_overflow (
    .clk_i,
    .rst_ni,
    .event_intr_i           (~acq_fifo_wready),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.acq_full.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.acq_full.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.acq_full.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.acq_full.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.acq_full.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.acq_full.d),
    .intr_o                 (intr_acq_full_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_unexp_stop (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_unexp_stop),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.unexp_stop.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.unexp_stop.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.unexp_stop.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.unexp_stop.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.unexp_stop.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.unexp_stop.d),
    .intr_o                 (intr_unexp_stop_o)
  );

  prim_intr_hw #(.Width(1)) intr_hw_host_timeout (
    .clk_i,
    .rst_ni,
    .event_intr_i           (event_host_timeout),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.host_timeout.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.host_timeout.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.host_timeout.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.host_timeout.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.host_timeout.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.host_timeout.d),
    .intr_o                 (intr_host_timeout_o)
  );

  // The STATUS CSR is defined as hwext, as most values in it are swaccess: "ro" and
  // simply forward certain internal signals to the register interface.
  // However, the HOST_DISABLED_NACK_TIMEOUT field is flopped, so manually instantiate here.
  prim_subreg #(
    .DW      (1),
    .SwAccess(prim_subreg_pkg::SwAccessRO),
    .RESVAL  (1'h0),
    .Mubi    (1'b0)
  ) u_status_host_disabled_nack_timeout_reg (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),

    // from register interface
    .we     (1'b0),
    .wd     ('0),

    // from internal hardware
    .de     (status_host_disabled_nack_timeout_de),
    .d      (status_host_disabled_nack_timeout_d),

    // to internal hardware
    .qe     (),
    .q      (),
    .ds     (),

    // to register interface (read)
    .qs     (hw2reg.status.host_disabled_nack_timeout.d)
  );
  // Set -> When the 'host_disable' signal is pulsed by the FSM.
  // Clear -> When SW sets ctrl.enablehost to 1'b1.
  assign status_host_disabled_nack_timeout_de =
    host_disable |                                           // Set
    (reg2hw.ctrl.enablehost.qe & reg2hw.ctrl.enablehost.q) ; // Clear
  assign status_host_disabled_nack_timeout_d = host_disable;

  ////////////////
  // ASSERTIONS //
  ////////////////

  `ASSERT_PULSE(HostDisablePulse_A, host_disable)

  `ASSERT_INIT(FifoDepthValid_A, FifoDepth > 0 && FifoDepthW <= MaxFifoDepthW)
  `ASSERT_INIT(AcqFifoDepthValid_A, AcqFifoDepth > 0 && AcqFifoDepthW <= MaxFifoDepthW)

endmodule
