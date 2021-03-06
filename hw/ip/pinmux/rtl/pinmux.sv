// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Pinmux toplevel.
//

`include "prim_assert.sv"

module pinmux
  import pinmux_pkg::*;
  import pinmux_reg_pkg::*;
#(
  // Taget-specific pinmux configuration passed down from the
  // target-specific top-level.
  parameter target_cfg_t TargetCfg = DefaultTargetCfg
) (
  input                            clk_i,
  input                            rst_ni,
  // Slow always-on clock
  input                            clk_aon_i,
  input                            rst_aon_ni,
  // Wakeup request, running on clk_aon_i
  output logic                     aon_wkup_req_o,
  output logic                     usb_wkup_req_o,
  // Sleep enable and strap sample enable
  // from pwrmgr, running on clk_i
  // TODO(#5198): figure out the connections.
  input                            sleep_en_i,
  input                            strap_en_i,
  // LC signals for TAP qualification
  input  lc_ctrl_pkg::lc_tx_t      lc_dft_en_i,
  input  lc_ctrl_pkg::lc_tx_t      lc_hw_debug_en_i,
  // Sampled values for DFT straps
  output dft_strap_test_req_t      dft_strap_test_o,
  // Qualified JTAG signals for TAPs
  output jtag_pkg::jtag_req_t      lc_jtag_o,
  input  jtag_pkg::jtag_rsp_t      lc_jtag_i,
  output jtag_pkg::jtag_req_t      rv_jtag_o,
  input  jtag_pkg::jtag_rsp_t      rv_jtag_i,
  output jtag_pkg::jtag_req_t      dft_jtag_o,
  input  jtag_pkg::jtag_rsp_t      dft_jtag_i,
  // Direct USB connection
  input                            usb_out_of_rst_i,
  input                            usb_aon_wake_en_i,
  input                            usb_aon_wake_ack_i,
  input                            usb_suspend_i,
  output usbdev_pkg::awk_state_t   usb_state_debug_o,
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t        tl_i,
  output tlul_pkg::tl_d2h_t        tl_o,
  // Muxed Peripheral side
  input        [NMioPeriphOut-1:0] periph_to_mio_i,
  input        [NMioPeriphOut-1:0] periph_to_mio_oe_i,
  output logic [NMioPeriphIn-1:0]  mio_to_periph_o,
  // Dedicated Peripheral side
  input        [NDioPads-1:0]      periph_to_dio_i,
  input        [NDioPads-1:0]      periph_to_dio_oe_i,
  output logic [NDioPads-1:0]      dio_to_periph_o,
  // Pad side
  // MIOs
  output logic [NMioPads-1:0][AttrDw-1:0] mio_attr_o,
  output logic [NMioPads-1:0]             mio_out_o,
  output logic [NMioPads-1:0]             mio_oe_o,
  input        [NMioPads-1:0]             mio_in_i,
  // DIOs
  output logic [NDioPads-1:0][AttrDw-1:0] dio_attr_o,
  output logic [NDioPads-1:0]             dio_out_o,
  output logic [NDioPads-1:0]             dio_oe_o,
  input        [NDioPads-1:0]             dio_in_i
);

  //////////////////////////////////
  // Regfile Breakout and Mapping //
  //////////////////////////////////

  pinmux_reg2hw_t reg2hw;
  pinmux_hw2reg_t hw2reg;

  pinmux_reg_top u_reg (
    .clk_i  ,
    .rst_ni ,
    .tl_i   ,
    .tl_o   ,
    .reg2hw ,
    .hw2reg ,
    .intg_err_o(),
    .devmode_i(1'b1)
  );

  /////////////////////////////
  // Pad attribute registers //
  /////////////////////////////

  logic [NDioPads-1:0][AttrDw-1:0] dio_pad_attr_q;
  logic [NMioPads-1:0][AttrDw-1:0] mio_pad_attr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      dio_pad_attr_q <= '0;
      mio_pad_attr_q <= '0;
    end else begin
      // dedicated pads
      for (int kk = 0; kk < NDioPads; kk++) begin
        if (reg2hw.dio_pad_attr[kk].qe) begin
          dio_pad_attr_q[kk] <= reg2hw.dio_pad_attr[kk].q;
        end
      end
      // muxed pads
      for (int kk = 0; kk < NMioPads; kk++) begin
        if (reg2hw.mio_pad_attr[kk].qe) begin
          mio_pad_attr_q[kk] <= reg2hw.mio_pad_attr[kk].q;
        end
      end
    end
  end

  ////////////////////////
  // Connect attributes //
  ////////////////////////

  // TODO(#5221): rework the WARL behavior
  for (genvar k = 0; k < NDioPads; k++) begin : gen_dio_attr
    logic [AttrDw-1:0] warl_mask;
    assign warl_mask = '0;
    assign dio_attr_o[k]            = dio_pad_attr_q[k] & warl_mask;
    assign hw2reg.dio_pad_attr[k].d = dio_pad_attr_q[k] & warl_mask;
  end

  for (genvar k = 0; k < NMioPads; k++) begin : gen_mio_attr
    logic [AttrDw-1:0] warl_mask;
    assign warl_mask = '0;
    assign mio_attr_o[k]            = mio_pad_attr_q[k] & warl_mask;
    assign hw2reg.mio_pad_attr[k].d = mio_pad_attr_q[k] & warl_mask;
  end


  //////////////////////////
  // Strap Sampling Logic //
  //////////////////////////

  // Local versions of the input signals
  logic [NMioPads-1:0] mio_out, mio_oe, mio_in;
  logic [NDioPads-1:0] dio_out, dio_oe, dio_in;

  // This module contains the strap sampling and JTAG mux.
  // Affected inputs are intercepted/tapped before they go to the pinmux
  // matrix. Likewise, affected outputs are intercepted/tapped after the
  // retention registers.
  pinmux_strap_sampling #(
    .TargetCfg (TargetCfg)
  ) u_pinmux_strap_sampling (
    .clk_i,
    .rst_ni,
    // To padring side
    .out_padring_o ( {dio_out_o, mio_out_o} ),
    .oe_padring_o  ( {dio_oe_o , mio_oe_o } ),
    .in_padring_i  ( {dio_in_i , mio_in_i } ),
    // To core side
    .out_core_i    ( {dio_out, mio_out} ),
    .oe_core_i     ( {dio_oe,  mio_oe}  ),
    .in_core_o     ( {dio_in,  mio_in}  ),
    // Strap and JTAG signals
    .strap_en_i,
    .lc_dft_en_i,
    .lc_hw_debug_en_i,
    .dft_strap_test_o,
    .lc_jtag_o,
    .lc_jtag_i,
    .rv_jtag_o,
    .rv_jtag_i,
    .dft_jtag_o,
    .dft_jtag_i
  );

  ///////////////////////////////////////
  // USB wake detect module connection //
  ///////////////////////////////////////

  // Dedicated Peripheral side
  usbdev_aon_wake u_usbdev_aon_wake (
    .clk_aon_i,
    .rst_aon_ni,

    // input signals for resume detection
    .usb_dp_async_alw_i(dio_to_periph_o[UsbDpSel]),
    .usb_dn_async_alw_i(dio_to_periph_o[UsbDnSel]),
    .usb_dppullup_en_alw_i(dio_oe_o[UsbDpPullUpSel]),
    .usb_dnpullup_en_alw_i(dio_oe_o[UsbDnPullUpSel]),

    // tie this to something from usbdev to indicate its out of reset
    .usb_out_of_rst_alw_i(usb_out_of_rst_i),
    .usb_aon_wake_en_upwr_i(usb_aon_wake_en_i),
    .usb_aon_woken_upwr_i(usb_aon_wake_ack_i),
    .usb_suspended_upwr_i(usb_suspend_i),

    // wake/powerup request
    .wake_req_alw_o(usb_wkup_req_o),
    .state_debug_o(usb_state_debug_o)
  );

  /////////////////////////
  // Retention Registers //
  /////////////////////////

  logic sleep_en_q, sleep_trig;

  logic [NMioPads-1:0] mio_sleep_trig;
  logic [NMioPads-1:0] mio_out_retreg_d, mio_oe_retreg_d;
  logic [NMioPads-1:0] mio_out_retreg_q, mio_oe_retreg_q;

  logic [NDioPads-1:0] dio_sleep_trig;
  logic [NDioPads-1:0] dio_out_retreg_d, dio_oe_retreg_d;
  logic [NDioPads-1:0] dio_out_retreg_q, dio_oe_retreg_q;

  // Sleep entry trigger
  assign sleep_trig = sleep_en_i & ~sleep_en_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_sleep
    if (!rst_ni) begin
      sleep_en_q       <= 1'b0;
      mio_out_retreg_q <= '0;
      mio_oe_retreg_q  <= '0;
      dio_out_retreg_q <= '0;
      dio_oe_retreg_q  <= '0;
    end else begin
      sleep_en_q <= sleep_en_i;

      // MIOs
      for (int k = 0; k < NMioPads; k++) begin
        if (mio_sleep_trig[k]) begin
          mio_out_retreg_q[k] <= mio_out_retreg_d[k];
          mio_oe_retreg_q[k]  <= mio_oe_retreg_d[k];
        end
      end

      // DIOs
      for (int k = 0; k < NDioPads; k++) begin
        if (dio_sleep_trig[k]) begin
          dio_out_retreg_q[k] <= dio_out_retreg_d[k];
          dio_oe_retreg_q[k]  <= dio_oe_retreg_d[k];
        end
      end
    end
  end

  /////////////////////
  // MIO Input Muxes //
  /////////////////////

  localparam int AlignedMuxSize = (NMioPads + 2 > NDioPads) ? 2**$clog2(NMioPads + 2) :
                                                              2**$clog2(NDioPads);

  // stack input and default signals for convenient indexing below possible defaults:
  // constant 0 or 1. make sure mux is aligned to a power of 2 to avoid Xes.
  logic [AlignedMuxSize-1:0] mio_mux;
  assign mio_mux = AlignedMuxSize'({mio_in, 1'b1, 1'b0});

  for (genvar k = 0; k < NMioPeriphIn; k++) begin : gen_mio_periph_in
    // index using configured insel
    assign mio_to_periph_o[k] = mio_mux[reg2hw.mio_periph_insel[k].q];
  end

  //////////////////////
  // MIO Output Muxes //
  //////////////////////

  // stack output data/enable and default signals for convenient indexing below
  // possible defaults: 0, 1 or 2 (high-Z). make sure mux is aligned to a power of 2 to avoid Xes.
  logic [2**$clog2(NMioPeriphOut+3)-1:0] periph_data_mux, periph_oe_mux;
  assign periph_data_mux  = $bits(periph_data_mux)'({periph_to_mio_i, 1'b0, 1'b1, 1'b0});
  assign periph_oe_mux    = $bits(periph_oe_mux)'({periph_to_mio_oe_i,  1'b0, 1'b1, 1'b1});

  for (genvar k = 0; k < NMioPads; k++) begin : gen_mio_out
    // Check individual sleep enable status bits
    assign mio_out[k] = reg2hw.mio_pad_sleep_status[k].q ?
                        mio_out_retreg_q[k]              :
                        periph_data_mux[reg2hw.mio_outsel[k].q];

    assign mio_oe[k]  = reg2hw.mio_pad_sleep_status[k].q ?
                        mio_oe_retreg_q[k]               :
                        periph_oe_mux[reg2hw.mio_outsel[k].q];

    // latch state when going to sleep
    // 0: drive low
    // 1: drive high
    // 2: high-z
    // 3: previous value
    assign mio_out_retreg_d[k] = (reg2hw.mio_pad_sleep_mode[k].q == 0) ? 1'b0 :
                                 (reg2hw.mio_pad_sleep_mode[k].q == 1) ? 1'b1 :
                                 (reg2hw.mio_pad_sleep_mode[k].q == 2) ? 1'b0 : mio_out[k];

    assign mio_oe_retreg_d[k] = (reg2hw.mio_pad_sleep_mode[k].q == 0) ? 1'b1 :
                                (reg2hw.mio_pad_sleep_mode[k].q == 1) ? 1'b1 :
                                (reg2hw.mio_pad_sleep_mode[k].q == 2) ? 1'b0 : mio_oe[k];

    // Activate sleep behavior only if it has been enabled
    assign mio_sleep_trig[k] = reg2hw.mio_pad_sleep_en[k].q & sleep_trig;
    assign hw2reg.mio_pad_sleep_status[k].d = 1'b1;
    assign hw2reg.mio_pad_sleep_status[k].de = mio_sleep_trig[k];
  end

  /////////////////////
  // DIO connections //
  /////////////////////

  // Inputs are just fed through
  assign dio_to_periph_o = dio_in;

  for (genvar k = 0; k < NDioPads; k++) begin : gen_dio_out
    // Check individual sleep enable status bits
    assign dio_out[k] = reg2hw.dio_pad_sleep_status[k].q ?
                        dio_out_retreg_q[k]              :
                        periph_to_dio_i[k];

    assign dio_oe[k]  = reg2hw.dio_pad_sleep_status[k].q ?
                        dio_oe_retreg_q[k]               :
                        periph_to_dio_oe_i[k];

    // latch state when going to sleep
    // 0: drive low
    // 1: drive high
    // 2: high-z
    // 3: previous value
    assign dio_out_retreg_d[k] = (reg2hw.dio_pad_sleep_mode[k].q == 0) ? 1'b0 :
                                 (reg2hw.dio_pad_sleep_mode[k].q == 1) ? 1'b1 :
                                 (reg2hw.dio_pad_sleep_mode[k].q == 2) ? 1'b0 : dio_out[k];

    assign dio_oe_retreg_d[k] = (reg2hw.dio_pad_sleep_mode[k].q == 0) ? 1'b1 :
                                (reg2hw.dio_pad_sleep_mode[k].q == 1) ? 1'b1 :
                                (reg2hw.dio_pad_sleep_mode[k].q == 2) ? 1'b0 : dio_oe[k];

    // Activate sleep behavior only if it has been enabled
    assign dio_sleep_trig[k] = reg2hw.dio_pad_sleep_en[k].q & sleep_trig;
    assign hw2reg.dio_pad_sleep_status[k].d = 1'b1;
    assign hw2reg.dio_pad_sleep_status[k].de = dio_sleep_trig[k];
  end

  //////////////////////
  // Wakeup detectors //
  //////////////////////

  // Wakeup detector taps are not affected by JTAG/strap
  // selection mux. I.e., we always sample the unmuxed inputs
  // that come directly from the pads.
  logic [AlignedMuxSize-1:0] dio_wkup_mux;
  logic [AlignedMuxSize-1:0] mio_wkup_mux;
  assign dio_wkup_mux = AlignedMuxSize'(dio_in_i);
  assign mio_wkup_mux = AlignedMuxSize'(mio_in_i);

  logic [NWkupDetect-1:0] aon_wkup_req;
  for (genvar k = 0; k < NWkupDetect; k++) begin : gen_wkup_detect
    logic pin_value;
    assign pin_value = (reg2hw.wkup_detector[k].miodio.q)           ?
                       dio_wkup_mux[reg2hw.wkup_detector_padsel[k]] :
                       mio_wkup_mux[reg2hw.wkup_detector_padsel[k]];

    pinmux_wkup u_pinmux_wkup (
      .clk_i,
      .rst_ni,
      .clk_aon_i,
      .rst_aon_ni,
      // config signals. these are synched to clk_aon internally
      .wkup_en_i          ( reg2hw.wkup_detector_en[k].q                ),
      .filter_en_i        ( reg2hw.wkup_detector[k].filter.q            ),
      .wkup_mode_i        ( wkup_mode_e'(reg2hw.wkup_detector[k].mode.q)),
      .wkup_cnt_th_i      ( reg2hw.wkup_detector_cnt_th[k].q            ),
      .pin_value_i        ( pin_value                                   ),
      // cause reg signals. these are synched from/to clk_aon internally
      .wkup_cause_valid_i ( reg2hw.wkup_cause[k].qe                     ),
      .wkup_cause_data_i  ( reg2hw.wkup_cause[k].q                      ),
      .wkup_cause_data_o  ( hw2reg.wkup_cause[k].d                      ),
      // wakeup request signals on clk_aon (level encoded)
      .aon_wkup_req_o     ( aon_wkup_req[k]                             )
    );
  end

  // OR' together all wakeup requests
  assign aon_wkup_req_o = |aon_wkup_req;

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  // `ASSERT_KNOWN(MioToPeriphKnownO_A, mio_to_periph_o)
  `ASSERT_KNOWN(MioOeKnownO_A, mio_oe_o)
  // `ASSERT_KNOWN(DioToPeriphKnownO_A, dio_to_periph_o)
  `ASSERT_KNOWN(DioOeKnownO_A, dio_oe_o)

  // TODO: need to check why some outputs are not valid (e.g. SPI device SDO)
  // for (genvar k = 0; k < NMioPads; k++) begin : gen_mio_known_if
  //   `ASSERT_KNOWN_IF(MioOutKnownO_A, mio_out_o[k], mio_oe_o[k])
  // end

  // for (genvar k = 0; k < NDioPads; k++) begin : gen_dio_known_if
  //   `ASSERT_KNOWN_IF(DioOutKnownO_A, dio_out_o[k], dio_oe_o[k])
  // end

  `ASSERT_KNOWN(MioKnownO_A, mio_attr_o)
  `ASSERT_KNOWN(DioKnownO_A, dio_attr_o)

  `ASSERT_KNOWN(LcJtagTckKnown_A, lc_jtag_o.tck)
  `ASSERT_KNOWN(LcJtagTrstKnown_A, lc_jtag_o.trst_n)
  `ASSERT_KNOWN(LcJtagTmsKnown_A, lc_jtag_o.tms)

  `ASSERT_KNOWN(RvJtagTckKnown_A, rv_jtag_o.tck)
  `ASSERT_KNOWN(RvJtagTrstKnown_A, rv_jtag_o.trst_n)
  `ASSERT_KNOWN(RvJtagTmsKnown_A, rv_jtag_o.tms)

  `ASSERT_KNOWN(DftJtagTckKnown_A, dft_jtag_o.tck)
  `ASSERT_KNOWN(DftJtagTrstKnown_A, dft_jtag_o.trst_n)
  `ASSERT_KNOWN(DftJtagTmsKnown_A, dft_jtag_o.tms)

  `ASSERT_KNOWN(DftStrapsKnown_A, dft_strap_test_o)

  // running on slow AON clock
  `ASSERT_KNOWN(AonWkupReqKnownO_A, aon_wkup_req_o, clk_aon_i, !rst_aon_ni)

endmodule : pinmux
