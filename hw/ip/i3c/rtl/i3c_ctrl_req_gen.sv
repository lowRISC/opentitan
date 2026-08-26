// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Combinational module that constructs the requests from the Controller Core to the transceiver.

module i3c_ctrl_req_gen
  import i3c_controller_pkg::*;
  import i3c_ctrl_ccc_pkg::*;
  import i3c_pkg::*;
  import i3c_reg_pkg::*;
#(
  parameter int unsigned ClkFreq   = 50_000_000,
  parameter int unsigned DataWidth = 32
) (
  // Configuration.
  input i3c_reg2hw_t          reg2hw_i,
  input                       use_bcst_addr_i,

  // The current FSM state.
  input i3c_ctrl_fsm_state_e  state_i,

  // Information about the current Command Descriptor and transfer.
  input i3c_ctrl_cmd_state_t  cmd_state_i,
  input i3c_ctrl_cmd_attrs_t  cmd_attrs_i,
  input i3c_dat_mem_t         dat_entry_i,
  input                       i3c_first_i,

  // Data transmission.
  input       [DataWidth-1:0] tx_data_i,
  input                       data_last_i,
  input                 [1:0] dlen_i,

  // Response from the CCC handling logic.
  input i3c_ctrl_ccc_rsp_t    ccc_rsp_i,

  // Timing parameters; target- and transfer-invariant.
  output         [TmCycW-1:0] tcas_d2_o,
  output         [TmCycW-1:0] tcbp_d2_o,
  output         [TmCycW-1:0] todch_d2_o,
  output         [TmCycW-1:0] todcl_d2_o,

  // Using I3C Broadcast Address?
  output                      addr_bcst_o,
  // Request to the transceiver logic.
  output                      trx_dvalid_o,
  output i3c_ctrl_trx_req_t   trx_dreq_o
);

  import i3c_consts_pkg::*;
  import i3c_timing_pkg::*;

  // Two parameters specify the signaling mode, and thus the timing parameters.
  i3c_xfer_mode_e mode;
  logic i2c;  // This disambiguates `mode` because it is overloaded.
  always_comb begin
    // The timing for the body of the transfer comes from the command attributes which is typically
    // informed by the DAT entry for the Target/Group, but some FSM states need to control it
    // explicitly, e.g. fetching of an In-Band Interrupt payload.
    mode = cmd_attrs_i.mode;
    i2c  = cmd_attrs_i.i2c;
    case (state_i)
      // HDR Exit/Restart signaling.
      ExitHDR,
      ReStHDR: begin
        mode = XferMode_HDRDDR;
        i2c  = 1'b0;
      end

      // Arbitrable Address Header, i.e. following a Start,
      CmdArb: begin
        mode = i3c_xfer_mode_e'(XferMode_I2CFM);
        i2c  = 1'b1;
      end

      CmdAddr,          // Address Header, following Repeated Start.
      EnterDDR,         // HDR-DDR entry.
      IBIRxData,        // IBI Payload Reception.
      CCC,              // Common Command Code handling.
      DirectDrv: begin  // Software direct-driving of pins.
        mode = XferMode_SDR0;
        i2c  = 1'b0;
      end

      default: begin end  // Nothing to do; not all FSM states need to modify the signaling speed.
    endcase
  end

  // Speed index for the current command.
  // - a single software-programmed value is used for SDR1-SDR4, but scaled accordingly.
  logic [2:0] sn;
  always_comb begin
    case ({i2c, mode})
      // I2C signaling modes.
      {1'b1, XferMode_I2CUDR3},
      {1'b1, XferMode_I2CUDR2},
      {1'b1, XferMode_I2CUDR1},
      {1'b1, XferMode_I2CFM}:     sn = 3'b110;
      {1'b1, XferMode_I2CFMPlus}: sn = 3'b101;
      // Supported SDR/HDR signaling modes.
      {1'b0, XferMode_SDR4}:      sn = 3'b100;
      {1'b0, XferMode_SDR3}:      sn = 3'b011;
      {1'b0, XferMode_SDR2}:      sn = 3'b010;
      {1'b0, XferMode_SDR1}:      sn = 3'b001;
      // The default timing covers SDR0 and HDR-DDR.
      default:                    sn = 3'b000;
    endcase
  end

  // ----- Default hardware-calculated timing parameters. -----
  //
  // Note that these timing parameters are expressed such that synthesis should reduce the complex
  // calculations to simple constants from which we select based on the current mode.
  // This is important because the logic is really quite involved but ultimately dependent only
  // upon constant values, particularly the clock frequency (ClkFreq).

  wire [TmCycW-1:0] hw_tcas_d2  = tm_cycles_init(ClkFreq, ceil_div(TCAS, 2));
  wire [TmCycW-1:0] hw_tcbp_d2  = tm_cycles_init(ClkFreq, ceil_div(TCBP, 2));
  wire [TmCycW-1:0] hw_todch_d2 = tm_cycles_init(ClkFreq, ceil_div(TDIGH, 2));
  wire [TmCycW-1:0] hw_todcl_d2 = tm_cycles_init(ClkFreq, ceil_div(TLOW_OD, 2));

  // Hardware-calculated default timing parameters for the various modes.
  tm_params_t tmhw_sdr0, tmhw_sdr1, tmhw_sdr2, tmhw_sdr3, tmhw_sdr4, tmhw_fmp, tmhw_fm;
  // SDR signaling.
  assign tmhw_sdr0 = tm_params(ClkFreq, TDIGH, TPERIOD_SDR0);  // Also HDR-DDR.
  assign tmhw_sdr1 = tm_params(ClkFreq, TDIGH, TPERIOD_SDR1);
  assign tmhw_sdr2 = tm_params(ClkFreq, TDIGH, TPERIOD_SDR2);
  assign tmhw_sdr3 = tm_params(ClkFreq, TDIGH, TPERIOD_SDR3);
  assign tmhw_sdr4 = tm_params(ClkFreq, TDIGH, TPERIOD_SDR4);
  // I2C signaling.
  assign tmhw_fmp  = tm_params(ClkFreq, TDIGH_FMP, TPERIOD_FMP);
  assign tmhw_fm   = tm_params(ClkFreq, TDIGH_FM,  TPERIOD_FM);

  // Hardware-calculated default timing parameters for the current mode.
  tm_params_t tm_hw;
  assign tm_hw = {tmhw_fm, tmhw_fmp, tmhw_sdr4, tmhw_sdr3, tmhw_sdr2, tmhw_sdr1, tmhw_sdr0} >>
                 (sn * $bits(tm_params_t));

  // ----- Software-programmed timing parameters. -----

  wire [TmCycW-1:0] sw_tcas_d2  = reg2hw_i.ctrl_time_sp.tcas_div2.q;
  wire [TmCycW-1:0] sw_tcbp_d2  = reg2hw_i.ctrl_time_sp.tcbp_div2.q;
  wire [TmCycW-1:0] sw_todch_d2 = reg2hw_i.ctrl_time_od.sclhi_div2.q;
  wire [TmCycW-1:0] sw_todcl_d2 = reg2hw_i.ctrl_time_od.scllo_div2.q;

  // Collect the potential software override values from the register API.
  // - nomenclature: tcls - time Clock Lo Setup (i.e. before rising edge).
  //                 tchh - time Clock Hi Hold (i.e. after rising edge).
  tm_params_t tmsw_sdr0, tmsw_sdr1, tmsw_sdr2, tmsw_sdr3, tmsw_sdr4, tmsw_fmp, tmsw_fm;
  // Programmed timings for push-pull SCL high.
  // - this is the same for all SDR modes and HDR-DDR, to be suppressed by I2C spike filters.
  assign tmsw_sdr0.tchh  = reg2hw_i.ctrl_time_pp.tchh.q;
  assign tmsw_sdr0.tchs  = reg2hw_i.ctrl_time_pp.tchs.q;
  assign tmsw_sdr0.hcext = reg2hw_i.ctrl_time_pp.hcext.q;
  assign tmsw_sdr1.tchh  = reg2hw_i.ctrl_time_pp.tchh.q;
  assign tmsw_sdr1.tchs  = reg2hw_i.ctrl_time_pp.tchs.q;
  assign tmsw_sdr1.hcext = reg2hw_i.ctrl_time_pp.hcext.q;
  assign tmsw_sdr2.tchh  = reg2hw_i.ctrl_time_pp.tchh.q;
  assign tmsw_sdr2.tchs  = reg2hw_i.ctrl_time_pp.tchs.q;
  assign tmsw_sdr2.hcext = reg2hw_i.ctrl_time_pp.hcext.q;
  assign tmsw_sdr3.tchh  = reg2hw_i.ctrl_time_pp.tchh.q;
  assign tmsw_sdr3.tchs  = reg2hw_i.ctrl_time_pp.tchs.q;
  assign tmsw_sdr3.hcext = reg2hw_i.ctrl_time_pp.hcext.q;
  assign tmsw_sdr4.tchh  = reg2hw_i.ctrl_time_pp.tchh.q;
  assign tmsw_sdr4.tchs  = reg2hw_i.ctrl_time_pp.tchs.q;
  assign tmsw_sdr4.hcext = reg2hw_i.ctrl_time_pp.hcext.q;

  // Programed timings for SDR0 SCL low.
  assign tmsw_sdr0.tcls = reg2hw_i.ctrl_time_sdr0.tcls.q;
  assign tmsw_sdr0.tclh = reg2hw_i.ctrl_time_sdr0.tclh.q;
  // Programmed timings for SDR1 SCL low.
  assign tmsw_sdr1.tcls = reg2hw_i.ctrl_time_sdr1.tcls.q;
  assign tmsw_sdr1.tclh = reg2hw_i.ctrl_time_sdr1.tclh.q;
  // Programmed timings for SDR2 SCL low.
  assign tmsw_sdr2.tcls = reg2hw_i.ctrl_time_sdr2.tcls.q;
  assign tmsw_sdr2.tclh = reg2hw_i.ctrl_time_sdr2.tclh.q;
  // Programmed timings for SDR3 SCL low.
  assign tmsw_sdr3.tcls = reg2hw_i.ctrl_time_sdr3.tcls.q;
  assign tmsw_sdr3.tclh = reg2hw_i.ctrl_time_sdr3.tclh.q;
  // Programmed timings for SDR4 SCL low.
  assign tmsw_sdr4.tcls = reg2hw_i.ctrl_time_sdr4.tcls.q;
  assign tmsw_sdr4.tclh = reg2hw_i.ctrl_time_sdr4.tclh.q;
  // Programmed timings for I2C Fast Mode Plus.
  assign tmsw_fmp.tcls  = reg2hw_i.ctrl_time_fmp.scllo_div2.q;
  assign tmsw_fmp.tchh  = reg2hw_i.ctrl_time_fmp.sclhi_div2.q;
  assign tmsw_fmp.tchs  = reg2hw_i.ctrl_time_fmp.sclhi_div2.q;
  assign tmsw_fmp.hcext = 1'b0;
  assign tmsw_fmp.tclh  = reg2hw_i.ctrl_time_fmp.scllo_div2.q;
  // Programmed timing for I2C Fast Mode.
  assign tmsw_fm.tcls  = reg2hw_i.ctrl_time_fm.scllo_div2.q;
  assign tmsw_fm.tchh  = reg2hw_i.ctrl_time_fm.sclhi_div2.q;
  assign tmsw_fm.tchs  = reg2hw_i.ctrl_time_fm.sclhi_div2.q;
  assign tmsw_fm.hcext = 1'b0;
  assign tmsw_fm.tclh  = reg2hw_i.ctrl_time_fm.scllo_div2.q;

  // Software-programmed default timing parameters for the current mode.
  tm_params_t tm_sw;
  assign tm_sw = {tmsw_fm, tmsw_fmp, tmsw_sdr4, tmsw_sdr3, tmsw_sdr2, tmsw_sdr1, tmsw_sdr0} >>
                 (sn * $bits(tm_params_t));

  // ----- Choose between hardware and software candidates. -----
  // Start/stoP timings.
  assign tcas_d2_o = &sw_tcas_d2 ? hw_tcas_d2[TmCycW-1:0] : sw_tcas_d2;
  assign tcbp_d2_o = &sw_tcbp_d2 ? hw_tcbp_d2[TmCycW-1:0] : sw_tcbp_d2;
  // Open drain timings; target- and transfer-invariant.
  assign todch_d2_o = &sw_todch_d2 ? hw_todch_d2[TmCycW-1:0] : sw_todch_d2;
  assign todcl_d2_o = &sw_todcl_d2 ? hw_todcl_d2[TmCycW-1:0] : sw_todcl_d2;

  // Push-pull timings; transfer-dependent.
  i3c_ctrl_timing_t tm_sel;
  assign tm_sel.tcls   = &tm_sw.tcls ? tm_hw.tcls  : tm_sw.tcls;
  assign tm_sel.tchh   = &tm_sw.tchh ? tm_hw.tchh  : tm_sw.tchh;
  assign tm_sel.tchs   = &tm_sw.tchs ? tm_hw.tchs  : tm_sw.tchs;
  assign tm_sel.hcext  = &tm_sw.tchs ? tm_hw.hcext : tm_sw.hcext;
  assign tm_sel.tclh   = &tm_sw.tclh ? tm_hw.tclh  : tm_sw.tclh;

  // Using I3C Broadcast Address to commence a transfer?
  // TODO: Address Assignment Command Descriptors involve multiple CCC segments; only the first
  //       shall use the I3C Broadcast Address.
  assign addr_bcst_o = |{cmd_attrs_i.is_ccc, cmd_attrs_i.ddr, use_bcst_addr_i};

  // Target address as request write data (CmdArb or CmdAddr).
  logic [DataWidth-1:0] addr_wdata;
  always_comb begin : gen_addr_wdata
    // Present the Broadcast/Target/Group address in the upper 7 bits.
    /// - I3C Broadcast address is used for SDR Private Transfers iff explicitly requested.
    addr_wdata = {dat_entry_i.dynamic_address[22:16], cmd_attrs_i.rnw} << (DataWidth - 8);
    if (addr_bcst_o) begin
      addr_wdata = Addr_Broadcast << (DataWidth - 7);
    // SETDASA is always sent to the programmed static address, and this is all I2C devices have.
    end else if (cmd_attrs_i.ccc == SETDASA || cmd_attrs_i.i2c) begin  // HCI 6.3.1
      addr_wdata = {dat_entry_i.static_address, cmd_attrs_i.rnw} << (DataWidth - 8);
    end
  end

  // TODO: Perhaps it would be more compact to list the states that do not send a request?
  assign trx_dvalid_o = |{state_i inside {StartSDR, StopSDR, RepStSDR,
                                          EnterDDR, ExitHDR, ReStHDR,
                                          CmdArb, CmdAddr,
                                          CmdWord,
                                          TxData, TxCRC,  // Transmit data.
                                          RxData, RxCRC,  // Request data reception.
                                          IBIRxData,
                                          TargRst,
                                          DirectDrv},     // Direct-driving of pins.
                         // Forward transceiver requests from the CCC handling.
                         (state_i == CCC) & ccc_rsp_i.req_dvalid};

  always_comb begin : gen_trx_req
    // Note: in particular, this initialization zeroes `len` for many requests, preventing the
    // transceiver logic from treating it as a 'multi-unit' request.
    trx_dreq_o = '0;
    // Only data transfer really needs to modify this field, based on the data length.
    trx_dreq_o.last = 1'b1;
    case (state_i)
      // SDR Bus State signaling.
      StartSDR: trx_dreq_o.req = CReqType_SDRStart;
      StopSDR:  trx_dreq_o.req = CReqType_SDRStop;
      RepStSDR: trx_dreq_o.req = CReqType_SDRRepStart;

      // HDR Exit signaling.
      ExitHDR: trx_dreq_o.req = CReqType_HDRExit;
      // HDR Restart signaling.
      ReStHDR: trx_dreq_o.req = CReqType_HDRRestart;

      // Arbitrable Address Header, i.e. following a Start.
      CmdArb: begin
        trx_dreq_o.req = CReqType_ArbAddr;
        if (cmd_state_i.available) begin
          trx_dreq_o.wdata = addr_wdata;
        end else begin
          // Start request from Target; drive out all '1's so that we will lose the arbitration.
          trx_dreq_o.wdata = 9'h1ff << (DataWidth - 9);
        end
      end

      // Address Header, following Repeated Start.
      CmdAddr: begin
        trx_dreq_o.req = CReqType_Address;
        trx_dreq_o.wdata = addr_wdata;
      end

      // HDR-DDR entry.
      EnterDDR: begin
        trx_dreq_o.req = CReqType_SDRBytes;
        trx_dreq_o.wdata = ENTHDR0 << (DataWidth - 8);
        trx_dreq_o.len   = 0;  // A single byte switches the bus into HDR-DDR mode.
      end

      // HDR-DDR transfer.
      CmdWord: begin
        trx_dreq_o.req = CReqType_CommandWord;
        trx_dreq_o.wdata = {// Upper bit of `CMD` field ignored in HDR-DDR.
                            cmd_attrs_i.rnw, cmd_attrs_i.ccc[6:0],
                            dat_entry_i.dynamic_address[22:16],  // Target Address/Group.
                            1'b0,  // Transceiver completes the Parity Adjustment bit.
                            16'b0};
        // Send only a single Command Word.
        trx_dreq_o.len  = 2'b00;
      end

      // Transmission (SDR or HDR-DDR).
      TxData: begin
        trx_dreq_o.req = cmd_attrs_i.ddr ? CReqType_DataWord : CReqType_SDRBytes;
        trx_dreq_o.len   = dlen_i;
        trx_dreq_o.wdata = tx_data_i;
        trx_dreq_o.last  = data_last_i;
      end
      // HDR-DDR CRC Word at the end of a Write.
      TxCRC: begin
        trx_dreq_o.req = CReqType_CRCWord;
        // 4'hC token indicating a valid CRC word, and the final bit of the 10-bit
        // payload is set in preparation for HDR Restart/Exit; Figure 105.
        // The CRC-5 injection is handled by the Transceiver logic.
        trx_dreq_o.wdata = 32'hc040_0000;  // 4'hC token and '1' bit bracket CRC-5.
        trx_dreq_o.len   = 2'b00;
      end

      // Reception (SDR or HDR-DDR).
      //
      // Note that RxData is requesting that the Transceiver logic perform read operations, and
      // progress is blocked upon the request being accepted, but it is _not_ waiting for the
      // response. This allows the current response and the next request to be overlapped,
      // achieving better utilization.
      RxData: begin
        trx_dreq_o.req = cmd_attrs_i.ddr ? CReqType_DataWord : CReqType_SDRBytes;
        trx_dreq_o.len   = dlen_i;
        trx_dreq_o.rx    = 1'b1;
        trx_dreq_o.last  = data_last_i;
      end
      // HDR-DDR CRC Word at the end of a Read.
      RxCRC: begin
        trx_dreq_o.req = CReqType_CRCWord;
        trx_dreq_o.rx    = 1'b1;
        trx_dreq_o.len   = 2'b00;
      end

      // IBI Payload Reception.
      IBIRxData: begin
        trx_dreq_o.req = CReqType_SDRBytes;
        trx_dreq_o.len   = 2'b11;
        trx_dreq_o.rx    = 1'b1;
        trx_dreq_o.last  = 1'b0;
      end

      // Common Command Code handling.
      CCC: begin
        // Forward all requests to the transceiver.
        trx_dreq_o.req   = ccc_rsp_i.req_type;
        trx_dreq_o.rx    = ccc_rsp_i.req_rx;
        trx_dreq_o.len   = ccc_rsp_i.req_len;
        trx_dreq_o.wdata = ccc_rsp_i.req_wdata;
        trx_dreq_o.last  = ccc_rsp_i.req_last;
      end

      // Target Reset operations.
      TargRst: trx_dreq_o.req = CReqType_TargetReset;

      // Software direct-driving of pins.
      DirectDrv: begin
        trx_dreq_o.req = CReqType_DirectDrive;
        // Send the new pin state to the transceiver, ordering the bits to simplify its logic
        // slightly.
        trx_dreq_o.wdata = {reg2hw_i.phy_config.ctrl_sda,       reg2hw_i.phy_config.ctrl_sda_pu_en,
                            reg2hw_i.phy_config.ctrl_sda_od_en, reg2hw_i.phy_config.ctrl_sda_pp_en,
                            reg2hw_i.phy_config.ctrl_scl,       reg2hw_i.phy_config.ctrl_scl_pu_en,
                            1'b0,                               reg2hw_i.phy_config.ctrl_scl_pp_en,
                            24'b0};
      end
      default: begin end  // Nothing to do; not all FSM states generate requests.
    endcase

    // Send the selected timing parameters to the transceiver as part of the request.
    trx_dreq_o.tm = tm_sel;
    // Indicates whether we have not yet sent an I3C Broadcast Address successfully.
    // - until such an address is ACKed, transmission occurs using slower signaling so that I3C
    //   devices fitted with enabled spike filters may still see I3C traffic.
    trx_dreq_o.i3c_first = i3c_first_i;
  end

endmodule
