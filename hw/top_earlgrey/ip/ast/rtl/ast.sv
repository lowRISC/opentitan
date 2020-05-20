// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This AST module can be developed without any dependencies on the lowrisc respositories,
// therefore it is self contained and does not reference any packages or other modules from the
// open source repository.

module ast #(
  parameter int NumIoRails      = 1,
  parameter int EntropyStreams  = 4,
  parameter int AdcChannels     = 4,
  parameter int AdcDataWidth    = 10,
  parameter int EntropyInWidth  = 1,          // TBD
  parameter int Ast2PadOutWidth = 16,         // TBD
  parameter int Pad2AstInWidth  = 16,         // TBD
  parameter int UsbCalibWidth   = 16          // TBD
) (
  // Power and IO pin connections
  // TBD

  // ast bus interface and sync clocks / rests
  input clk_ast_io_i,                         // Buffered AST IO Clock
  input clk_ast_sys_i,                        // Buffered AST SYS Clock
  input clk_ast_usb_i,                        // Buffered AST USB Clock
  input clk_ast_aon_i,                        // Buffered AST AON Clock
  input rst_ast_io_ni,                        // Buffered AST IO Reset
  input rst_ast_sys_ni,                       // Buffered AST SYS Reset
  input rst_ast_usb_ni,                       // Buffered AST USB Reset
  input rst_ast_aon_ni,                       // Buffered AST AON Reset

  // tlul if
  input  tlul_pkg::tl_h2d_t tl_i,             // TLUL H2D
  output tlul_pkg::tl_d2h_t tl_o,             // TLUL D2H

  // power related
  input por_ni,                               // Power ON Reset
  output logic vcc_pok_o,                     // VCC Power OK
  output logic main_pok_o,                    // MAIN Power OK
  output logic aon_pok_o,                     // AON Power OK
  output logic [NumIoRails-1:0] io_pok_o,     // IO Rails Power OK
  input main_pd_ni,                           // MAIN Power Down
  input main_iso_en_i,                        // MAIN Isolation Enable

  // power OK control (for debug only). pok signal follows these inputs
  input vcc_supp_i,                           // VCC Supply Test
  input main_supp_i,                          // MAIN Supply Test
  input aon_supp_i,                           // AON Supply Test
  input [NumIoRails-1:0] io_supp_i,           // IO Rails Supply Test

  // output clocks and associated controls
  output logic clk_src_sys_o,                 // SYS Source Clock
  output logic clk_src_sys_val_o,             // SYS Source Clock Valid
  input clk_src_sys_en_i,                     // SYS Source Clock Enable
  input clk_src_sys_jen_i,                    // SYS Source Clock Jitter Enable

  output logic clk_src_aon_o,                 // AON Source Clock
  output logic clk_src_aon_val_o,             // AON Source Clock Valid
  input clk_src_aon_en_i,                     // AON Source Clock Enable

  output logic clk_src_usb_o,                 // USB Source Clock
  output logic clk_src_usb_val_o,             // USB Source Clock Valid
  input clk_src_usb_en_i,                     // USB Source Clock Enable

  output logic clk_src_io_o,                  // IO Source Clock
  output logic clk_src_io_val_o,              // IO Source Clock Valid
  input clk_src_io_en_i,                      // IO Source Clock Enable

  // input clock and references for calibration
  input clk_ast_ext_i,                        // AST External Clock
  input usb_ref_pulse_i,                      // USB Reference Pulse
  input usb_ref_val_i,                        // USB Reference Valid

  // adc interface
  input [AdcChannels-1:0] adc_ai,             // ADC Analog (per channel)
  input [AdcChannels-1:0] adc_chnsel_i,       // ADC Channel Select
  input adc_pd_i,                             // ADC Power Down
  output [AdcDataWidth-1:0] adc_d_o,          // ADC Digital (per channel)
  output adc_d_val_o,                         // ADC Digital Valid

  // entropy source interface
  input rng_en_i,                             // RNG Enable
  output logic rng_ok_o,                      // RNG OK
  output logic [EntropyStreams-1:0] rng_b_o,  // RNG Bit(s)

  // entropy distribution interface
  output logic entropy_req_o,                 // Entropy Request
  input entropy_ack_i,                        // Entropy Acknowlage
  input [EntropyInWidth-1:0] entropy_i,       // Entropy

  // alerts
  output logic as_alert_po,                   // AS Alert Positive
  output logic as_alert_no,                   // AS Alert Negative
  output logic cg_alert_po,                   // CG Alert Positive
  output logic cg_alert_no,                   // CG Alert Negative
  output logic gd_alert_po,                   // GD Alert Positive
  output logic gd_alert_no,                   // GD Alert Negative
  output logic ts_alert_hi_po,                // TS High Alert Positive
  output logic ts_alert_hi_no,                // TS High Alert Negative
  output logic ts_alert_lo_po,                // TS Low Alert Positive
  output logic ts_alert_lo_no,                // TS Low Alert Negative
  output logic ls_alert_po,                   // LS Alert Positive
  output logic ls_alert_no,                   // LS Alert Negative
  output logic ot_alert_po,                   // OT Alert Positive
  output logic ot_alert_no,                   // OT Alert Negative

  input as_alert_ack_i,                       // AS Alert Acknowlage
  input cg_alert_ack_i,                       // CG Alert Acknowlage
  input gd_alert_ack_i,                       // GD Alert Acknowlage
  input ts_alert_hi_ack_i,                    // TS High Alert Acknowlage
  input ts_alert_lo_ack_i,                    // TS Low Alert Acknowlage
  input ls_alert_ack_i,                       // LS Alert Acknowlage
  input ot_alert_ack_i,                       // OT Alert Acknowlage

  input as_alert_trig_i,                      // AS Alert Trigger
  input cg_alert_trig_i,                      // CG Alert Trigger
  input gd_alert_trig_i,                      // GD Alert Trigger
  input ts_alert_hi_trig_i,                   // TS High Alert Trigger
  input ts_alert_lo_trig_i,                   // TS Low Alert Trigger
  input ls_alert_trig_i,                      // LS Alert Trigger
  input ot_alert_trig_i,                      // OT Alert Trigger

  // flash related
  output logic flash_power_down_h_o,          // Flash Power Down
  output logic flash_power_ready_h_o,         // Flash Power Ready

  // pad mux related - DFT
  output logic [Ast2PadOutWidth-1:0] ast2padmux_o,  // DFT_2_IO Output Signals
  input [Pad2AstInWidth-1:0] padmux2ast_i,          // IO_2_DFT Input Signals

  // usb IO calib
  output logic [UsbCalibWidth-1:0] usb_io_pu_cal_o  // USB IO Pull-up Calibration Setting
);

  /////////////////////////////////
  // Reset and power related
  /////////////////////////////////

  // emulates regulator power up sequence
  // aon powers up after vcc
  always_ff @(posedge clk_ast_ext_i or negedge por_ni) begin
    if (!por_ni) begin
      vcc_pok_o <= 1'b0;
      aon_pok_o <= 1'b0;
    end else begin
      vcc_pok_o <= 1'b1;
      aon_pok_o <= vcc_pok_o;
    end
  end

  // blind assumption that these power up at the same time
  // The model should be changed to detect VIO inputs
  assign io_pok_o = {NumIoRails{vcc_pok_o}};

  // main power domain power up
  always_ff @(posedge clk_ast_ext_i or negedge por_ni) begin
    if (!por_ni) begin
      main_pok_o <= 1'b0;
    end else if (main_pd_ni) begin
      main_pok_o <= 1'b1;
    end
  end

  /////////////////////////////////
  // Clocking
  /////////////////////////////////

  // The clocking story can be complicated depending on how we view AST's place in
  // DV, verilator and FPGA.
  // If this module intends to work in all 3:
  // For DV, the clk_rst_if functions will need to be relocated here.
  // For FPGA, the clkgen module would need to be placed here.
  // For verilator, since it only supports 1 domain right now , the story can be significantly
  // simplified.
  //
  // For now, as a giant hack, this module temporarily routes the input clock back out for the
  // system to use.  This is NOT how it is meant to work, the clocks should be generated here.
  assign clk_src_sys_o  = clk_ast_ext_i;
  assign clk_src_usb_o  = clk_ast_ext_i;
  assign clk_src_io_o   = clk_ast_ext_i;
  assign clk_src_aon_o  = clk_ast_ext_i;
  assign clk_src_aon_val_o = 1'b1;

  always_ff @(posedge clk_ast_ext_i or negedge por_ni) begin
    if (!por_ni) begin
      clk_src_sys_val_o <= 1'b0;
      clk_src_usb_val_o <= 1'b0;
      clk_src_io_val_o  <= 1'b0;
    end else begin
      clk_src_sys_val_o <= clk_src_sys_en_i;
      clk_src_usb_val_o <= clk_src_usb_en_i;
      clk_src_io_val_o  <= clk_src_io_en_i;
    end
  end

  /////////////////////////////////
  // ADC
  /////////////////////////////////

  assign adc_d_o = '0;
  assign adc_d_val_o = '0;

  /////////////////////////////////
  // Entropy
  /////////////////////////////////

  assign rng_ok_o = rng_en_i;
  assign rng_b_o = '0;

  /////////////////////////////////
  // Alerts
  /////////////////////////////////

  localparam int NumAlerts = 7;
  logic [NumAlerts-1:0] alert_q;
  logic [NumAlerts-1:0] alert_ack;
  logic [NumAlerts-1:0] alert_trig;

  // this is the clock / reset that sensor control operates
  always_ff @(posedge clk_ast_io_i or negedge rst_ast_io_ni) begin
    if (!rst_ast_io_ni) begin
      alert_q <= '0;
    end else begin
      for (int unsigned i=0; i < NumAlerts; i++) begin
        if (alert_q[i] && alert_ack[i]) begin
          alert_q[i] <= 1'b0;
        end else if (alert_trig[i]) begin
          alert_q[i] <= 1'b1;
        end
      end
    end
  end

  assign alert_trig = {
                       as_alert_trig_i,
                       cg_alert_trig_i,
                       gd_alert_trig_i,
                       ts_alert_hi_trig_i,
                       ts_alert_lo_trig_i,
                       ls_alert_trig_i,
                       ot_alert_trig_i
                      };

  assign alert_ack  = {
                       as_alert_ack_i,
                       cg_alert_ack_i,
                       gd_alert_ack_i,
                       ts_alert_hi_ack_i,
                       ts_alert_lo_ack_i,
                       ls_alert_ack_i,
                       ot_alert_ack_i
                      };

  assign as_alert_po    =  alert_q[6];
  assign as_alert_no    = ~alert_q[6];
  assign cg_alert_po    =  alert_q[5];
  assign cg_alert_no    = ~alert_q[5];
  assign gd_alert_po    =  alert_q[4];
  assign gd_alert_no    = ~alert_q[4];
  assign ts_alert_hi_po =  alert_q[3];
  assign ts_alert_hi_no = ~alert_q[3];
  assign ts_alert_lo_po =  alert_q[2];
  assign ts_alert_lo_no = ~alert_q[2];
  assign ls_alert_po    =  alert_q[1];
  assign ls_alert_no    = ~alert_q[1];
  assign ot_alert_po    =  alert_q[0];
  assign ot_alert_no    = ~alert_q[0];

  // bus assignments
  assign tl_o = '{
      d_valid  : '0,
      d_opcode : tlul_pkg::AccessAck,
      d_param  : '0,
      d_size   : '0,
      d_source : '0,
      d_sink   : '0,
      d_data   : '0,
      d_user   : '0,
      d_error  : '0,
      a_ready  : 1'b1
  };

endmodule // ast
