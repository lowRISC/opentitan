// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: rglts_pdm_3p3v
// *Module Description: Regulators (MAIN & AON) & PDM Logic @3.3V
//############################################################################

`include "prim_assert.sv"

module rglts_pdm_3p3v (
  input vcc_pok_h_i,                       // VCC Exist @3.3v
  input vcaon_pok_por_h_i,                 // VCAON_POK_POR @1.1v
  input vcmain_pok_por_h_i,                // VCMAIN_POK_POR @1.1v
  input [2-1:0] vio_pok_h_i,               // vioa/b_pok signals @1.1v
  input clk_src_aon_h_i,                   // AON Clock @1.1v
  input main_pd_h_i,                       // MAIN Regulator Power Down @1.1v
  input por_sync_h_i,                      // POR (Sync to AON clock) @1.1v
  input scan_mode_h_i,                     // Scan Mode @1.1v
  input [2-1:0] otp_power_seq_h_i,         // MMR0,24 in @1.1v
  input vcaon_supp_i,                      //
  input vcmain_supp_i,                     //
  output logic rglssm_vmppr_h_o,           // Regulators SM at VMPPR (vcmaim_pok_por_reset) @3.3v
  output logic rglssm_vcmon_h_o,           // Regulators state machine at VCMON @3.3v
  output logic rglssm_brout_h_o,           // Regulators state machine at BROUT @3.3v
  output logic vcmain_pok_h_o,             // VCMAIN POK @3.3v
  output logic vcmain_pok_por_h_o,         // VCMAIN_POK_POR @3.3v
  output logic vcaon_pok_h_o,              // VCAON Exist @3.3v
  output logic vcaon_pok_1p1_h_o,          // VCAON Exist @3.3v for BE 1.1v (UPF issue)
  output logic vcaon_pok_por_h_o,          // VCAON_POK_POR @3.3v
  output logic [2-1:0] vio_pok_h_o,        // vioa/b_pok_h signals @3.3v
  output logic vcc_pok_str_h_o,            // VCC Exist Stretched @3.3V
  output logic vcc_pok_str_1p1_h_o,        // VCC Exist Stretched @3.3V for BE 1.1v (UPF issue)
  output logic deep_sleep_h_o,             // Deep Sleep (main regulator & switch are off) @3.3v
  output logic flash_power_down_h_o,       //
  output logic flash_power_ready_h_o,      //
  output logic [2-1:0] otp_power_seq_h_o   // MMR0,24 masked by PDM, out (VCC)
);

// Turn 1.1v into 3.3v signals
////////////////////////////////////////
assign vcaon_pok_por_h_o = vcaon_pok_por_h_i;    // Level Up Shifter
assign vcmain_pok_por_h_o = vcmain_pok_por_h_i;  // Level Up Shifter
assign vio_pok_h_o[1:0] = vio_pok_h_i[1:0];      // Level Up Shifter


///////////////////////////////////////
// Regulators Enable State Machine
///////////////////////////////////////
logic fla_pdm_h, otp_pdm_h;
logic [9-1:0] dly_cnt, hc2lc_val, lc2hc_val;  // upto 255 aon clock (1275us)

// DV Hook
logic [1:0] dv_hook, dft_sel;

`ifndef SYNTHESIS
initial begin
  // Regulator Power-up time (non cold power-up) selected according to 'dv_hook' value:
  //
  //   0: hc2lc_val=HC2LCOC;    lc2hc_val=LC2HCOC;
  //   1: hc2lc_val=HC2LCOC*2;  lc2hc_val=LC2HCOC*2;
  //   2: hc2lc_val=9'd2;       lc2hc_val=9'd6;
  //   3: hc2lc_val=9'd4;       lc2hc_val=9'd12;
  //
  if ( !$value$plusargs("accelerate_regulators_power_up_time=%d", dv_hook) ) begin
    dv_hook = 2'd0;
  end
  `ASSERT_I(accelerate_regulators_power_up_time, dv_hook inside {[0:3]})
end
`else
assign dv_hook = 2'd0;
`endif

localparam int unsigned HC2LCOC = ast_pkg::Hc2LcTrCyc;
localparam int unsigned LC2HCOC = ast_pkg::Lc2HcTrCyc;
logic [9-1:0] cld_pu_val;

`ifndef SYNTHESIS
initial begin
  // Cold Power-up time can be selected between 2 and LC2HCOC (default: ast_pkg::Lc2HcTrCyc)
  if ( !$value$plusargs("accelerate_cold_power_up_time=%d", cld_pu_val) ) begin
    cld_pu_val = LC2HCOC[9-1:0];
  end
  `ASSERT_I(accelerate_cold_power_up_time, cld_pu_val inside {[2:LC2HCOC[9-1:0]]})
end
`else
assign cld_pu_val = LC2HCOC[9-1:0];
`endif

// Force 2'b11 to reduce LDOs time & double LDOs start-up time
assign dft_sel = dv_hook;

assign hc2lc_val = (dft_sel == 2'b10) ? 9'd2 :
                   (dft_sel == 2'b11) ? 9'd4 :
                   (dft_sel == 2'b00) ? HC2LCOC[9-1:0] :
                                        HC2LCOC[8-1:0]*2;

assign lc2hc_val = (dft_sel == 2'b10) ? 9'd6 :
                   (dft_sel == 2'b11) ? 9'd12 :
                   (dft_sel == 2'b00) ? LC2HCOC[9-1:0] :
                                        LC2HCOC[8-1:0]*2;



///////////////////////////////////////
// Regulators State Machine
///////////////////////////////////////
typedef enum logic [3-1:0] {
  RGLS_CLDPU = 3'd0,  // Cold power-up (MAIN Regulator ON, AON Regulator OFF, Power Switch Enabled)
  RGLS_VCMON = 3'd1,  // MAIN Regulator ON (AON Regulator OFF, Power Switch Enabled)
  RGLS_VCM2A = 3'd3,  // MAIN Regulator ON (AON Regulator rN,  Power Switch Enabled->Disabled)
  RGLS_VCAON = 3'd7,  // AON Regulator ON (MAIN Regulator OFF, Power Switch Diabled)
  RGLS_VCA2M = 3'd5,  // AON Regulator ON (MAIN Regulator ON,  Power Switch Diabled->Enabled)
  RGLS_BROUT = 3'd6   // Brownout (MAIN Regulator ON, AON Regulator OFF, Power Switch Enabled)
} rgls_sm_e;

rgls_sm_e rgls_sm;
logic vcmain_pok_h, vcaon_pok_h, main_pd_str_h;

// Hold state machin reset on brownout for minimum 13us.
logic rgls_rst_h_n;
assign rgls_rst_h_n = vcc_pok_str_h_o;

// Syncronizers
// First stage clk FE & second clk RE
///////////////////////////////////////
logic vcc_pok_fe_h, vcc_pok_s_h;


logic clk_src_aon_h_n;
assign clk_src_aon_h_n = scan_mode_h_i ? clk_src_aon_h_i :
                                        !clk_src_aon_h_i;

always_ff @( posedge clk_src_aon_h_n, negedge rgls_rst_h_n ) begin
  if ( !rgls_rst_h_n ) begin
    vcc_pok_fe_h <= 1'b0;
  end else begin
    vcc_pok_fe_h  <= vcc_pok_h_i;
  end
end

always_ff @( posedge clk_src_aon_h_i, negedge rgls_rst_h_n ) begin
  if ( !rgls_rst_h_n ) begin
    vcc_pok_s_h <= 1'b0;
  end else begin
    vcc_pok_s_h <= vcc_pok_fe_h;
  end
end

// Regulators State Mashine
////////////////////////////////////////
always_ff @( posedge clk_src_aon_h_i, negedge rgls_rst_h_n ) begin
  if ( !rgls_rst_h_n ) begin
    vcmain_pok_h     <= 1'b0;        // VCMAIN Rail Disabled
    vcaon_pok_h      <= 1'b0;        // VCAON Rail Disabled
    main_pd_str_h    <= 1'b0;        // Power Down Stratch off
    //
    rglssm_vcmon_h_o <= 1'b0;        //
    rglssm_vmppr_h_o <= 1'b1;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
    rglssm_brout_h_o <= 1'b0;        //
    fla_pdm_h        <= 1'b1;        // !((rgls_sm == RGLS_VCMON) || (rgls_sm == RGLS_BROUT))
    //
    dly_cnt          <= cld_pu_val;  // VCMAIN Regulator power-up time
    //
    rgls_sm          <= RGLS_CLDPU;  // Power VCMAIN (Cold)
  end else begin
    unique case ( rgls_sm )
      RGLS_CLDPU: begin
        vcmain_pok_h       <= 1'b0;        // VCMAIN Rail Disabled
        vcaon_pok_h        <= 1'b0;        // VCAON Rail Disabled
        main_pd_str_h      <= 1'b0;        // Power Down Stratch off
        //
        rglssm_vcmon_h_o   <= 1'b0;        //
        rglssm_vmppr_h_o   <= 1'b1;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
        rglssm_brout_h_o   <= 1'b0;        //
        fla_pdm_h          <= 1'b1;        // !((rgls_sm == RGLS_VCMON)||(rgls_sm == RGLS_BROUT))
        //
        dly_cnt            <= dly_cnt - 1'b1;
        //
        if (dly_cnt == '0) begin
          vcmain_pok_h     <= 1'b1;        // VCMAIN Rail Enable
          vcaon_pok_h      <= 1'b1;        // VCAON Rail Enabled
          rglssm_vcmon_h_o <= 1'b1;        // (rgls_sm == RGLS_VCMON)
          rglssm_vmppr_h_o <= 1'b0;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
          fla_pdm_h        <= 1'b0;        //
          rgls_sm          <= RGLS_VCMON;  // VCMAIN Regultor is ON!
        end else begin
          rgls_sm          <= RGLS_CLDPU;  // Power VCMAIN!
        end
      end

      RGLS_VCMON: begin
        vcmain_pok_h       <= 1'b1;        // VCMAIN Rail Enabled
        vcaon_pok_h        <= 1'b1;        // VCAON Rail Enabled
        main_pd_str_h      <= 1'b0;        // Power Down Stratch
        //
        rglssm_vcmon_h_o   <= 1'b1;        // (rgls_sm == RGLS_VCMON)
        rglssm_vmppr_h_o   <= 1'b0;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
        rglssm_brout_h_o   <= 1'b0;        //
        fla_pdm_h          <= 1'b0;        //
        //
        dly_cnt            <= hc2lc_val;   // VCAON Regulator power-up time
        //
        if ( !vcc_pok_s_h ) begin
          rglssm_vcmon_h_o <= 1'b0;        //
          rglssm_vmppr_h_o <= 1'b0;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
          rglssm_brout_h_o <= 1'b1;        // (rgls_sm == RGLS_BROUT)
          fla_pdm_h        <= 1'b0;        //
          rgls_sm          <= RGLS_BROUT;  // Brownout
        end else if ( main_pd_h_i && !por_sync_h_i ) begin
          main_pd_str_h    <= 1'b1;        // Power Down Stratch on
          rglssm_vcmon_h_o <= 1'b0;        //
          rglssm_vmppr_h_o <= 1'b0;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
          fla_pdm_h        <= 1'b1;        // !((rgls_sm == RGLS_VCMON) || (rgls_sm == RGLS_BROUT))
          rgls_sm          <= RGLS_VCM2A;  // VCMAIN to VCAON Transition
        end else begin
          rgls_sm          <= RGLS_VCMON;  // VCMAIN Regulator is ON!
        end
      end

      RGLS_VCM2A: begin
        vcmain_pok_h       <= 1'b1;        // VCMAIN Rail Enabled
        vcaon_pok_h        <= 1'b1;        // VCAON Rail Enabled
        main_pd_str_h      <= 1'b1;        // Power Down Stratch
        //
        rglssm_vcmon_h_o   <= 1'b0;        //
        rglssm_vmppr_h_o   <= 1'b0;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
        rglssm_brout_h_o   <= 1'b0;        //
        fla_pdm_h          <= 1'b1;        // !((rgls_sm == RGLS_VCMON) || (rgls_sm == RGLS_BROUT))
        //
        dly_cnt            <= dly_cnt - 1'b1;
        //
        if ( por_sync_h_i ) begin
          vcmain_pok_h     <= 1'b1;        // VCMAIN Rail Enable
          vcaon_pok_h      <= 1'b1;        // VCAON Rail Enabled
          rglssm_vcmon_h_o <= 1'b1;        // (rgls_sm == RGLS_VCMON)
          rglssm_vmppr_h_o <= 1'b0;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
          fla_pdm_h        <= 1'b0;        //
          rgls_sm          <= RGLS_VCMON;  // VCMAIN Regultor is ON!
        end else if ( dly_cnt == '0 ) begin
          rglssm_vmppr_h_o <= 1'b1;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
          rgls_sm          <= RGLS_VCAON;  // VCAON Regulator is ON!
        end else begin
          rgls_sm          <= RGLS_VCM2A;  // VCMAIN to VCAON Transition
        end
      end

      RGLS_VCAON: begin
        vcmain_pok_h       <= 1'b0;        // VCMAIN Rail Disabled
        vcaon_pok_h        <= 1'b1;        // VCAON Rail Enabled
        main_pd_str_h      <= 1'b1;        // Power Down Stratch
        //
        rglssm_vcmon_h_o   <= 1'b0;        //
        rglssm_vmppr_h_o   <= 1'b1;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
        rglssm_brout_h_o   <= 1'b0;        //
        fla_pdm_h          <= 1'b1;        // !((rgls_sm == RGLS_VCMON) || (rgls_sm == RGLS_BROUT))
        //
        dly_cnt            <= lc2hc_val;   // VCMAIN Regulator power-up time
        //
        if ( !main_pd_h_i || por_sync_h_i ) begin
          rglssm_vmppr_h_o <= 1'b1;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
          rgls_sm          <= RGLS_VCA2M;  // VCAON->VCMAIN Transition
        end else begin
          rgls_sm          <= RGLS_VCAON;  // VCAON Regulator is ON!
        end
      end

      RGLS_VCA2M: begin
        vcmain_pok_h       <= 1'b0;        // VCMAIN Rail Disable
        vcaon_pok_h        <= 1'b1;        // VCAON Rail Enabled
        main_pd_str_h      <= 1'b0;        // Power Down Stratch off
        //
        rglssm_vcmon_h_o   <= 1'b0;        //
        rglssm_vmppr_h_o   <= 1'b1;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
        rglssm_brout_h_o   <= 1'b0;        //
        fla_pdm_h          <= 1'b1;        // !((rgls_sm == RGLS_VCMON) || (rgls_sm == RGLS_BROUT))
        //
        dly_cnt            <= dly_cnt - 1'b1;
        //
        if ( dly_cnt == '0 ) begin
          vcmain_pok_h     <= 1'b1;        // VCMAIN Rail Enable
          vcaon_pok_h      <= 1'b1;        // VCAON Rail Enabled
          rglssm_vcmon_h_o <= 1'b1;        // (rgls_sm == RGLS_VCMON)
          rglssm_vmppr_h_o <= 1'b0;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
          fla_pdm_h        <= 1'b0;        //
          rgls_sm          <= RGLS_VCMON;  // VCMAIN Regulator is ON!
        end else begin
          rgls_sm          <= RGLS_VCA2M;  // VCAON->VCMAIN Transition
        end
      end

      RGLS_BROUT: begin
        vcmain_pok_h       <= 1'b1;        // VCMAIN Rail Enabled
        vcaon_pok_h        <= 1'b1;        // VCAON Rail Enabled
        main_pd_str_h      <= 1'b0;        // Powe Down Stratch off
        //
        rglssm_vcmon_h_o   <= 1'b0;        //
        rglssm_vmppr_h_o   <= 1'b0;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
        rglssm_brout_h_o   <= 1'b1;        // (rgls_sm == RGLS_BROUT)
        fla_pdm_h          <= 1'b0;        //
        //
        dly_cnt            <= lc2hc_val;   // VCMAIN Regulator power-up time
        //
        rgls_sm            <= RGLS_BROUT;  // Brownout
      end

      default: begin
        vcmain_pok_h       <= 1'b0;        // VCMAIN Rail Disabled
        vcaon_pok_h        <= 1'b0;        // VCAON Rail Disabled
        main_pd_str_h      <= 1'b0;        // Powe Down Stratch off
        //
        rglssm_vcmon_h_o   <= 1'b0;        //
        rglssm_vmppr_h_o   <= 1'b1;        // (rgls_sm == RRGLS_[CLDPU | VCAON | VCA2M])
        rglssm_brout_h_o   <= 1'b0;        //
        fla_pdm_h          <= 1'b1;        // !((rgls_sm == RGLS_VCMON) || (rgls_sm == RGLS_BROUT))
        //
        dly_cnt            <= lc2hc_val;   // VCMAIN Regulator power-up time
        //
        rgls_sm            <= RGLS_CLDPU;  // Power VCMAIN (Cold)
      end
    endcase
  end
end


///////////////////////////////////////
// VCMAIN_POK & VCAON POK
///////////////////////////////////////
assign vcmain_pok_h_o = vcmain_pok_h && vcmain_supp_i;
// VCAON POK is needed for cold power-up to enable the AON clock
// Therefore, it is connected directly to VCC POK.
assign vcaon_pok_h_o = vcc_pok_h_i && vcaon_supp_i;
assign vcaon_pok_1p1_h_o = vcaon_pok_h_o;  // For layout separation


///////////////////////////////////////
// Streched VCC_POK During Brownout
///////////////////////////////////////
localparam int VccPokStrNum = 4;  // (Min-Max) (3-4)x5us=(15-20)us

logic vcc_pok_set_h, vcc_pok_rst_h_n;
logic [VccPokStrNum-1:0] vcc_pok_str_no_scan_h;

assign vcc_pok_rst_h_n = vcc_pok_h_i || vcaon_pok_h_o;  // Non-Scan

// Enable proper order of reset/set execution
always_comb begin
  vcc_pok_set_h = vcc_pok_rst_h_n && vcc_pok_h_i;
end

always_ff @( posedge clk_src_aon_h_i, negedge vcc_pok_rst_h_n, posedge vcc_pok_set_h ) begin
  if ( !vcc_pok_rst_h_n ) begin
    vcc_pok_str_no_scan_h[0] <= 1'b0;
  end else if ( vcc_pok_set_h ) begin
    vcc_pok_str_no_scan_h[0] <= 1'b1;
  end else begin
    vcc_pok_str_no_scan_h[0] <= 1'b0;
  end
end

for (genvar i = 1; i < VccPokStrNum; i++ ) begin : gen_vcc_pok_str
  always_ff @( posedge clk_src_aon_h_i, negedge vcc_pok_rst_h_n, posedge vcc_pok_set_h ) begin
    if ( !vcc_pok_rst_h_n ) begin
      vcc_pok_str_no_scan_h[i] <= 1'b0;
    end else if ( vcc_pok_set_h ) begin
      vcc_pok_str_no_scan_h[i] <= 1'b1;
    end else begin
      vcc_pok_str_no_scan_h[i] <= vcc_pok_str_no_scan_h[i-1];
    end
  end
end

assign vcc_pok_str_h_o = vcc_pok_str_no_scan_h[VccPokStrNum-1];
assign vcc_pok_str_1p1_h_o = vcc_pok_str_no_scan_h[VccPokStrNum-1];


///////////////////////////////////////
// Deep Sleep Indication
///////////////////////////////////////
always_ff @( posedge clk_src_aon_h_i, negedge rgls_rst_h_n ) begin
  if ( !rgls_rst_h_n ) begin
    deep_sleep_h_o <= 1'b0;
  end else begin
    deep_sleep_h_o <= main_pd_h_i || main_pd_str_h;
  end
end


///////////////////////////////////////
// Flash
///////////////////////////////////////
// fla_pdm_h = !(rglssm_vcmon || rglssm_brout);
assign flash_power_down_h_o  = scan_mode_h_i || fla_pdm_h;
assign flash_power_ready_h_o = vcc_pok_h_i;


///////////////////////////////////////
// OTP
///////////////////////////////////////
assign otp_pdm_h = !rglssm_vcmon_h_o;
assign otp_power_seq_h_o[0] = !scan_mode_h_i && !otp_pdm_h && otp_power_seq_h_i[0];
assign otp_power_seq_h_o[1] =  scan_mode_h_i ||  otp_pdm_h || otp_power_seq_h_i[1];


/////////////////////
// Unused Signals  //
/////////////////////
logic unused_sigs;

assign unused_sigs = ^{ vcaon_pok_h };

endmodule : rglts_pdm_3p3v
