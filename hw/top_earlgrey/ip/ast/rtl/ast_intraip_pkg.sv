// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

///////////////////////////////////////////////////////////////////////////////
// Open-source simplified intra-IP / inter-partition communication structures
///////////////////////////////////////////////////////////////////////////////
package ast_intraip_pkg;
  import ast_pkg::*;

  // Power signals: secondary to primary partition
  typedef struct packed {
    logic vcc_pok;
    logic vcaon_pok;
    logic vcmain_pok_h;
    logic vcmain_pok_por;
    logic vcc_pok_str;
  } pwr_s2p_t;

  // Clock and reset signals for secondary to primary partition communication
  typedef struct packed {
    logic clk_aon;
    logic clk_ast_tlul;
    logic rst_ast_tlul_n;
    logic clk_ast_rng;
    logic rst_ast_rng_n;
    logic clk_ast_es;
    logic rst_ast_es_n;
    logic rst_sys_clk_n;
    logic rst_io_clk_n;
    logic rst_usb_clk_n;
  } clk_rst_s2p_t;

  // Clock bypass interface: primary to secondary partition
  typedef struct packed {
    logic clk_ext_aon;        // Divided external clock for AON (from main dividers)
    logic aon_select_ext;     // AON bypass select (1=external, 0=internal)
  } clks_byp_p2s_t;

  // Clock bypass interface: secondary to primary partition
  typedef struct packed {
    logic clk_src_aon_o;      // Selected AON clock output
    logic clk_src_aon_val_o;  // AON clock valid
    logic aon_clk_byp_en;     // AON bypass enabled (for ack generation)
  } clks_byp_s2p_t;

  // Oscillator control: secondary to primary partition
  typedef struct packed {
    logic deep_sleep;
    logic usb_ref_pulse;
    logic usb_ref_val;
  } clk_osc_s2p_t;

  typedef struct packed {
    logic clk_src_io_val;
    logic clk_src_usb_val;
    logic clk_src_sys_val;
  } pwrmgr_p2s_t;

  typedef struct packed {
    logic clk_src_sys_en;
    logic clk_src_io_en;
    logic clk_src_usb_en;
  } pwrmgr_s2p_t;

  // Secondary to primary partition Communication Structure (OS simplified)
  typedef struct packed {
    // Clock bypass interface
    clks_byp_s2p_t clks_byp;

    // Oscillator control interface
    clk_osc_s2p_t clk_osc;

    // Clock and reset signals
    clk_rst_s2p_t clk_rst;

    // Power signals
    pwr_s2p_t pwr;

    // Scan signals
    logic scan_mode;
    logic scan_reset_n;

    // Calibration signals
    logic sys_io_osc_cal;
    logic usb_osc_cal;

    // Memory configuration
    ast_mem_cfg_primary_req_t mem_cfg_req;

    // pwrmgr signals
    pwrmgr_s2p_t pwrmgr_req;
  } s2p_t;

  // Primary to secondary partition Communication Structure (OS simplified)
  typedef struct packed {
    // Clock bypass interface
    clks_byp_p2s_t clks_byp;

    // Alert source from main (TLUL integrity error)
    ast_dif_t ot0_alert_src;

    logic regal_we;

    // Memory configuration
    ast_mem_cfg_primary_rsp_t mem_cfg_rsp;

    // pwrmgr signals
    pwrmgr_p2s_t pwrmgr_rsp;
  } p2s_t;

endpackage
