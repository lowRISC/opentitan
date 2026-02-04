// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AST AON-Main Domain Communication Package
// Defines structured communication between AON and Main power domains
//
//############################################################################

package ast_aon_main_pkg;

  import ast_pkg::*;
  import ast_reg_pkg::*;


  //////////////////////////////////////////////////////////////////////////
  // OS Simplified Inter-domain Communication Structures
  //////////////////////////////////////////////////////////////////////////

  // Power signals: AON to Main
  typedef struct packed {
    logic vcc_pok;
    logic vcaon_pok;
    logic vcmain_pok_h;
    logic vcmain_pok_por;
    logic vcc_pok_str;
  } pwr_aon_to_main_t;

  // Clock and reset signals for AON to Main domain communication
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
  } aon_to_main_clk_rst_t;

  // Clock bypass interface: Main to AON domain
  typedef struct packed {
    logic clk_ext_aon;        // Divided external clock for AON (from main dividers)
    logic aon_select_ext;     // AON bypass select (1=external, 0=internal)
  } clks_byp_main_to_aon_t;

  // Clock bypass interface: AON to Main domain
  typedef struct packed {
    logic clk_src_aon_o;      // Selected AON clock output
    logic clk_src_aon_val_o;  // AON clock valid
    logic aon_clk_byp_en;     // AON bypass enabled (for ack generation)
  } clks_byp_aon_to_main_t;

  // Oscillator control: AON to Main
  typedef struct packed {
    logic deep_sleep;
    logic usb_ref_pulse;
    logic usb_ref_val;
  } clk_osc_aon_to_main_t;

  // AON to Main Domain Communication Structure (OS simplified)
  typedef struct packed {
    // Clock bypass interface
    clks_byp_aon_to_main_t clks_byp;

    // Oscillator control interface
    clk_osc_aon_to_main_t clk_osc;

    // Clock and reset signals
    aon_to_main_clk_rst_t clk_rst;

    // Power signals
    pwr_aon_to_main_t pwr;

    // Scan signals
    logic scan_mode;
    logic scan_reset_n;

    // Calibration signals
    logic sys_io_osc_cal;
    logic usb_osc_cal;
  } aon_to_main_t;

  // Main to AON Domain Communication Structure (OS simplified)
  typedef struct packed {
    // Clock bypass interface
    clks_byp_main_to_aon_t clks_byp;

    // Alert source from main (TLUL integrity error)
    ast_pkg::ast_dif_t ot0_alert_src;
  } main_to_aon_t;


endpackage : ast_aon_main_pkg
