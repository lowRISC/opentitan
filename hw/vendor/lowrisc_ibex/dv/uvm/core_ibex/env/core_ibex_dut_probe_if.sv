// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to probe DUT internal signal
interface core_ibex_dut_probe_if(input logic clk);

  import uvm_pkg::*;

  logic                              reset;
  logic                              illegal_instr;
  logic                              ecall;
  logic                              wfi;
  logic                              ebreak;
  logic                              dret;
  logic                              mret;
  ibex_pkg::ibex_mubi_t              fetch_enable;
  logic                              core_sleep;
  logic                              alert_minor;
  logic                              alert_major_internal;
  logic                              alert_major_bus;
  logic                              debug_req;
  logic [ibex_pkg::IC_NUM_WAYS-1:0]  ic_tag_req;
  logic                              ic_tag_write;
  logic [ibex_pkg::IC_INDEX_W-1:0]   ic_tag_addr;
  logic [ibex_pkg::IC_NUM_WAYS-1:0]  ic_data_req;
  logic                              ic_data_write;
  logic [ibex_pkg::IC_INDEX_W-1:0]   ic_data_addr;
  ibex_pkg::priv_lvl_e               priv_mode;
  ibex_pkg::ctrl_fsm_e               ctrl_fsm_cs;
  logic                              debug_mode;
  logic                              double_fault_seen;
  logic                              rf_ren_a;
  logic                              rf_ren_b;
  logic                              rf_rd_a_wb_match;
  logic                              rf_rd_b_wb_match;
  logic                              sync_exc_seen;
  logic                              irq_exc_seen;
  logic                              csr_save_cause;
  ibex_pkg::exc_cause_t              exc_cause;
  logic                              wb_exception;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      irq_exc_seen <= 1'b0;
    end else begin
      if (ctrl_fsm_cs == ibex_pkg::IRQ_TAKEN) begin
        irq_exc_seen <= 1'b1;
      end else if (mret) begin
        irq_exc_seen <= 1'b0;
      end
    end
  end

  clocking dut_cb @(posedge clk);
    output fetch_enable;
    output debug_req;
    input reset;
    input illegal_instr;
    input ecall;
    input wfi;
    input ebreak;
    input dret;
    input mret;
    input core_sleep;
    input alert_minor;
    input alert_major_internal;
    input alert_major_bus;
    input ic_tag_req;
    input ic_tag_write;
    input ic_tag_addr;
    input ic_data_req;
    input ic_data_write;
    input ic_data_addr;
    input priv_mode;
    input ctrl_fsm_cs;
    input debug_mode;
    input double_fault_seen;
    input rf_ren_a;
    input rf_ren_b;
    input rf_rd_a_wb_match;
    input rf_rd_b_wb_match;
    input sync_exc_seen;
    input irq_exc_seen;
    input wb_exception;
  endclocking

  initial begin
    debug_req = 1'b0;
  end

  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_rf_ren_a, rf_ren_a)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_rf_ren_b, rf_ren_b)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_rf_rd_a_wb_match, rf_rd_a_wb_match)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_rf_rd_b_wb_match, rf_rd_b_wb_match)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_alert_minor, alert_minor)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_ic_tag_req, ic_tag_req)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_ic_tag_write, ic_tag_write)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_ic_tag_addr, ic_tag_addr)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_ic_data_req, ic_data_req)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_ic_data_write, ic_data_write)
  `DV_CREATE_SIGNAL_PROBE_FUNCTION(signal_probe_ic_data_addr, ic_data_addr)

endinterface
