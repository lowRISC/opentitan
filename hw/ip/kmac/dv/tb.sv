// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module tb;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import kmac_env_pkg::*;
  import kmac_test_pkg::*;
  import kmac_reg_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  wire clk, rst_n;
  wire devmode;
  wire idle;
  wire [NUM_MAX_INTERRUPTS-1:0] interrupts;
  // keymgr/kmac sideload wires
  keymgr_pkg::hw_key_req_t kmac_sideload_key;
  // kmac_app interfaces
  kmac_pkg::app_req_t [kmac_pkg::NumAppIntf-1:0] app_req;
  kmac_pkg::app_rsp_t [kmac_pkg::NumAppIntf-1:0] app_rsp;

  // interfaces
  clk_rst_if clk_rst_if(.clk(clk), .rst_n(rst_n));

  pins_if #(1)                   devmode_if(devmode);
  pins_if #(1)                   idle_if(idle);
  pins_if #(NUM_MAX_INTERRUPTS)  intr_if(interrupts);

  tl_if tl_if(.clk(clk), .rst_n(rst_n));

  kmac_sideload_if sideload_if();

  kmac_app_intf kmac_app_if[kmac_pkg::NumAppIntf](.clk(clk), .rst_n(rst_n));

  // edn_clk, edn_rst_n and edn_if is defined and driven in below macro
  `DV_EDN_IF_CONNECT

  // dut

  kmac #(.EnMasking(`EN_MASKING), .ReuseShare(`REUSE_SHARE)) dut (
    .clk_i              (clk                          ),
    .rst_ni             (rst_n                        ),

    // TLUL interface
    .tl_i               (tl_if.h2d                    ),
    .tl_o               (tl_if.d2h                    ),

    // KeyMgr sideload key interface
    .keymgr_key_i       (sideload_if.sideload_key     ),

    // KeyMgr KDF datapath
    //
    // TODO: this is set to 0 for the time being to get the csr tests passing.
    //       this will eventually be hooked up to the kmac<->keymgr agent.
    .app_i       (app_req ),
    .app_o       (app_rsp ),

    // Interrupts
    .intr_kmac_done_o   (interrupts[KmacDone]         ),
    .intr_fifo_empty_o  (interrupts[KmacFifoEmpty]    ),
    .intr_kmac_err_o    (interrupts[KmacErr]          ),

    // Idle interface
    .idle_o             (idle                         ),

    // EDN interface
    .clk_edn_i          (edn_clk                      ),
    .rst_edn_ni         (edn_rst_n                    ),
    .entropy_o          (edn_if.req                   ),
    .entropy_i          ({edn_if.ack, edn_if.d_data}  )
  );

  for (genvar i = 0; i < kmac_pkg::NumAppIntf; i++) begin : gen_kmac_app_intf
    assign app_req[i]                   = kmac_app_if[i].kmac_data_req;
    assign kmac_app_if[i].kmac_data_rsp = app_rsp[i];

    initial begin
      uvm_config_db#(virtual kmac_app_intf)::set(null,
          $sformatf("*env.m_kmac_app_agent[%0d]*", i), "vif", kmac_app_if[i]);
    end
  end

  initial begin
    // drive clk and rst_n from clk_if
    clk_rst_if.set_active();
    uvm_config_db#(virtual clk_rst_if)::set(null, "*.env", "clk_rst_vif", clk_rst_if);
    uvm_config_db#(intr_vif)::set(null, "*.env", "intr_vif", intr_if);
    uvm_config_db#(devmode_vif)::set(null, "*.env", "devmode_vif", devmode_if);
    uvm_config_db#(virtual tl_if)::set(null, "*.env.m_tl_agent*", "vif", tl_if);
    uvm_config_db#(virtual pins_if#(1))::set(null, "*.env", "idle_vif", idle_if);
    uvm_config_db#(virtual kmac_sideload_if)::set(null, "*.env", "sideload_vif", sideload_if);
    $timeformat(-12, 0, " ps", 12);
    run_test();
  end

endmodule
