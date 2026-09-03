// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(rram_ctrl_core_reg_block));
  `uvm_object_utils(rram_ctrl_env_cfg)

  // Clock and reset for the otp_ctrl interface, present at the DUT's clk_otp_i and
  // rst_otp_ni ports.
  virtual clk_rst_if otp_clk_rst_vif;

  // otp_ctrl scrambling-key request/response, driven by otp_model() in
  // rram_ctrl_base_vseq.sv. See rram_ctrl_otp_key_if.sv.
  otp_key_vif_t otp_key_vif;

  // Name of the RAL model tied to the host interface (tl_host), which accesses the
  // RRAM data array.
  string host_ral_name = "rram_ctrl_host_reg_block";
  // Name of the RAL model tied to the RRAM macro's primitive interface (tl_prim).
  string prim_ral_name = "rram_macro_prim_reg_block";

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void initialize(bit inherit_ral_models = 1'b0);

endclass : rram_ctrl_env_cfg


function rram_ctrl_env_cfg::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_env_cfg::initialize(bit inherit_ral_models = 1'b0);
  list_of_alerts = rram_ctrl_env_pkg::LIST_OF_ALERTS;

  ral_model_names[host_ral_name] = 1'b0;
  clk_freqs_mhz[host_ral_name] = clk_freq_mhz;
  ral_model_names[prim_ral_name] = 1'b0;
  clk_freqs_mhz[prim_ral_name] = clk_freq_mhz;

  super.initialize(inherit_ral_models);

  // Configure tl agents. Everything defaults to 1 outstanding request, except the
  // host interface (tl_host), which can tolerate up to 2 outstanding read requests.
  m_tl_agent_cfg.max_outstanding_req = 1;
  m_tl_agent_cfgs[prim_ral_name].max_outstanding_req = 1;
  m_tl_agent_cfgs[host_ral_name].max_outstanding_req = rram_ctrl_pkg::NumOutstandingRdReq;

  // Set num_interrupts
  begin
    uvm_reg rg = ral.get_reg_by_name("intr_state");
    if (rg != null) begin
      num_interrupts = ral.intr_state.get_n_used_bits();
      `DV_CHECK_EQ_FATAL(num_interrupts, rram_ctrl_env_pkg::NumRramCtrlIntr,
                          "num_interrupts does not match rram_ctrl_intr_e")
    end
  end
endfunction : initialize
