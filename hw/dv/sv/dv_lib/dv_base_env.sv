// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_env #(type CFG_T               = dv_base_env_cfg,
                    type VIRTUAL_SEQUENCER_T = dv_base_virtual_sequencer,
                    type SCOREBOARD_T        = dv_base_scoreboard,
                    type COV_T               = dv_base_env_cov) extends uvm_env;
  `uvm_component_param_utils(dv_base_env #(CFG_T, VIRTUAL_SEQUENCER_T, SCOREBOARD_T, COV_T))

  CFG_T                      cfg;
  VIRTUAL_SEQUENCER_T        virtual_sequencer;
  SCOREBOARD_T               scoreboard;
  COV_T                      cov;

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    string default_ral_name;
    super.build_phase(phase);
    // get dv_base_env_cfg object from uvm_config_db
    if (!uvm_config_db#(CFG_T)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", cfg.get_type_name()))
    end

    // get vifs for RAL models
    if (cfg.ral_model_names.size > 0) begin
      default_ral_name = cfg.ral.get_type_name();
      foreach (cfg.ral_model_names[i]) begin
        string ral_name = cfg.ral_model_names[i];
        string if_name;

        if (ral_name == default_ral_name) if_name = "clk_rst_vif";
        else                              if_name = {"clk_rst_vif_", ral_name};
        if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", if_name,
            cfg.clk_rst_vifs[ral_name])) begin
          `uvm_fatal(`gfn, $sformatf("failed to get clk_rst_if for %0s from uvm_config_db", ral_name))
        end
        cfg.clk_rst_vifs[ral_name].set_freq_mhz(cfg.clk_freqs_mhz[ral_name]);
      end

      // assign default clk_rst_vif
      `DV_CHECK_FATAL(cfg.clk_rst_vifs.exists(default_ral_name))
      cfg.clk_rst_vif = cfg.clk_rst_vifs[default_ral_name];
    end else begin
      // no RAL model, get the default clk_rst_vif for the block
      // such as xbar, it doesn't has ral model, but it also needs a default clk_rst_vif
      if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "clk_rst_vif", cfg.clk_rst_vif))
      begin
        `uvm_fatal(`gfn, "failed to get clk_rst_if from uvm_config_db")
      end
      cfg.clk_rst_vif.set_freq_mhz(cfg.clk_freq_mhz);
    end


    // create components
    if (cfg.en_cov) begin
      cov = COV_T::type_id::create("cov", this);
      cov.cfg = cfg;
    end

    if (cfg.is_active) begin
      virtual_sequencer = VIRTUAL_SEQUENCER_T::type_id::create("virtual_sequencer", this);
      virtual_sequencer.cfg = cfg;
      virtual_sequencer.cov = cov;
    end

    // scb also monitors the reset and call cfg.reset_asserted/reset_deasserted for reset
    scoreboard = SCOREBOARD_T::type_id::create("scoreboard", this);
    scoreboard.cfg = cfg;
    scoreboard.cov = cov;
  endfunction

endclass
