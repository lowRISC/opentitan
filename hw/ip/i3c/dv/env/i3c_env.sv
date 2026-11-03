// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i3c_env extends cip_base_env #(
    .CFG_T              (i3c_env_cfg),
    .COV_T              (i3c_env_cov),
    .VIRTUAL_SEQUENCER_T(i3c_virtual_sequencer),
    .SCOREBOARD_T       (i3c_scoreboard)
  );
  `uvm_component_utils(i3c_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "clk_aon_rst_vif",
                                                 cfg.clk_aon_rst_vif)) begin
      `uvm_fatal(`gfn, "Failed to get clk_aon_rst_vif from uvm_config_db")
    end
    cfg.clk_aon_rst_vif.set_freq_khz(AonClkFreqKhz);

    if (!uvm_config_db#(board_pullup_vif_t)::get(this, "", "board_pullup_vif",
                                                 cfg.board_pullup_vif)) begin
      `uvm_fatal(`gfn, "Failed to get board_pullup_vif from uvm_config_db")
    end
    cfg.board_pullup_vif.set_pullup_en({NumBusLines{cfg.en_board_pullup}});

    if (!uvm_config_db#(bus_ctrl_vif_t)::get(this, "", "bus_ctrl_vif", cfg.bus_ctrl_vif)) begin
      `uvm_fatal(`gfn, "Failed to get bus_ctrl_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual i3c_buf_mon_if)::get(this, "", "buf_mon_vif",
                                                     cfg.buf_mon_vif)) begin
      `uvm_fatal(`gfn, "Failed to get buf_mon_vif from uvm_config_db")
    end
  endfunction

endclass
