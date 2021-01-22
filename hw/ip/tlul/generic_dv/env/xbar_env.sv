// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Xbar environment class
// ---------------------------------------------
class xbar_env extends dv_base_env#(.CFG_T              (xbar_env_cfg),
                                    .VIRTUAL_SEQUENCER_T(xbar_virtual_sequencer),
                                    .SCOREBOARD_T       (xbar_scoreboard),
                                    .COV_T              (xbar_env_cov));

  tl_agent          host_agent[];
  tl_agent          device_agent[];

  `uvm_component_utils(xbar_env)

  function new (string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Connect TileLink host and device agents
    host_agent = new[cfg.num_hosts];
    foreach (host_agent[i]) begin
      host_agent[i] = tl_agent::type_id::create(
                      $sformatf("%0s_agent", xbar_hosts[i].host_name), this);
      uvm_config_db#(tl_agent_cfg)::set(this,
        $sformatf("*%0s*", xbar_hosts[i].host_name),"cfg", cfg.host_agent_cfg[i]);
      cfg.host_agent_cfg[i].en_cov = cfg.en_cov;
    end
    device_agent = new[cfg.num_devices];
    foreach (device_agent[i]) begin
      device_agent[i] = tl_agent::type_id::create(
                      $sformatf("%0s_agent", xbar_devices[i].device_name), this);
      uvm_config_db#(tl_agent_cfg)::set(this,
        $sformatf("*%0s*", xbar_devices[i].device_name), "cfg", cfg.device_agent_cfg[i]);
      cfg.device_agent_cfg[i].en_cov = cfg.en_cov;
    end

    // this clock isn't connected to design but only used for TB, like measure timeout, drive long
    // enough reset (bigger than 1 cycle of any DUT clock). Use fixed frequency 100 Mhz
    cfg.clk_rst_vif.set_freq_mhz(100);

    // increase timer as device may respond very slowly in test - xbar_main_random_slow_rsp
    scoreboard.timeout_cycle_limit = 100_000;
    // create analysis_fifos and scoreboard_queue
    foreach (xbar_hosts[i]) begin
      scoreboard.add_item_port({"a_chan_", xbar_hosts[i].host_name}, scoreboard_pkg::kSrcPort);
      scoreboard.add_item_port({"d_chan_", xbar_hosts[i].host_name}, scoreboard_pkg::kDstPort);
      // this queue is used to store expected rsp in d channel for unmapped address
      scoreboard.add_item_queue({"host_unmapped_addr_", xbar_hosts[i].host_name},
                                scoreboard_pkg::kInOrderCheck);
    end
    foreach (xbar_devices[i]) begin
      scoreboard.add_item_port({"a_chan_", xbar_devices[i].device_name}, scoreboard_pkg::kDstPort);
      scoreboard.add_item_port({"d_chan_", xbar_devices[i].device_name}, scoreboard_pkg::kSrcPort);

      scoreboard.add_item_queue({"a_chan_", xbar_devices[i].device_name},
                         scoreboard_pkg::kOutOfOrderCheck);
      scoreboard.add_item_queue({"d_chan_", xbar_devices[i].device_name},
                         scoreboard_pkg::kOutOfOrderCheck);
    end
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect virtual sequencer
    if (cfg.is_active) begin
      virtual_sequencer.host_seqr = new[cfg.num_hosts];
      virtual_sequencer.device_seqr = new[cfg.num_devices];
      foreach (host_agent[i]) begin
        virtual_sequencer.host_seqr[i] = host_agent[i].sequencer;
      end
      foreach (device_agent[i]) begin
        virtual_sequencer.device_seqr[i] = device_agent[i].sequencer;
      end
    end
    // Connect scoreboard
    foreach (host_agent[i]) begin
      host_agent[i].monitor.a_chan_port.connect(
          scoreboard.item_fifos[{"a_chan_", xbar_hosts[i].host_name}].analysis_export);
      host_agent[i].monitor.d_chan_port.connect(
          scoreboard.item_fifos[{"d_chan_", xbar_hosts[i].host_name}].analysis_export);
    end
    foreach (device_agent[i]) begin
      device_agent[i].monitor.a_chan_port.connect(
          scoreboard.item_fifos[{"a_chan_", xbar_devices[i].device_name}].analysis_export);
      device_agent[i].monitor.d_chan_port.connect(
          scoreboard.item_fifos[{"d_chan_", xbar_devices[i].device_name}].analysis_export);
    end
  endfunction : connect_phase

endclass
