// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_scoreboard #(type RAL_T = chip_ral_pkg::chip_reg_block) extends cip_base_scoreboard #(
    .CFG_T(chip_env_cfg),
    .RAL_T(RAL_T),
    .COV_T(chip_env_cov)
  );
  `uvm_component_utils(chip_scoreboard)

  // local variables

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(jtag_riscv_item) jtag_fifo;

  // local queues to hold incoming packets pending comparison
  uart_item       uart_tx_q[$];
  uart_item       uart_rx_q[$];
  jtag_riscv_item jtag_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    jtag_fifo = new("jtag_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    // Disable alert signal integrity check to avoid false alert on low_power_group_en or
    // alert_init. Alert signal integrity can be checked by assertions.
    check_alert_sig_int_err = 0;
    // Disable individual alert checking in scb. Alerts should be checked in SW or DV sequence.
    do_alert_check = 0;
    super.run_phase(phase);
    fork
      process_jtag_fifo();
      if (cfg.en_cov) process_alerts_for_cov();
    join_none
  endtask

  virtual task process_alerts_for_cov();
    int alert_cg_size = 0;
    forever @cfg.chip_vif.alerts_if.alerts_cb.alerts begin
      foreach (cfg.chip_vif.alerts_if.alerts_cb.alerts[i]) begin
        if (cfg.chip_vif.alerts_if.alerts_cb.alerts[i]) cov.alert_cg_wrap[i].sample(1'b1);
      end
    end
  endtask

  virtual task process_jtag_fifo();
    jtag_riscv_item item;
    forever begin
      jtag_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received jtag item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  // TODO, may add some checking later
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    return;
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

  virtual function bit predict_tl_err(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg_addr_t addr = cfg.ral_models[ral_name].get_normalized_addr(item.a_addr);
    uvm_mem mem = cfg.ral_models[ral_name].default_map.get_mem_by_offset(addr);

    // any access to dv_sim_window returns d_error since this is a DV mem
    // if stub_cpu is off, we force connect this DV mem with a sim_sram, accessing the DV mem is to
    // passing info from C to SV, which won't set d_error
    if (mem != null && mem.get_name() == "dv_sim_window" && cfg.chip_vif.stub_cpu) begin
      if (channel == DataChannel) `DV_CHECK_EQ(item.d_error, 1)
      return 1;
    end
    return super.predict_tl_err(item, channel, ral_name);
  endfunction

endclass
