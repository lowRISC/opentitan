// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests shadow_registers' update error and storage error
// The sequence will loop thorugh all shadow_regs from each IP
// It will create update error by first write value 'h5555_5555 to shadow_reg, then write value
// 'haaaa_aaaa as second write, and check the corresponding alert handshake
// It will create storage error by randomly backdoor write to shadow register's committed_val or
// shadow_val, and check the corresponding alert handshake
class chip_shadow_reg_errors_vseq extends chip_common_vseq;
  `uvm_object_utils(chip_shadow_reg_errors_vseq)
  `uvm_object_new

  // Most of the shadow_reg related tasks are from `dv/sv/cip_lib/cip_base_vseq.sv`
  virtual task body();
    dv_base_reg shadowed_csrs[$];

    // Get all shadowed_regs from each IP
    ral.get_shadowed_regs(shadowed_csrs);
    shadowed_csrs.shuffle();

    foreach (shadowed_csrs[i]) begin
      bit             alert_triggered;
      string          alert_name;
      bit [TL_DW-1:0] origin_val, poke_val;
      bkdr_reg_path_e kind;

      // Create update error
      wr_shadowed_reg_update_err(shadowed_csrs[i], alert_triggered);

      // Check update error alerts
      alert_name = shadowed_csrs[i].get_update_err_alert_name();
      `DV_SPINWAIT(while (!alert_triggered && !cfg.m_alert_agent_cfg[alert_name].vif.get_alert())
                   cfg.clk_rst_vif.wait_clks(1);,
                   $sformatf("%0s update_err alert not detected", shadowed_csrs[i].get_name()));
      `DV_SPINWAIT(cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();,
                   $sformatf("timeout for alert:%0s", alert_name))

      // Create storage error, randomly choose to poke committed or shadow value
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(kind, kind inside
                                         {BkdrRegPathRtlCommitted, BkdrRegPathRtlShadow};)
      csr_peek(.ptr(shadowed_csrs[i]), .value(origin_val), .kind(kind));
      poke_val = gen_storage_err_val(shadowed_csrs[i], origin_val, 0);
      csr_poke(.csr(shadowed_csrs[i]), .value(poke_val), .kind(kind), .predict(1));

      // Check storage error alerts
      alert_name = shadowed_csrs[i].get_storage_err_alert_name();
      `DV_SPINWAIT(while (!cfg.m_alert_agent_cfg[alert_name].vif.get_alert())
                   cfg.clk_rst_vif.wait_clks(1);,
                   $sformatf("%0s storage_err alert not detected", shadowed_csrs[i].get_name()));
      csr_poke(.csr(shadowed_csrs[i]), .value(origin_val), .kind(kind), .predict(1));
      `DV_SPINWAIT(cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();,
                   $sformatf("timeout for alert:%0s", alert_name))
    end
  endtask : body

  // Generally we should get update error if first write of the register is 'h5555_5555,
  // and the second write is 'haaaa_aaaa
  // If any shadow reg does not follow this, can add additional requirements to this task
  virtual task wr_shadowed_reg_update_err(dv_base_reg csr, output bit alert_triggered);
    csr_wr(.csr(csr), .value('h5555_5555), .en_shadow_wr(0), .predict(1));
    shadow_reg_wr(.csr(csr), .wdata('haaaa_aaaa), .alert_triggered(alert_triggered));
  endtask : wr_shadowed_reg_update_err

endclass
