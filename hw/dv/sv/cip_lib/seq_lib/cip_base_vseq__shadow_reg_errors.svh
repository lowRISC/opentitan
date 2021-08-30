// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This function generates a random CSR value different from the input original value.
// It can generate a rand value, or randomly flip one bit from the original value.
virtual function bit [BUS_DW-1:0] get_shadow_reg_diff_val(dv_base_reg      csr,
                                                          bit [BUS_DW-1:0] origin_val);
  bit [BUS_DW-1:0] reg_mask = csr.get_reg_mask();
  if ($urandom_range(0, 1)) begin
    // Generate pure random value, but make sure it is not equal to the origin_val, and does not
    // inject more than CSR's MSB.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(get_shadow_reg_diff_val,
                                       (get_shadow_reg_diff_val & reg_mask) !=
                                       (origin_val & reg_mask);)
  end else begin
    // Only flip one bit from the original.
    int index;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(index, reg_mask[index] == 1;)
    get_shadow_reg_diff_val = origin_val;
    get_shadow_reg_diff_val [index] = ~get_shadow_reg_diff_val[index];
  end
endfunction

// Alert triggers as soon as design accept the TLUL transaction, if wait until csr_wr() finishes
// then check alert, the alert transaction might already finished.
// This task can be overridden in block level common_vseq for specific shadow_regs.
virtual task shadow_reg_wr(dv_base_reg csr, uvm_reg_data_t wdata);
  fork
    begin
      csr_wr(.ptr(csr), .value(wdata), .en_shadow_wr(0), .predict(1));
    end
    begin
      string alert_name = csr.get_update_err_alert_name();
      `DV_SPINWAIT(while (!cfg.m_alert_agent_cfg[alert_name].vif.get_alert()) begin
                     cfg.clk_rst_vif.wait_clks(1);
                   end,
                   $sformatf("%0s update_err alert not detected", csr.get_name()))
      `DV_SPINWAIT(cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();,
                   $sformatf("timeout for alert:%0s", alert_name))
    end
  join
endtask

virtual task run_shadow_reg_errors(int num_times);
  dv_base_reg shadowed_csrs[$];

  // Verify that status register fields are set in CFG.
  if (cfg.shadow_update_err_status_fields.size() == 0 ||
      cfg.shadow_storage_err_status_fields.size() == 0) begin
    `uvm_fatal(`gfn, "Please assign shadow reg status register fields in env_cfg!")
  end

  foreach (cfg.ral_models[i]) cfg.ral_models[i].get_shadowed_regs(shadowed_csrs);

  for (int trans = 1; trans <= num_times; trans++) begin
    `uvm_info(`gfn, $sformatf("Running shadow reg error test iteration %0d/%0d", trans,
                              num_times), UVM_LOW)

    shadowed_csrs.shuffle();

    foreach (shadowed_csrs[i]) begin
      repeat(5) begin
        randcase
          1: write_and_check_update_error(shadowed_csrs[i]);
          1: check_csr_read_clear_staged_val(shadowed_csrs[i]);
          1: poke_and_check_storage_error(shadowed_csrs[i]);
        endcase
      end
    end
  end
endtask

// Write shadow register twice with different value and expect a shadow register update alert.
virtual task write_and_check_update_error(dv_base_reg shadowed_csr);
  uvm_reg_data_t wdata, err_wdata;
  string         alert_name = shadowed_csr.get_update_err_alert_name();
  err_wdata = get_shadow_reg_diff_val(shadowed_csr, wdata);
  `DV_CHECK_STD_RANDOMIZE_FATAL(wdata);

  csr_wr(.ptr(shadowed_csr), .value(wdata), .en_shadow_wr(0), .predict(1));

  shadow_reg_wr(shadowed_csr, err_wdata);
  predict_shadow_reg_status(.predict_update_err(1));

  read_check_shadow_reg_status("Write_and_check_update_error task");
  csr_rd_check(.ptr(shadowed_csr), .compare_vs_ral(1));
endtask

// Verifies that a read after the first write to a shadow reg clears the staged value.
//
// Single write to the shadow register followed by a read opeartion.
// Then issue two shadow register writes with the same value.
// Check the read cleared first shadow write by:
// 1). No shadow update alert is triggered the sequence.
// 2). Read and check the register value after the two consective write.
virtual task check_csr_read_clear_staged_val(dv_base_reg shadowed_csr);
  uvm_reg_data_t wdata;
  string         alert_name = shadowed_csr.get_update_err_alert_name();
  `DV_CHECK_STD_RANDOMIZE_FATAL(wdata);

  csr_wr(.ptr(shadowed_csr), .value(wdata), .en_shadow_wr(0), .predict(1));
  csr_rd_check(.ptr(shadowed_csr), .compare_vs_ral(1));
  wdata = get_shadow_reg_diff_val(shadowed_csr, wdata);
  csr_wr(.ptr(shadowed_csr), .value(wdata), .en_shadow_wr(1), .predict(1));

  `DV_CHECK_EQ(cfg.m_alert_agent_cfg[alert_name].vif.get_alert(), 0,
               $sformatf("Unexpected alert: %s fired", alert_name))

  read_check_shadow_reg_status("Check_csr_read_clear_staged_val task");
  csr_rd_check(.ptr(shadowed_csr), .compare_vs_ral(1));
endtask

// Verifies that mismatch of two copies of the internal stored values will trigger fatal alert.
//
// Backdoor write to the `committed` or `shadowed` flops to trigger a storage error.
// Check fatal alert is firing and check any write attempt is blocked.
virtual task poke_and_check_storage_error(dv_base_reg shadowed_csr);
  uvm_reg_data_t  err_val, origin_val, rand_val;
  bkdr_reg_path_e kind;
  int             shadow_reg_width = shadowed_csr.get_msb_pos() + 1;
  string          alert_name = shadowed_csr.get_storage_err_alert_name();

  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
      kind, kind inside {BkdrRegPathRtlCommitted, BkdrRegPathRtlShadow};)
  csr_peek(.ptr(shadowed_csr), .value(origin_val), .kind(kind));
  err_val = get_shadow_reg_diff_val(shadowed_csr, origin_val);

  csr_poke(.ptr(shadowed_csr), .value(err_val), .kind(kind), .predict(1));
  predict_shadow_reg_status(.predict_storage_err(1));
  `uvm_info(`gfn, $sformatf("backdoor write %s through %s with value 0x%0h",
            shadowed_csr.`gfn, kind.name, err_val), UVM_HIGH);

  // This non-blocking task checks if the alert is continuously firing until reset is issued.
  check_fatal_alert_nonblocking(alert_name);

  // Wait random clock cycles and ensure the fatal alert is continuously firing.
  cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

  // Check if CSR write is blocked.
  `DV_CHECK_STD_RANDOMIZE_FATAL(rand_val);
  csr_wr(.ptr(shadowed_csr), .value(rand_val), .en_shadow_wr(1), .predict(0));
  // TODO: Commented out due to issue #7764.
  //csr_rd_check(.ptr(shadowed_csr), .compare_vs_ral(1));

  // Backdoor write back to original value and ensure the fatal alert is continuously firing.
  csr_poke(.ptr(shadowed_csr), .value(origin_val), .kind(kind), .predict(1));

  read_check_shadow_reg_status("Poke_and_check_storage_error task");
  cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

  dut_init();
  read_and_check_all_csrs_after_reset();
endtask

virtual function void predict_shadow_reg_status(bit predict_update_err  = 0,
                                                bit predict_storage_err = 0);
  if (predict_update_err) begin
    foreach (cfg.shadow_update_err_status_fields[status_field]) begin
      void'(status_field.predict(cfg.shadow_update_err_status_fields[status_field]));
    end
  end
  if (predict_storage_err) begin
    foreach (cfg.shadow_storage_err_status_fields[status_field]) begin
      void'(status_field.predict(cfg.shadow_storage_err_status_fields[status_field]));
    end
  end
endfunction

// Verify update and storage error status with RAL mirrored value.
virtual task read_check_shadow_reg_status(string msg_id);
  foreach (cfg.shadow_update_err_status_fields[status_field]) begin
    csr_rd_check(.ptr(status_field), .compare_vs_ral(1),
                 .err_msg($sformatf(" %0s: check update_err status", msg_id)));
  end
  foreach (cfg.shadow_storage_err_status_fields[status_field]) begin
    csr_rd_check(.ptr(status_field), .compare_vs_ral(1),
                 .err_msg($sformatf(" %0s: check storage_err status", msg_id)));
  end
endtask
