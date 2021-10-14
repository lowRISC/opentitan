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
    get_shadow_reg_diff_val[index] = ~get_shadow_reg_diff_val[index];
  end
endfunction

// Wrap this shadow register csr_wr task with predict option so extended IPs can override it with
// their customerized prediction. For example: AES's ctrl_shadow register needs to update `mode`
// and `key_len` fields before calling the RAL predict function.
virtual task csr_wr_for_shadow_reg_predict(dv_base_reg csr, uvm_reg_data_t wdata, bit predict = 1);
  csr_wr(.ptr(csr), .value(wdata), .en_shadow_wr(0), .predict(predict));
endtask

// Alert triggers as soon as design accept the TLUL transaction, if wait until
// csr_wr_for_shadow_reg_predict() finishes then check alert, the alert transaction might already
// finished.
virtual task shadow_reg_wr(dv_base_reg    csr,
                           uvm_reg_data_t wdata,
                           bit            en_shadow_wr = 1,
                           bit            predict = 1);
  // Sequence does not know if this write will trigger update error, so set the initial value to
  // 1 to trigger alert check. Update this value once the write is complete.
  // If no update_err_alert is expected, exit the alert handshake check.
  bit exp_update_err_alert = 1;
  fork
    begin
      repeat (en_shadow_wr ? 2 : 1) csr_wr_for_shadow_reg_predict(csr, wdata, predict);
      exp_update_err_alert = csr.get_shadow_update_err();
    end
    begin
      string alert_name = csr.get_update_err_alert_name();
      // This logic gates alert_handler testbench because it does not have outgoing alert.
      if (cfg.m_alert_agent_cfg.exists(alert_name)) begin
        fork
          begin
            `DV_SPINWAIT(while (!cfg.m_alert_agent_cfg[alert_name].vif.get_alert()) begin
                           cfg.clk_rst_vif.wait_clks(1);
                         end
                         cfg.m_alert_agent_cfg[alert_name].vif.wait_ack_complete();,
                         $sformatf("%0s update_err alert timeout", csr.get_name()))
          end
          begin
            wait (exp_update_err_alert == 0);
          end
        join_any
        disable fork;
      end
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
          1: glitch_shadowed_reset(shadowed_csrs);
        endcase
      end
    end
  end
endtask

virtual task glitch_shadowed_reset(ref dv_base_reg shadowed_csr[$]);
  string alert_name;

  // If any of the shadowed registers have been written with a different value than its reset
  // value, glitch reset pins will trigger alerts.
  foreach (shadowed_csr[i]) begin
    if (shadowed_csr[i].get_reset() != `gmv(shadowed_csr[i])) begin
      alert_name = shadowed_csr[i].get_storage_err_alert_name();
      predict_shadow_reg_status(.predict_storage_err(1));
      `uvm_info(`gfn, $sformatf("Expect reset storage error %0s", shadowed_csr[i].get_name()),
                UVM_HIGH)
      break;
    end
  end

  // Randomly choose to glitch `rst_n` or `shadowed_rst_n` pin.
  if ($urandom_range(0, 1)) begin
    cfg.rst_shadowed_vif.drive_shadow_rst_pin(0);
    `uvm_info(`gfn, "toggle shadow reset pin", UVM_HIGH)
  end else begin
    cfg.rst_shadowed_vif.drive_shadow_rst_pin(1);
    dut_init();
  end

  // Check if shadow reset will trigger fatal storage error.
  //
  // - First check if alert_name exists in alert_agent_cfg because alert_handler IP won't trigger
  // external alert, it triggers it as a local alert instead.
  // - Wait for the first alert to trigger then check if the alert is firing continuously, because
  // `dut_init` is a blocking task and alert is firing once alert_init is done.
  if (cfg.m_alert_agent_cfg.exists(alert_name) && alert_name != "") begin
    `DV_SPINWAIT(while (!cfg.m_alert_agent_cfg[alert_name].vif.get_alert())
                 cfg.clk_rst_vif.wait_clks(1);,
                 $sformatf("expect fatal alert:%0s to fire after rst_ni glitched", alert_name))
    check_fatal_alert_nonblocking(alert_name);
  end

  // Wait for random cycles and reconnect `shadowed_rst_n` with `rst_n`.
  cfg.clk_rst_vif.wait_clks($urandom_range(50, 200));
  cfg.rst_shadowed_vif.reconnect_shadowed_rst_n_to_rst_n();
  if (alert_name != "") begin
    dut_init();
    read_check_shadow_reg_status("Glitch_shadow_reset_pin task");
  end
endtask

// Write shadow register twice with different value and expect a shadow register update alert.
virtual task write_and_check_update_error(dv_base_reg shadowed_csr);
  uvm_reg_data_t wdata, err_wdata;
  string         alert_name = shadowed_csr.get_update_err_alert_name();
  `DV_CHECK_STD_RANDOMIZE_FATAL(wdata);
  err_wdata = get_shadow_reg_diff_val(shadowed_csr, wdata);

  shadow_reg_wr(.csr(shadowed_csr), .wdata(wdata), .en_shadow_wr(0));

  shadow_reg_wr(.csr(shadowed_csr), .wdata(err_wdata), .en_shadow_wr(0));
  // If the shadow register is external register, writing two different value might not actually
  // trigger update error. So we trigger dv_base_reg function to double check.
  predict_shadow_reg_status(.predict_update_err(shadowed_csr.get_shadow_update_err()));
  `uvm_info(`gfn, $sformatf("write %0s with first value %0h second value %0h",
            shadowed_csr.get_name(), wdata, err_wdata), UVM_HIGH);

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

  `uvm_info(`gfn, $sformatf("%0s check csr read clear", shadowed_csr.get_name()), UVM_HIGH);
  shadow_reg_wr(.csr(shadowed_csr), .wdata(wdata), .en_shadow_wr(0));
  csr_rd_check(.ptr(shadowed_csr), .compare_vs_ral(1));
  wdata = get_shadow_reg_diff_val(shadowed_csr, wdata);
  shadow_reg_wr(.csr(shadowed_csr), .wdata(wdata), .en_shadow_wr(1));

  if (cfg.m_alert_agent_cfg.exists(alert_name)) begin
    `DV_CHECK_EQ(cfg.m_alert_agent_cfg[alert_name].vif.get_alert(), 0,
                 $sformatf("Unexpected alert: %s fired", alert_name))
  end

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
      kind, kind inside {BkdrRegPathRtl, BkdrRegPathRtlShadow};)
  csr_peek(.ptr(shadowed_csr), .value(origin_val), .kind(kind));
  err_val = get_shadow_reg_diff_val(shadowed_csr, origin_val);

  csr_poke(.ptr(shadowed_csr), .value(err_val), .kind(kind), .predict(1));
  predict_shadow_reg_status(.predict_storage_err(shadowed_csr.get_shadow_storage_err()));
  `uvm_info(`gfn, $sformatf("backdoor write %s through %s with value 0x%0h",
            shadowed_csr.`gfn, kind.name, err_val), UVM_HIGH);

  // This non-blocking task checks if the alert is continuously firing until reset is issued.
  if (cfg.m_alert_agent_cfg.exists(alert_name)) check_fatal_alert_nonblocking(alert_name);

  // Wait random clock cycles and ensure the fatal alert is continuously firing.
  cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

  // Check if CSR write is blocked.
  `DV_CHECK_STD_RANDOMIZE_FATAL(rand_val);
  shadow_reg_wr(.csr(shadowed_csr), .wdata(rand_val), .en_shadow_wr(1));
  csr_rd_check(.ptr(shadowed_csr), .compare_vs_ral(1));

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
