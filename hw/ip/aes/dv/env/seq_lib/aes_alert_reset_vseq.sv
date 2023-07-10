// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test randomly injects resets and alert conditions such as:
// - storage errors in the mode field of the shadowed main control register,
// - life cycle escalations, and
// - writes to the alert test CSR.
class aes_alert_reset_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_alert_reset_vseq)

  `uvm_object_new
  aes_message_item my_message;
  status_t aes_status;
  bit finished_all_msgs = 0;
  rand bit [$bits(aes_mode_e)-1:0] mal_error;
  rand bit [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] lc_esc;
  rand alert_test_t alert_test_value;

  task body();

    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES MAIN SEQUENCE |----\n %s",
                              cfg.convert2string()), UVM_LOW)

    // generate list of messages //
    generate_message_queue();

    // process all messages //
    fork
      begin: isolation_fork
        fork
          error: begin
            cfg.clk_rst_vif.wait_clks(cfg.inj_delay);
            if (cfg.alert_reset_trigger == ShadowRegStorageErr) begin
              `uvm_info(`gfn, "Injecting storage error into shadowed main control register",
                  UVM_MEDIUM)
              if (!(randomize(mal_error) with { $countones(mal_error) > 1; })) begin
                `uvm_fatal(`gfn, "Randomization failed")
              end
              if (!uvm_hdl_check_path(
                  "tb.dut.u_aes_core.u_ctrl_reg_shadowed.u_ctrl_reg_shadowed_mode.committed_q"
                  )) begin
                `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
              end else begin
                void'(uvm_hdl_force(
                    "tb.dut.u_aes_core.u_ctrl_reg_shadowed.u_ctrl_reg_shadowed_mode.committed_q",
                    mal_error));
                wait(!cfg.clk_rst_vif.rst_n);
                void'(uvm_hdl_release(
                    "tb.dut.u_aes_core.u_ctrl_reg_shadowed.u_ctrl_reg_shadowed_mode.committed_q"));
              end
            end else if (cfg.alert_reset_trigger == PullReset) begin
              `uvm_info(`gfn, "Pulling reset", UVM_MEDIUM)
              aes_reset();
              #10ps;
              wait(!cfg.under_reset);
            end else if (cfg.alert_reset_trigger == LcEscalate) begin
              `uvm_info(`gfn, "Triggering life cycle escalation", UVM_MEDIUM)
              if (!(randomize(lc_esc) with { lc_esc != lc_ctrl_pkg::Off; })) begin
                `uvm_fatal(`gfn, "Randomization failed")
              end
               cfg.lc_escalate_vif.drive({lc_esc,1'b1});
               wait(!cfg.clk_rst_vif.rst_n);
               cfg.lc_escalate_vif.drive('0);
            end else if (cfg.alert_reset_trigger == AlertTest) begin
              `uvm_info(`gfn, "Writing alert test CSR", UVM_MEDIUM)
              if (!(randomize(alert_test_value) with { $countones(alert_test_value) > 1; })) begin
                `uvm_fatal(`gfn, "Randomization failed")
              end
              csr_wr(.ptr(ral.alert_test), .value(alert_test_value), .blocking(1));
              // Wait to see the actual alert signal. Note that the DUT doesn't block even if the
              // fatal_fault alert has been triggered.
              fork
                wait_for_fatal_alert: begin
                  if (alert_test_value.fatal_fault) begin
                    cfg.m_alert_agent_cfgs["fatal_fault"].vif.wait_ack_complete();
                  end
                end
                wait_for_recov_alert: begin
                  if (alert_test_value.recov_ctrl_update_err) begin
                    cfg.m_alert_agent_cfgs["recov_ctrl_update_err"].vif.wait_ack_complete();
                  end
                end
              join
              // Clear alert test CSR.
              csr_wr(.ptr(ral.alert_test), .value(0), .blocking(1));
            end
          end
          basic: begin
            // Process messages and recover from randomly inserted resets and alert conditions.
            // If required, the DUT is reset to recover from fatal alert conditions.
            send_msg_queue(cfg.unbalanced, cfg.read_prob, cfg.write_prob);
            finished_all_msgs = 1;
          end
        join_none
        // make sure we don't wait for a reset that never comes
        // in case the inject happened efter test finished
        wait (finished_all_msgs);
        wait_no_outstanding_access();
        disable fork;
      end // fork
    join
  endtask : body
endclass
