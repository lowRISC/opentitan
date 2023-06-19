// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test randomly injects resets and alert conditions such as:
// - invalid mode configuration values, and
// - life cycle escalation.
class aes_alert_reset_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_alert_reset_vseq)

  `uvm_object_new
  aes_message_item my_message;
  status_t aes_status;
  bit  finished_all_msgs = 0;

  rand bit [$bits(aes_mode_e) -1 : 0]           mal_error;
  rand bit [$bits(lc_ctrl_pkg::lc_tx_t)-1 :0 ]  lc_esc;

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
            if (cfg.flip_rst_lc_esc == Flip_bits) begin
              void'(randomize(mal_error)  with { $countones(mal_error) > 1; });
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
            end else if (cfg.flip_rst_lc_esc == Pull_reset) begin
              // only do reset injection if we are not already
              // injecting other errors (which will pull reset anyway)
              aes_reset();
              #10ps;
              wait(!cfg.under_reset);
            end else if (cfg.flip_rst_lc_esc == Lc_escalate) begin
              if (!(randomize(lc_esc)  with { lc_esc != lc_ctrl_pkg::Off;})) begin
                `uvm_fatal(`gfn, $sformatf("Randomization failes"))
              end
               cfg.lc_escalate_vif.drive({lc_esc,1'b1});
               wait(!cfg.clk_rst_vif.rst_n);
               cfg.lc_escalate_vif.drive('0);
            end
          end
          basic: begin
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
