// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test that injects random resets &
// bit errors into FSMs
class aes_alert_reset_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_alert_reset_vseq)

  `uvm_object_new
  aes_message_item my_message;
  status_t aes_status;
  bit  finished_all_msgs = 0;

  rand bit [$bits(aes_mode_e) -1 : 0] mal_error;
 // constraint mal_error_c { $countones(mal_error.mode) > 1; };

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
            if (cfg.error_types.mal_inject && (cfg.flip_rst == Flip_bits)) begin
              void'(randomize(mal_error)  with { $countones(mal_error) > 1; });
              if (!uvm_hdl_check_path(
                  "tb.dut.u_aes_core.u_ctrl_reg_shadowed.u_ctrl_reg_shadowed_mode.committed_q"
                  )) begin
                `uvm_fatal(`gfn, $sformatf("\n\t ----| PATH NOT FOUND"))
              end else begin
                $assertoff(0, "tb.dut.u_aes_core.AesModeValid");
                $assertoff(0, "tb.dut.u_aes_core.u_aes_control.AesModeValid");
                void'(uvm_hdl_force(
                    "tb.dut.u_aes_core.u_ctrl_reg_shadowed.u_ctrl_reg_shadowed_mode.committed_q",
                    mal_error));
                wait(!cfg.clk_rst_vif.rst_n);
                void'(uvm_hdl_release(
                    "tb.dut.u_aes_core.u_ctrl_reg_shadowed.u_ctrl_reg_shadowed_mode.committed_q"));
                // turn assertions back on
                $asserton(0, "tb.dut.u_aes_core.AesModeValid");
                $asserton(0, "tb.dut.u_aes_core.u_aes_control.AesModeValid");
              end
            end else if (cfg.error_types.reset && (cfg.flip_rst == Pull_reset)) begin
              // only do reset injection if we are not already
              // injecting other errors (which will pull reset anyway)
              aes_reset();
              #10ps;
              wait(!cfg.under_reset);
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
