// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test that injects random resets &
// bit errors into FSMs
class aes_fi_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_fi_vseq)

  `uvm_object_new
  aes_message_item my_message;
  status_t aes_status;
  bit  finished_all_msgs = 0;
  bit  wait_for_alert_clear = 0;
  bit  alert = 0;

  rand bit [StateWidth-1:0] force_state;
  rand int if_num;

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
            // avoid forcing IDLE
            if (!randomize(force_state) with { force_state != 6'b100100;}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            if (!randomize(if_num) with { if_num inside { [0:2] };}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            cfg.clk_rst_vif.wait_clks(cfg.inj_delay);
            `uvm_info(`gfn, $sformatf("FORCING %h on if[%d]", force_state, if_num), UVM_MEDIUM)
            cfg.aes_fi_vif[if_num].force_state(force_state);
            wait_for_alert_clear = 1;
            cfg.m_alert_agent_cfg["fatal_fault"].vif.wait_ack_complete();
            wait(!cfg.clk_rst_vif.rst_n);
            cfg.aes_fi_vif[if_num].release_state();
            wait_for_alert_clear = 0;
          end
          basic: begin
            send_msg_queue(cfg.unbalanced, cfg.read_prob, cfg.write_prob);
            finished_all_msgs = 1;
          end
        join_none
        // make sure we don't wait for a reset that never comes
        // in case the inject happened efter test finished
        wait (finished_all_msgs);
        if (wait_for_alert_clear) begin
          `uvm_fatal(`gfn, $sformatf("Was Able to finish without clearing reset"))
        end
        wait_no_outstanding_access();
        disable fork;
      end // fork
    join
  endtask : body
endclass
