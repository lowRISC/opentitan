// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test randomly forces critical control signals inside one of the independent, redundant
// logic rails of the cipher core FSM. The test then checks that the DUT triggers a fatal
// alert and cannot proceed until a reset is triggered.
class aes_cipher_fi_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_cipher_fi_vseq)

  `uvm_object_new
  aes_message_item my_message;
  status_t aes_status;
  bit  finished_all_msgs = 0;
  bit  wait_for_alert_clear = 0;
  bit  wait_for_alert_and_reset = 0;

  localparam bit FORCE   = 0;
  localparam bit RELEASE = 1;

  rand bit [31:0]                 force_value;
  rand int                        if_num;
  rand int                        target;

  rand aes_pkg::aes_cipher_ctrl_e await_state;

  int                             if_size;


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
            if (!randomize(force_value) with { force_value != '0;}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            if (!randomize(if_num) with { if_num inside { [0:2] };}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            // workaround for vcs issue
            if_size = cfg.aes_cipher_control_fi_vif[if_num].get_if_size();
            if (!randomize(target) with {
              target inside { [0:if_size - 1]};}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            `DV_CHECK_STD_RANDOMIZE_FATAL(await_state)
            if (await_state inside {aes_pkg::CIPHER_CTRL_CLEAR_S,
                                    aes_pkg::CIPHER_CTRL_CLEAR_KD}) begin
              // The clear states are difficult to hit with a random delay.  This writes the clear
              // register to bring the FSM into the clear state and then waits for the FSM to enter
              // that state.
              clear_regs('{dataout: 1'b1, default: 1'b0});
              `DV_WAIT(cfg.aes_cipher_control_fi_vif[if_num].aes_cipher_ctrl_cs == await_state)
            end else if ((await_state == aes_pkg::CIPHER_CTRL_PRNG_RESEED) && `EN_MASKING) begin
              // The PRNG Reseed state is also difficult to hit with a random delay, and completely
              // unreachable for the unmasked implementation.
              // This writes the trigger register to bring the FSM into the PRNG Reseed state, and
              // waits until the FSM has reached that state.
              prng_reseed();
              `DV_WAIT(cfg.aes_cipher_control_fi_vif[if_num].aes_cipher_ctrl_cs == await_state)
            end else begin
              cfg.clk_rst_vif.wait_clks(cfg.inj_delay);
            end
            if (finished_all_msgs) begin
              // As long as the DUT hasn't finished processing messages yet, the signal forcing
              // will interrupt the message processing. The `basic` thread will notice this and
              // as part of the recovery procedure wait for an alert, reset the DUT and then
              // continue processing messages.
              // Otherwise we have to try to detect the alert and to reset the DUT ourselves.
              wait_for_alert_and_reset = 1;
            end
            `uvm_info(`gfn, $sformatf("FORCING %h on if[%d]", force_value, if_num), UVM_MEDIUM)
            cfg.aes_cipher_control_fi_vif[if_num].force_signal(target, FORCE, force_value);
            wait_for_alert_clear = 1;
            if (wait_for_alert_and_reset) begin
              wait_for_fatal_alert_and_reset();
            end
          end
          basic: begin
            send_msg_queue(cfg.unbalanced, cfg.read_prob, cfg.write_prob);
            finished_all_msgs = 1;
          end
        join_none

        // wait to confirm alert
        wait(wait_for_alert_clear);
        `uvm_info(`gfn, $sformatf("Waiting alert ack complete"), UVM_MEDIUM)
        cfg.m_alert_agent_cfgs["fatal_fault"].vif.wait_ack_complete();
        wait(!cfg.clk_rst_vif.rst_n);
        cfg.aes_cipher_control_fi_vif[if_num].force_signal(target, RELEASE, force_value);
        `uvm_info(`gfn, $sformatf("Finish"), UVM_MEDIUM)
        disable fork;
      end // fork
    join
  endtask : body
endclass
