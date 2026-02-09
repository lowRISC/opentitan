// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test randomly forces critical control signals inside the GHASH block. The test then checks
// that the DUT triggers a fatal alert and cannot proceed until a reset is triggered.
class aes_ghash_fi_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_ghash_fi_vseq)

  `uvm_object_new
  aes_message_item my_message;
  status_t aes_status;
  bit  finished_all_msgs = 0;
  bit  wait_for_alert_clear = 0;
  bit  wait_for_alert_and_reset = 0;

  localparam bit FORCE   = 0;
  localparam bit RELEASE = 1;

  rand bit [31:0]           force_value;
  rand int                  target;

  rand aes_pkg::aes_ghash_e await_state;

  int                       if_size;


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
            if (!randomize(force_value) with { force_value != '0;}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            // workaround for vcs issue
            if_size = cfg.aes_ghash_fi_vif.get_if_size();
            if (!randomize(target) with {
              target inside { [0:if_size - 1]};}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            if (target == 4) begin
              // Only glitch gcm_phase_i while being in the GHASH_IDLE state. Otherwise, the DUT
              // may endlessly loop through the active states without ever producing an output or
              // signaling an alert.
              await_state = aes_pkg::GHASH_IDLE;
            end else begin
              if (`EN_MASKING) begin
                // The masked implementation doesn't use the GHASH_ADD_S state.
                if (!randomize(await_state)
                    with { await_state inside { aes_pkg::GHASH_IDLE,
                                                aes_pkg::GHASH_MULT,
                                                aes_pkg::GHASH_OUT,
                                                aes_pkg::GHASH_MASKED_INIT,
                                                aes_pkg::GHASH_MASKED_ADD_STATE_SHARES,
                                                aes_pkg::GHASH_MASKED_ADD_CORR,
                                                aes_pkg::GHASH_MASKED_SETTLE};}) begin
                  `uvm_fatal(`gfn, $sformatf("Randomization failed"))
                end
              end else begin
                // The unmasked implementation doesn't use the GHASH_MASKED_* states.
                if (!randomize(await_state)
                    with { await_state inside { aes_pkg::GHASH_IDLE,
                                                aes_pkg::GHASH_MULT,
                                                aes_pkg::GHASH_ADD_S,
                                                aes_pkg::GHASH_OUT};}) begin
                  `uvm_fatal(`gfn, $sformatf("Randomization failed"))
                end
              end
            end
            `DV_WAIT(cfg.aes_ghash_fi_vif.aes_ghash_cs == await_state)
            if (((await_state == aes_pkg::GHASH_IDLE && target != 4) ||
                  await_state == aes_pkg::GHASH_MULT                 ||
                  await_state == aes_pkg::GHASH_MASKED_INIT) &&
                ($urandom_range(0, 4) == 0)) begin
              // These states take multiple clock cycles and it may be interesting to randomly
              // delay the fault injection to not only hit the first cycle in the state.
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
            cfg.aes_ghash_fi_vif.force_signal(target, FORCE, force_value);
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
        cfg.aes_ghash_fi_vif.force_signal(target, RELEASE, force_value);
       `uvm_info(`gfn, $sformatf("Finish"), UVM_MEDIUM)
        disable fork;
      end // fork
    join
  endtask : body
endclass
