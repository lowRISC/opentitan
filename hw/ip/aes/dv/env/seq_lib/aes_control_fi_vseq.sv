// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test randomly forces critical control signals inside one of the independent, redundant
// logic rails of the main control FSM. The test then checks that the DUT triggers a fatal
// alert and cannot proceed until a reset is triggered.
class aes_control_fi_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_control_fi_vseq)

  `uvm_object_new
  aes_message_item my_message;
  status_t aes_status;
  bit  finished_all_msgs = 0;
  bit  wait_for_alert_clear = 0;
  bit  alert = 0;

  localparam bit FORCE   = 0;
  localparam bit RELEASE = 1;

  rand bit [31:0]           force_value;
  rand int                  if_num;
  rand int                  target;

  rand aes_pkg::aes_ctrl_e  await_state;

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
            // avoid forcing IDLE
            if (!randomize(force_value) with { force_value != '0;}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            if (!randomize(if_num) with { if_num inside { [0:2] };}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            // workaround for vcs issue
            if_size = cfg.aes_control_fi_vif[if_num].get_if_size();
            if (!randomize(target) with {
              target inside { [0:if_size - 1]};}) begin
              `uvm_fatal(`gfn, $sformatf("Randomization failed"))
            end
            `DV_CHECK_STD_RANDOMIZE_FATAL(await_state)
            if (await_state inside {aes_pkg::CTRL_PRNG_UPDATE, aes_pkg::CTRL_CLEAR_I,
                                          aes_pkg::CTRL_CLEAR_CO}) begin
              // The PRNG Update state and the Clear states are difficult to hit with a random
              // delay.  This writes the clear register to bring the FSM to the PRNG Update and then
              // the Clear states, and it waits until the FSM has reached the required state.
              clear_regs('{dataout: 1'b1, key_iv_data_in: 1'b1, default: 1'b0});
              `DV_WAIT(cfg.aes_control_fi_vif[if_num].aes_ctrl_cs == await_state)
            end else if (await_state inside {aes_pkg::CTRL_LOAD, aes_pkg::CTRL_PRNG_RESEED}) begin
              // The Load state and the PRNG Reseed state are also difficult to hit with a random
              // delay, but for them simply waiting works.
              `DV_WAIT(cfg.aes_control_fi_vif[if_num].aes_ctrl_cs == await_state)
            end else begin
              cfg.clk_rst_vif.wait_clks(cfg.inj_delay);
            end
            `uvm_info(`gfn, $sformatf("FORCING %h on if[%d]", force_value, if_num), UVM_MEDIUM)
            cfg.aes_control_fi_vif[if_num].force_signal(target, FORCE, force_value);
            wait_for_alert_clear = 1;
          end
          basic: begin
            send_msg_queue(cfg.unbalanced, cfg.read_prob, cfg.write_prob);
          end
        join_none

        // wait to confirm alert
        wait(wait_for_alert_clear);
        `uvm_info(`gfn, $sformatf("Waiting alert ack complete"), UVM_MEDIUM)
        cfg.m_alert_agent_cfg["fatal_fault"].vif.wait_ack_complete();
        wait(!cfg.clk_rst_vif.rst_n);
        cfg.aes_control_fi_vif[if_num].force_signal(target, RELEASE, force_value);
       `uvm_info(`gfn, $sformatf("Finish"), UVM_MEDIUM)
        disable fork;
      end // fork
    join
  endtask : body
endclass
