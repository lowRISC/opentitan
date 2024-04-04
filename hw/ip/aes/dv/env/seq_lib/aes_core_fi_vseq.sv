// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test randomly forces critical control signals inside aes_core.sv.
class aes_core_fi_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_core_fi_vseq)

  `uvm_object_new

  localparam bit FORCE   = 0;
  localparam bit RELEASE = 1;

  rand bit [31:0]          force_value;
  rand int                 target;
  rand aes_pkg::aes_ctrl_e await_state;

  task body();

    int if_size;
    bit finished_all_msgs = 0;
    bit wait_for_alert = 0;
    bit wait_for_idle = 0;
    bit forcing = 0;

    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES MAIN SEQUENCE |----\n %s",
                              cfg.convert2string()), UVM_LOW)

    // generate list of messages //
    generate_message_queue();

    // process all messages //
    fork
      error: begin
        // workaround for vcs issue
        if_size = cfg.aes_core_fi_vif.get_if_size();
        `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(target, target inside { [0:if_size - 1]};)
        // We are forcing non one-hot values and the individual targets can have different
        // widths. Determine signal width and whether an alert is expected.
        if (target == 0) begin
          `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(force_value,
              $countones(force_value[aes_pkg::AES_OP_WIDTH-1:0]) > 1;)
          wait_for_alert = 1;
        end else if (target == 1) begin
          `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(force_value,
              $countones(force_value[aes_pkg::AES_OP_WIDTH-1:0]) > 1;)
        end else if (target == 2) begin
          `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(force_value,
              $countones(force_value[aes_pkg::AES_MODE_WIDTH-1:0]) > 1;)
          wait_for_idle = 1;
        end else if (target == 3) begin
          `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(force_value,
              $countones(force_value[aes_pkg::AES_KEYLEN_WIDTH-1:0]) > 1;)
        end else if (target == 4) begin
          `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(force_value,
              $countones(force_value[aes_pkg::AES_PRNGRESEEDRATE_WIDTH-1:0]) > 1;)
        end

        // Wait and apply force.
        if (await_state inside {aes_pkg::CTRL_PRNG_UPDATE, aes_pkg::CTRL_CLEAR_I,
                                      aes_pkg::CTRL_CLEAR_CO}) begin
          // The PRNG Update state and the Clear states are difficult to hit with a random
          // delay.  This writes the clear register to bring the FSM to the PRNG Update and then
          // the Clear states, and it waits until the FSM has reached the required state.
          clear_regs('{dataout: 1'b1, key_iv_data_in: 1'b1, default: 1'b0});
          `DV_WAIT(cfg.aes_core_fi_vif.aes_ctrl_cs == await_state)
        end else if (await_state == aes_pkg::CTRL_PRNG_RESEED) begin
          // The PRNG Reseed state is also difficult to hit with a random delay. This writes the
          // trigger register to bring the FSM into the PRNG Reseed state, and it waits until the
          // FSM has reached that state.
          prng_reseed();
          `DV_WAIT(cfg.aes_core_fi_vif.aes_ctrl_cs == await_state)
        end else if (await_state == aes_pkg::CTRL_LOAD) begin
          // The Load state is also difficult to hit with a random delay, but simply waiting works.
          `DV_WAIT(cfg.aes_core_fi_vif.aes_ctrl_cs == await_state)
        end else begin
          cfg.clk_rst_vif.wait_clks(cfg.inj_delay);
        end
        `uvm_info(`gfn, $sformatf("FORCING %h on target %d", force_value, target), UVM_MEDIUM)
        cfg.aes_core_fi_vif.force_signal(target, FORCE, force_value);
        forcing = 1;

        // Potentially react to the fault.
        if (wait_for_alert) begin
          // The fault is expected to trigger a fatal alert. Ensure this actually happens and
          // release the signal after reset.
          `uvm_info(`gfn, $sformatf("Waiting for alert ack to complete"), UVM_MEDIUM)
          cfg.m_alert_agent_cfgs["fatal_fault"].vif.wait_ack_complete();
          `DV_WAIT(!cfg.clk_rst_vif.rst_n)
          cfg.aes_core_fi_vif.force_signal(target, RELEASE, force_value);
        end else if (wait_for_idle) begin
          // The fault potentially prevents the module from making any progress. DV will try to
          // clear and restart it but might never succeed resulting in the module being idle and
          // again busy.
          csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
          csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b0));
          cfg.aes_core_fi_vif.force_signal(target, RELEASE, force_value);
        end else begin
          // The fault might trigger a reset or not.
          `DV_WAIT(!cfg.clk_rst_vif.rst_n || finished_all_msgs)
          if (!cfg.clk_rst_vif.rst_n) begin
            cfg.aes_core_fi_vif.force_signal(target, RELEASE, force_value);
          end
        end
      end

      basic: begin
        send_msg_queue(cfg.unbalanced, cfg.read_prob, cfg.write_prob);
        finished_all_msgs = 1;
      end

    join
    wait_no_outstanding_access();

  endtask : body
endclass
