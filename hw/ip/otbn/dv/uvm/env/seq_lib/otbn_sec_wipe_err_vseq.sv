// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that injects different types of errors into the internal handshake on secure wipes
// between the controller and the start-stop controller.

class otbn_sec_wipe_err_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_sec_wipe_err_vseq)

  `uvm_object_new

  task body();
    typedef enum int {
      ERR_SPURIOUS_REQ,
      ERR_DROPPED_REQ,
      ERR_SPURIOUS_ACK
    } err_type_e;
    err_type_e err_type;

    // Randomize error type.
    `DV_CHECK_STD_RANDOMIZE_FATAL(err_type)

    // Wait for deassertion of reset.
    cfg.clk_rst_vif.wait_for_reset(.wait_negedge(1'b0), .wait_posedge(1'b1));

    case (err_type)
      ERR_SPURIOUS_REQ: begin // Spurious secure wipe request
        string err_path = "tb.dut.u_otbn_core.u_otbn_start_stop_control.secure_wipe_req_i";

        // Secure wipe requests are not allowed when OTBN is idle; so wait for OTBN to become idle.
        wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle);
        @(cfg.clk_rst_vif.cbn);

        // Disable assertion that would abort simulation when the fault is injected.
        $assertoff(0,
            "tb.dut.u_otbn_core.u_otbn_start_stop_control.StartSecureWipeImpliesRunning_A");
        `uvm_info(`gfn, "Requesting secure wipe while OTBN is idle, which is not allowed.", UVM_LOW)

        // Inject error.
        `uvm_info(`gfn, "Injecting error by force.", UVM_LOW)
        `DV_CHECK_FATAL(uvm_hdl_force(err_path, 1'b1) == 1)

        // Let model escalate in next clock cycle.
        @(cfg.clk_rst_vif.cbn);
        cfg.model_agent_cfg.vif.send_err_escalation(32'd1 << 20);

        `uvm_info(`gfn, "Releasing force.", UVM_LOW)
        `DV_CHECK_FATAL(uvm_hdl_release(err_path) == 1)

        `uvm_info(`gfn, "Waiting for OTBN to lock up.", UVM_LOW)
        wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked);
      end

      ERR_DROPPED_REQ: begin // Dropped secure wipe request
        string err_path = "tb.dut.u_otbn_core.u_otbn_start_stop_control.secure_wipe_req_i";
        bit skip_err_injection = 0;

        // The OTBN controller requests a secure wipe from the start-stop controller at the end of
        // execution.  To reach that point, we must first execute a binary.
        string elf_path = pick_elf_path();
        load_elf(elf_path, 1'b1);
        `uvm_info(`gfn, $sformatf("Executing OTBN binary `%0s'.", elf_path), UVM_LOW)
        start_running_otbn(.check_end_addr(1'b0));

        // Wait until binary has completed execution and OTBN does the internal secure wipe.
        `uvm_info(`gfn, "Waiting for OTBN to complete execution.", UVM_LOW)
        wait(cfg.model_agent_cfg.vif.status != otbn_pkg::StatusBusyExecute);
        if (cfg.model_agent_cfg.vif.status != otbn_pkg::StatusBusySecWipeInt) begin
          // If OTBN is no longer executing but also not performing the internal secure wipe, we
          // have missed the opportunity (the `start_running_otbn()` function does not guarantee
          // that it returns while OTBN is still running).  So we cannot inject the error anymore.
          skip_err_injection = 1;
        end
        @(cfg.clk_rst_vif.cbn);

        if (skip_err_injection) begin
          `uvm_info(`gfn, "Skipping error injection.", UVM_LOW)
        end else begin
          // Inject error.
          `uvm_info(`gfn, "Injecting error by force.", UVM_LOW)
          `DV_CHECK_FATAL(uvm_hdl_force(err_path, 1'b0) == 1)

          @(cfg.clk_rst_vif.cbn);

          // Release force, but before doing so disable an assertion that would otherwise abort
          // simulation with a fatal error.
          $assertoff(0,
              "tb.dut.u_otbn_core.u_otbn_start_stop_control.StartSecureWipeImpliesRunning_A");
          `uvm_info(`gfn, "Releasing force.", UVM_LOW)
          `DV_CHECK_FATAL(uvm_hdl_release(err_path) == 1)

          // Let model escalate in next clock cycle.
          @(cfg.clk_rst_vif.cbn);
          cfg.model_agent_cfg.vif.send_err_escalation(32'd1 << 20);

          `uvm_info(`gfn, "Waiting for OTBN to lock up.", UVM_LOW)
          wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked);
        end
      end

      ERR_SPURIOUS_ACK: begin // Spurious secure wipe acknowledge
        string err_path = "tb.dut.u_otbn_core.u_otbn_controller.secure_wipe_ack_i";
        bit skip_err_injection = 0;
        bit while_executing;

        `DV_CHECK_STD_RANDOMIZE_FATAL(while_executing)

        if (while_executing) begin
          // Secure wipe acknowledges are not allowed when OTBN is executing; so load and execute
          // a binary.
          string elf_path = pick_elf_path();
          load_elf(elf_path, 1'b1);
          `uvm_info(`gfn, $sformatf("Executing OTBN binary `%0s'.", elf_path), UVM_LOW)
          start_running_otbn(.check_end_addr(1'b0));
          @(cfg.clk_rst_vif.cbn);

          // If we are unlucky, OTBN is now already securely wiping due to a different error.  In
          // that case, we skip error injection.
          if (cfg.model_agent_cfg.vif.status == otbn_pkg::StatusBusySecWipeInt) begin
            skip_err_injection = 1;
          end
        end else begin
          // Secure wipe acknowledges are not allowed when OTBN is idle; so wait for OTBN to become
          // idle.
          wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusIdle);
          @(cfg.clk_rst_vif.cbn);
        end

        if (skip_err_injection) begin
          `uvm_info(`gfn, "Skipping error injection.", UVM_LOW)
        end else begin
          // Inject error.
          `uvm_info(`gfn, "Injecting error by force.", UVM_LOW)
          `DV_CHECK_FATAL(uvm_hdl_force(err_path, 1'b1) == 1)

          // Let model escalate in next clock cycle.
          @(cfg.clk_rst_vif.cbn);
          cfg.model_agent_cfg.vif.send_err_escalation(32'd1 << 20);

          // Release force.
          `uvm_info(`gfn, "Releasing force.", UVM_LOW)
          `DV_CHECK_FATAL(uvm_hdl_release(err_path) == 1)

          `uvm_info(`gfn, "Waiting for OTBN to lock up.", UVM_LOW)
          wait(cfg.model_agent_cfg.vif.status == otbn_pkg::StatusLocked);
        end
      end

      default: `DV_CHECK_FATAL(0) // This case must never be reached.
    endcase

    reset_if_locked();

  endtask

endclass
