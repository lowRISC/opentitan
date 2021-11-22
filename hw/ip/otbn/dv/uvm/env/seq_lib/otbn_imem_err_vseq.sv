// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times and corrupts the
// imem registers while the otbn is still running.

class otbn_imem_err_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_imem_err_vseq)

  `uvm_object_new

  task body();
    string elf_path;
    uvm_reg_data_t act_val;
    bit [38:0] mask;

    logic [127:0]    key;
    logic [63:0]     nonce;

    elf_path = pick_elf_path();
    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, 1'b1);

    // Start OTBN running. When this task returns, we'll be in the middle of a run.
    start_running_otbn(.check_end_addr(1'b0));

    key = cfg.get_imem_key();
    nonce = cfg.get_imem_nonce();

    // Mask to corrupt 1 to 2 bits of the imem memory
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)

    for (int i = 0; i < otbn_reg_pkg::OTBN_IMEM_SIZE / 4; i++) begin
      bit [38:0] good_data = cfg.read_imem_word(i, key, nonce);
      bit [38:0] bad_data = good_data ^ mask;
      cfg.write_imem_word(i, bad_data, key, nonce);
    end

    // We're expecting to see an alert as a result of poking things. We have to allow a large delay,
    // because we might have just started and be still waiting for URND data to come in: OTBN
    // doesn't actually fetch anything until that happens. This isn't as lax as it looks, though. We
    // know that the alert is supposed to go out at the same time as STATUS changes, so can add a
    // timeout there.
    cfg.scoreboard.set_exp_alert(.alert_name("fatal"), .is_fatal(1'b1), .max_delay(100000));

    cfg.model_agent_cfg.vif.invalidate_imem <= 1'b1;
    @(cfg.clk_rst_vif.cb);
    cfg.model_agent_cfg.vif.invalidate_imem <= 1'b0;

    wait (cfg.model_agent_cfg.vif.status != otbn_pkg::StatusBusyExecute);

    // At this point, our status has changed. We're probably actually seeing the alert now, but make
    // sure that it has gone out in at most 10 cycles.
    fork : isolation_fork
      begin
        bit seen_alert = 1'b0;
        fork
          begin
            wait_alert_trigger("fatal", .wait_complete(1));
            seen_alert = 1'b1;
          end
          begin
            repeat (50) @(cfg.m_alert_agent_cfg["fatal"].vif.receiver_cb);
          end
        join_any
        `DV_CHECK_FATAL(seen_alert, "No alert after 50 cycles")
        disable fork;
      end
    join

    fork
      begin
        csr_utils_pkg::csr_rd(.ptr(ral.status), .value(act_val));
        csr_utils_pkg::csr_rd(.ptr(ral.err_bits), .value(act_val));
        csr_utils_pkg::csr_rd(.ptr(ral.fatal_alert_cause), .value(act_val));
      end
      begin
        wait_alert_trigger("fatal", .wait_complete(1));
      end
    join

    dut_init("HARD");

  endtask

endclass
