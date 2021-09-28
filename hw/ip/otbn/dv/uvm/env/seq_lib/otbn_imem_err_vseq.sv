// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence that runs a program multiple times and corrupts the
// imem registers while the otbn is still running.

class otbn_imem_err_vseq extends otbn_base_vseq;
  `uvm_object_utils(otbn_imem_err_vseq)

  `uvm_object_new

  task body();
    int wait_cycles;
    string elf_path;
    uvm_reg_data_t act_val;
    bit [38:0] mask;
    bit timed_out;

    logic [127:0]    key;
    logic [63:0]     nonce;

    elf_path = pick_elf_path();
    `uvm_info(`gfn, $sformatf("Loading OTBN binary from `%0s'", elf_path), UVM_LOW)
    load_elf(elf_path, 1'b1);

    wait_cycles = 1000;
    for (int i = 0; i < 10; i++) begin
      int cycle_counter;
      int err_wait;

      // Guess the number of cycles until error is injected. The first time around, we pick any
      // number between 1 and 1,000. After that, we replace "1,000" with "75% of the longest we've
      // seen the sequence run before terminating". This should avoid problems where we keep
      // injecting errors after the sequence has finished.
      err_wait = $urandom_range(wait_cycles * 3 / 4) + 1;
      fork: isolation_fork
      begin
        fork
          run_otbn(.check_end_addr(0));
          begin
            wait (cfg.model_agent_cfg.vif.status == otbn_pkg::StatusBusyExecute);
            repeat (err_wait) begin
              @(cfg.clk_rst_vif.cbn);
              cycle_counter++;
            end
          end
        join_any

        // When we get here, we know that either the OTBN sequence finished or we timed out
        // and it's still going. We can see whether OTBN is still going by looking at the status
        // from the model (which is also in sync with the RTL). Because we wait on the negedge
        // when updating cycle_counter above, we know we've got the "new version" of the status at
        // this point.
        if (cfg.model_agent_cfg.vif.status == otbn_pkg::StatusBusyExecute) begin
          timed_out = 1'b1;
        end else begin
          timed_out = 1'b0;
          // The OTBN sequence finished so update wait_cycles. cycle_counter should always be less
          // than wait_cycles (because of how we calculate wait cycles).
          `DV_CHECK_FATAL(cycle_counter < wait_cycles);
          wait_cycles = cycle_counter;

          // Wait for the run_otbn thread to finish. This will usually be instant, but might take
          // a couple of cycles if we happen to have timed out exactly at the end of the run (when
          // the status has switched, but before run_otbn finishes)
          wait (!running_);

          // Kill the counter thread
          disable fork;
        end
      end
      join
      if (timed_out) break;
    end

    // The below check is required to ensure that we always inject the errors while the otbn
    // is still running. If timed_out is not asserted within 10 iterations, something has
    // gone wrong and needs debug.
    `DV_CHECK_FATAL(timed_out, "timed_out should be set")

    key = cfg.get_imem_key();
    nonce = cfg.get_imem_nonce();

    // Mask to corrupt 1 to 2 bits of the imem memory
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(mask, $countones(mask) inside {[1:2]};)

    for (int i = 0; i < otbn_reg_pkg::OTBN_IMEM_SIZE / 4; i++) begin
      bit [38:0] good_data = cfg.read_imem_word(i, key, nonce);
      bit [38:0] bad_data = good_data ^ mask;
      cfg.write_imem_word(i, bad_data, key, nonce);
    end

    cfg.model_agent_cfg.vif.invalidate_imem <= 1'b1;
    @(cfg.clk_rst_vif.cb);
    cfg.model_agent_cfg.vif.invalidate_imem <= 1'b0;

    wait (cfg.model_agent_cfg.vif.status != otbn_pkg::StatusBusyExecute);
    wait_alert_trigger("fatal", .wait_complete(1));
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
