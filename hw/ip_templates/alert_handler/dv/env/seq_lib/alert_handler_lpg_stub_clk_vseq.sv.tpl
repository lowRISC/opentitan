// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence check LPG by randomly turn off ${module_instance_name}'s clock, and check if ping timer can
// resume correctly without sending some spurious ping errors.
class ${module_instance_name}_lpg_stub_clk_vseq extends ${module_instance_name}_lpg_vseq;
  `uvm_object_utils(${module_instance_name}_lpg_stub_clk_vseq)

  `uvm_object_new

  constraint loc_alert_en_c {
    local_alert_en[LocalAlertPingFail] == 1;
    local_alert_en[LocalEscPingFail] == 1;
  }

  constraint ping_fail_c {
    alert_ping_timeout == 0;
    esc_ping_timeout   == 0;
  }

  task body();
    fork begin : isolation_fork
      trigger_non_blocking_seqs();
      fork
        rand_stub_clk();
        run_smoke_seq();
      join
      disable fork; // disable non-blocking seqs for stress_all tests
    end join
  endtask : body

  virtual task rand_stub_clk();
    repeat($urandom_range(1, 5)) begin
      int clk_stub_ps = cfg.clk_rst_vif.clk_period_ps * $urandom_range(2, 1_000);
      cfg.clk_rst_vif.wait_clks($urandom_range(0, 100_000));
      cfg.clk_rst_vif.stop_clk();
      #((clk_stub_ps)*1ps);
      cfg.clk_rst_vif.start_clk();
    end
  endtask

endclass : ${module_instance_name}_lpg_stub_clk_vseq
