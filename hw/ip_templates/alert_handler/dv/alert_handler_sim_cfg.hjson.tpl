// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  // Name of the sim cfg - typically same as the name of the DUT.
  name: alert_handler

  // Top level dut name (sv module).
  dut: alert_handler

  // Top level testbench name (sv module).
  tb: tb

  // Simulator used to sign off this block
  tool: vcs

  // Fusesoc core file used for building the file list.
  fusesoc_core: ${instance_vlnv("lowrisc:dv:alert_handler_sim:0.1")}

  // Testplan hjson file.
  testplan: "{self_dir}/../data/alert_handler_testplan.hjson"

  // Import additional common sim cfg files.
  import_cfgs: [// Project wide common sim cfg file
                "{proj_root}/hw/dv/tools/dvsim/common_sim_cfg.hjson",
                // Common CIP test lists
                "{proj_root}/hw/dv/tools/dvsim/tests/csr_tests.hjson",
                "{proj_root}/hw/dv/tools/dvsim/tests/intr_test.hjson",
                "{proj_root}/hw/dv/tools/dvsim/tests/tl_access_tests.hjson",
                "{proj_root}/hw/dv/tools/dvsim/tests/shadow_reg_errors_tests.hjson",
                "{proj_root}/hw/dv/tools/dvsim/tests/stress_tests.hjson"]

  // Add additional tops for simulation.
  sim_tops: ["alert_handler_bind"]

  // Default iterations for all tests - each test entry can override this.
  reseed: 50

  // Add ALERT_HANDLER specific exclusion files.
  vcs_cov_excl_files: ["{self_dir}/cov/alert_handler_cov_excl.el"]

  // Default UVM test and seq class name.
  uvm_test: alert_handler_base_test
  uvm_test_seq: alert_handler_base_vseq

  // List of test specifications.
  tests: [
    {
      name: alert_handler_smoke
      uvm_test_seq: alert_handler_smoke_vseq
    }

    {
      name: alert_handler_random_alerts
      uvm_test_seq: alert_handler_random_alerts_vseq
    }

    {
      name: alert_handler_random_classes
      uvm_test_seq: alert_handler_random_classes_vseq
    }

    {
      name: alert_handler_esc_intr_timeout
      uvm_test_seq: alert_handler_esc_intr_timeout_vseq
    }

    {
      name: alert_handler_esc_alert_accum
      uvm_test_seq: alert_handler_esc_alert_accum_vseq
    }

    {
      name: alert_handler_sig_int_fail
      uvm_test_seq: alert_handler_sig_int_fail_vseq
    }

    {
      name: alert_handler_entropy
      uvm_test_seq: alert_handler_entropy_vseq
      run_opts: ["+test_timeout_ns=10_000_000_000"]
    }

    {
      name: alert_handler_ping_timeout
      uvm_test_seq: alert_handler_ping_timeout_vseq
    }

    {
      name: alert_handler_lpg
      uvm_test_seq: alert_handler_lpg_vseq
    }

    {
      name: alert_handler_stress_all
      run_opts: ["+test_timeout_ns=15_000_000_000"]
    }

    {
      name: alert_handler_stress_all_with_rand_reset
    }
  ]

  // List of regressions.
  regressions: [
    {
      name: smoke
      tests: ["alert_handler_smoke"]
    }
  ]
}
