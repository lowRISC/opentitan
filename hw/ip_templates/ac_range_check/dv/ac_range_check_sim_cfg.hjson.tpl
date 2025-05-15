// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  // Name of the sim cfg - typically same as the name of the DUT.
  name: ${module_instance_name}

  // Top level dut name (sv module).
  dut: ${module_instance_name}

  // Top level testbench name (sv module).
  tb: tb

  // Simulator used to sign off this block
  tool: xcelium

  // Fusesoc core file used for building the file list.
  fusesoc_core: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_sim:0.1")}

  // Testplan hjson file.
  testplan: "{self_dir}/../data/${module_instance_name}_testplan.hjson"

  // Import additional common sim cfg files.
  import_cfgs: [// Project wide common sim cfg file
                "{proj_root}/hw/dv/tools/dvsim/common_sim_cfg.hjson",
                // Common CIP test lists
                "{proj_root}/hw/dv/tools/dvsim/tests/csr_tests.hjson",
                "{proj_root}/hw/dv/tools/dvsim/tests/intr_test.hjson",
                "{proj_root}/hw/dv/tools/dvsim/tests/alert_test.hjson",
                "{proj_root}/hw/dv/tools/dvsim/tests/shadow_reg_errors_tests.hjson",
                "{proj_root}/hw/dv/tools/dvsim/tests/tl_access_tests.hjson",
                "{proj_root}/hw/dv/tools/dvsim/tests/sec_cm_tests.hjson", // TODO MVy needed?
                "{proj_root}/hw/dv/tools/dvsim/tests/stress_tests.hjson"]

  // Add additional tops for simulation.
  sim_tops: ["ac_range_check_bind"]

  // Default iterations for all tests - each test entry can override this.
  reseed: 50

  // Default UVM test and seq class name.
  uvm_test: ac_range_check_base_test
  uvm_test_seq: ac_range_check_base_vseq

  // List of test specifications.
  tests: [
    {
      name: ac_range_check_smoke
      uvm_test_seq: ac_range_check_smoke_vseq
    }
    {
      name: ac_range_check_smoke_racl
      uvm_test_seq: ac_range_check_smoke_racl_vseq
    }
    {
      name: ac_range_check_bypass
      uvm_test_seq: ac_range_check_bypass_vseq
    }

    // TODO: add more tests here
  ]

  // List of regressions.
  regressions: [
    {
      name: smoke
      tests: ["ac_range_check_smoke", "ac_range_check_smoke_racl"]
    }
    {
      name: normal
      tests: ["ac_range_check_smoke", "ac_range_check_smoke_racl"]
      reseed: 1000
    }
  ]
}
