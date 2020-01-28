// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  // Name of the sim cfg - typically same as the name of the DUT.
  name: ${name}

  // Top level dut name (sv module).
  dut: ${name}

  // Top level testbench name (sv module).
  tb: tb

  // Fusesoc core file used for building the file list.
  fusesoc_core: lowrisc:dv:${name}_sim:0.1

  // Testplan hjson file.
  testplan: "{proj_root}/hw/ip/${name}/data/${name}_testplan.hjson"

  // RAL spec - used to generate the RAL model.
  ral_spec: "{proj_root}/hw/ip/${name}/data/${name}.hjson"

  // Import additional common sim cfg files.
  // TODO: remove imported cfgs that do not apply.
% if is_cip:
  import_cfgs: [// Project wide common sim cfg file
                "{proj_root}/hw/dv/data/common_sim_cfg.hjson",
                // Common CIP test lists
                "{proj_root}/hw/dv/data/tests/csr_tests.hjson",
                "{proj_root}/hw/dv/data/tests/mem_tests.hjson",
% if has_interrupts:
                "{proj_root}/hw/dv/data/tests/intr_test.hjson",
% endif
                "{proj_root}/hw/dv/data/tests/tl_access_tests.hjson",
                "{proj_root}/hw/dv/data/tests/stress_tests.hjson"]
% else:
  import_cfgs: [// Project wide common sim cfg file
                "{proj_root}/hw/dv/data/common_sim_cfg.hjson",
                "{proj_root}/hw/dv/data/tests/csr_tests.hjson",
                "{proj_root}/hw/dv/data/tests/mem_tests.hjson"]
% endif

  // Add additional tops for simulation.
  sim_tops: ["-top {name}_bind"]

  // Default iterations for all tests - each test entry can override this.
  reseed: 50

  // Default UVM test and seq class name.
  uvm_test: ${name}_base_test
  uvm_test_seq: ${name}_base_vseq

  // List of test specifications.
  tests: [
    {
      name: ${name}_sanity
      uvm_test_seq: ${name}_sanity_vseq
    }

    // TODO: add more tests here
  ]
}

