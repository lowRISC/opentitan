// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
{
  // Fusesoc core file used for building the file list.
  fusesoc_core: ${instance_vlnv(f"lowrisc:dv:{module_instance_name}_sim:0.1")}

  // RAL spec - used to generate the RAL model.
  ral_spec: "{self_dir}/../data/${module_instance_name}.hjson"

  // Top level dut module name
  dut: ${module_instance_name}

  // Import the underlying sim_cfg (not templated)
  import_cfgs: ["{proj_root}/hw/ip/racl_ctrl/dv/racl_ctrl_tests.hjson"]
}
