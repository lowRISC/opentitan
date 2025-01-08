// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "${module_instance_name}_base_vseq.sv"
`include "${module_instance_name}_smoke_vseq.sv"
`include "${module_instance_name}_common_vseq.sv"
`include "${module_instance_name}_random_alerts_vseq.sv"
`include "${module_instance_name}_random_classes_vseq.sv"
`include "${module_instance_name}_esc_intr_timeout_vseq.sv"
`include "${module_instance_name}_esc_alert_accum_vseq.sv"
`include "${module_instance_name}_sig_int_fail_vseq.sv"
`include "${module_instance_name}_entropy_vseq.sv"
`include "${module_instance_name}_ping_timeout_vseq.sv"
`include "${module_instance_name}_lpg_vseq.sv"
`include "${module_instance_name}_lpg_stub_clk_vseq.sv"
`include "${module_instance_name}_entropy_stress_vseq.sv"
`include "${module_instance_name}_stress_all_vseq.sv"
`include "${module_instance_name}_alert_accum_saturation_vseq.sv"
