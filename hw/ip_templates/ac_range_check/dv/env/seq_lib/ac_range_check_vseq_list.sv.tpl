// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "${module_instance_name}_base_vseq.sv"
`include "${module_instance_name}_smoke_vseq.sv"
`include "${module_instance_name}_smoke_racl_vseq.sv"
`include "${module_instance_name}_smoke_high_threshold_vseq.sv"
`include "${module_instance_name}_bypass_vseq.sv"
`include "${module_instance_name}_lock_range_vseq.sv"
`include "${module_instance_name}_common_vseq.sv"
`include "${module_instance_name}_stress_all_vseq.sv"
