// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "${module_instance_name}_base_vseq.sv"
`include "${module_instance_name}_smoke_vseq.sv"
% if num_inp_period_counters > 0:
`include "${module_instance_name}_inp_prd_cnt_vseq.sv"
% endif
`include "${module_instance_name}_common_vseq.sv"
`include "${module_instance_name}_random_dout_din_vseq.sv"
`include "${module_instance_name}_dout_din_regs_random_rw_vseq.sv"
`include "${module_instance_name}_intr_rand_pgm_vseq.sv"
`include "${module_instance_name}_rand_intr_trigger_vseq.sv"
`include "${module_instance_name}_intr_with_filter_rand_intr_event_vseq.sv"
`include "${module_instance_name}_filter_stress_vseq.sv"
`include "${module_instance_name}_random_long_reg_writes_reg_reads_vseq.sv"
`include "${module_instance_name}_full_random_vseq.sv"
`include "${module_instance_name}_stress_all_vseq.sv"
`include "${module_instance_name}_rand_straps_vseq.sv"
