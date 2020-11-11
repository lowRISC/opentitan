// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "gpio_base_vseq.sv"
`include "gpio_smoke_vseq.sv"
`include "gpio_common_vseq.sv"
`include "gpio_random_dout_din_vseq.sv"
`include "gpio_dout_din_regs_random_rw_vseq.sv"
`include "gpio_intr_rand_pgm_vseq.sv"
`include "gpio_rand_intr_trigger_vseq.sv"
`include "gpio_intr_with_filter_rand_intr_event_vseq.sv"
`include "gpio_filter_stress_vseq.sv"
`include "gpio_random_long_reg_writes_reg_reads_vseq.sv"
`include "gpio_full_random_vseq.sv"
`include "gpio_stress_all_vseq.sv"
