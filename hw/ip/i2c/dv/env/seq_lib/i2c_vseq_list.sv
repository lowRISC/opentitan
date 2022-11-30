// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "i2c_base_vseq.sv"
`include "i2c_common_vseq.sv"
`include "i2c_rx_tx_vseq.sv"
`include "i2c_host_smoke_vseq.sv"

`include "i2c_host_override_vseq.sv"
`include "i2c_host_fifo_watermark_vseq.sv"
`include "i2c_host_fifo_overflow_vseq.sv"
`include "i2c_host_fifo_reset_fmt_vseq.sv"
`include "i2c_host_fifo_fmt_empty_vseq.sv"
`include "i2c_host_fifo_reset_rx_vseq.sv"
`include "i2c_host_timeout_vseq.sv"
`include "i2c_host_rx_oversample_vseq.sv"
`include "i2c_host_fifo_full_vseq.sv"
`include "i2c_host_perf_vseq.sv"
`include "i2c_host_stretch_timeout_vseq.sv"
`include "i2c_host_error_intr_vseq.sv"
`include "i2c_host_stress_all_vseq.sv"
`include "i2c_target_smoke_vseq.sv"
`include "i2c_target_stress_wr_vseq.sv"
`include "i2c_target_stress_rd_vseq.sv"
`include "i2c_target_stretch_vseq.sv"
`include "i2c_target_tx_ovf_vseq.sv"
`include "i2c_target_timeout_vseq.sv"
