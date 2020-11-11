// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "i2c_base_vseq.sv"
`include "i2c_common_vseq.sv"
`include "i2c_rx_tx_vseq.sv"
`include "i2c_smoke_vseq.sv"

`include "i2c_override_vseq.sv"
`include "i2c_fifo_watermark_vseq.sv"
`include "i2c_fifo_overflow_vseq.sv"
`include "i2c_fifo_full_vseq.sv"
`include "i2c_perf_vseq.sv"
`include "i2c_stretch_timeout_vseq.sv"
`include "i2c_error_intr_vseq.sv"
`include "i2c_stress_all_vseq.sv"
