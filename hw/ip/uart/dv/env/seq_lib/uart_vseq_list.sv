// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "uart_base_vseq.sv"
`include "uart_tx_rx_vseq.sv"
`include "uart_smoke_vseq.sv"
`include "uart_common_vseq.sv"
`include "uart_fifo_full_vseq.sv"
`include "uart_fifo_overflow_vseq.sv"
`include "uart_fifo_reset_vseq.sv"
`include "uart_rx_oversample_vseq.sv"
`include "uart_intr_vseq.sv"
`include "uart_noise_filter_vseq.sv"
`include "uart_tx_ovrd_vseq.sv"
`include "uart_rx_start_bit_filter_vseq.sv"
`include "uart_rx_parity_err_vseq.sv"
`include "uart_loopback_vseq.sv"
`include "uart_perf_vseq.sv"
`include "uart_long_xfer_wo_dly_vseq.sv"
`include "uart_stress_all_vseq.sv"
