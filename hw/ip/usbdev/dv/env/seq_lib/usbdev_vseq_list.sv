// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "usbdev_base_vseq.sv"
`include "usbdev_common_vseq.sv"
`include "usbdev_csr_test_vseq.sv"
`include "usbdev_smoke_vseq.sv"
`include "usbdev_pkt_received_vseq.sv"
`include "usbdev_av_buffer_vseq.sv"
`include "usbdev_setup_trans_ignored_vseq.sv"
`include "usbdev_pkt_sent_vseq.sv"
`include "usbdev_nak_trans_vseq.sv"
`include "usbdev_enable_vseq.sv"
`include "usbdev_in_trans_vseq.sv"
`include "usbdev_random_length_out_transaction_vseq.sv"
`include "usbdev_min_length_out_transaction_vseq.sv"
`include "usbdev_max_length_out_transaction_vseq.sv"
`include "usbdev_out_stall_vseq.sv"
`include "usbdev_out_trans_nak_vseq.sv"
`include "usbdev_fifo_rst_vseq.sv"
`include "usbdev_rx_fifo_vseq.sv"
