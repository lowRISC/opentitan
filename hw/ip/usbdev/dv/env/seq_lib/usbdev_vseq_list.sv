// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "usbdev_base_vseq.sv"
`include "usbdev_common_vseq.sv"
`include "usbdev_csr_test_vseq.sv"
`include "usbdev_smoke_vseq.sv"
`include "usbdev_pkt_received_vseq.sv"

`include "usbdev_random_length_out_transaction_vseq.sv"
`include "usbdev_min_length_out_transaction_vseq"
`include "usbdev_max_length_out_transaction_vseq"
`include "usbdev_out_stall_vseq"
`include "usbdev_out_trans_nak_vseq"

