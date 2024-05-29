// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "usbdev_base_vseq.sv"
`include "usbdev_common_vseq.sv"

`include "usbdev_smoke_vseq.sv"

`include "usbdev_av_buffer_vseq.sv"
`include "usbdev_bitstuff_err_vseq.sv"
`include "usbdev_csr_test_vseq.sv"
`include "usbdev_data_toggle_restore_vseq.sv"
`include "usbdev_disconnected_vseq.sv"
`include "usbdev_dpi_config_host_vseq.sv"
`include "usbdev_enable_vseq.sv"
`include "usbdev_fifo_rst_vseq.sv"
`include "usbdev_in_rand_trans_vseq.sv"
`include "usbdev_in_stall_vseq.sv"
`include "usbdev_in_trans_vseq.sv"
`include "usbdev_in_iso_vseq.sv"
`include "usbdev_link_in_err_vseq.sv"
`include "usbdev_nak_trans_vseq.sv"
`include "usbdev_out_iso_vseq.sv"
`include "usbdev_out_stall_vseq.sv"
`include "usbdev_out_trans_nak_vseq.sv"
`include "usbdev_pending_in_trans_vseq.sv"
`include "usbdev_phy_config_usb_ref_disable_vseq.sv"
`include "usbdev_phy_pins_sense_vseq.sv"
`include "usbdev_phy_config_eop_single_bit_handling_vseq.sv"
`include "usbdev_pkt_buffer_vseq.sv"
`include "usbdev_pkt_received_vseq.sv"
`include "usbdev_pkt_sent_vseq.sv"
`include "usbdev_random_length_out_transaction_vseq.sv"
`include "usbdev_stall_trans_vseq.sv"
`include "usbdev_rx_crc_err_vseq.sv"
`include "usbdev_setup_trans_ignored_vseq.sv"
`include "usbdev_stall_priority_over_nak_vseq.sv"
`include "usbdev_setup_stage_vseq.sv"

// These depend on usbdev_random_length_out_transaction, so need to come after it.
`include "usbdev_max_length_out_transaction_vseq.sv"
`include "usbdev_min_length_out_transaction_vseq.sv"
// This must follow usbdev_in_trans
`include "usbdev_endpoint_access_vseq.sv"
// This must follow usbdev_pkt_sent
`include "usbdev_link_suspend_vseq.sv"
// This must follow usbdev_link_suspend
`include "usbdev_aon_wake_vseq.sv"
