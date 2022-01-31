// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "chip_callback_vseq.sv"
`include "chip_base_vseq.sv"
`include "chip_stub_cpu_base_vseq.sv"
`include "chip_common_vseq.sv"
`include "chip_jtag_csr_rw_vseq.sv"
// This needs to be listed prior to all sequences that derive from it.
`include "chip_sw_base_vseq.sv"
`include "chip_sw_full_aon_reset_vseq.sv"
`include "chip_sw_main_power_glitch_vseq.sv"
`include "chip_sw_uart_tx_rx_vseq.sv"
`include "chip_sw_uart_rand_baudrate_vseq.sv"
`include "chip_sw_gpio_smoke_vseq.sv"
`include "chip_sw_gpio_vseq.sv"
`include "chip_sw_flash_ctrl_lc_rw_en_vseq.sv"
`include "chip_sw_lc_ctrl_transition_vseq.sv"
`include "chip_sw_spi_tx_rx_vseq.sv"
`include "chip_sw_rom_ctrl_integrity_check_vseq.sv"
`include "chip_sw_sram_ctrl_execution_main_vseq.sv"
`include "chip_sw_sram_ctrl_scrambled_access_vseq.sv"
`include "chip_sw_pwm_pulses_vseq.sv"
`include "chip_sw_keymgr_key_derivation_vseq.sv"
