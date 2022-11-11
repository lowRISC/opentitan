# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

# Driving from PAD RESET to SPI TPM
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived}                           \
  -expression {(DrivingSignal=~"IO*") && (ReceivingFlop=~"*u_spi_device.u_spi_tpm.*")} \
  -comment {PAD RESET driving to SPI TPM}

set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived}                           \
  -expression {(DrivingSignal=~"SPI_DEV_CS_L*") && (ReceivingFlop=~"*u_spi_device.u_spi_tpm.*")} \
  -comment {PAD RESET driving to SPI TPM}

set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived}                           \
  -expression {(DrivingSignal=~"top_earlgrey.u_pinmux_aon.*strap_sampling*lc_sync*u_sync_2*") && (ReceivingFlop=~"*u_spi_device.u_spi_tpm.*")} \
  -comment {pinmux driving to SPI TPM}

set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived}                           \
  -expression {(DrivingSignal=~"top_earlgrey.u_pinmux_aon.mio_pad_attr_q*") && (ReceivingFlop=~"*u_spi_device.u_spi_tpm.*")} \
  -comment {pinmux driving to SPI TPM}

set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived}                           \
  -expression {(DrivingSignal=~"top_earlgrey.u_pinmux_aon.mio_pad_attr_q*") && (ReceivingFlop=~"*u_spi_device.spi_clk_csb_rst_toggle*")} \
  -comment {pinmux driving to SPI TPM}

set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived}                           \
  -expression {(DrivingSignal=~"top_earlgrey.u_pinmux_aon.mio_pad_attr_q*") && (ReceivingFlop=~"*u_spi_device.spi_clk_csb_rst_toggle*")} \
  -comment {pinmux driving to SPI TPM}

set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived}                           \
  -expression {(DrivingSignal=~"IO*") && (ReceivingFlop=~"*u_spi_device.u_spi_tpm.*")} \
  -comment {PAD RESET driving to SPI TPM}

# Driving from PAD PIN MUX RESET to DMI JTAG
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived}                           \
  -expression {(DrivingSignal=~"top_earlgrey.u_pinmux_aon*") && (ReceivingFlop=~"*u_dmi_jtag.*")} \
  -comment {PAD RESET driving to dmi jtag}

set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"u_ast.*scan*")} -comment {W_ASYNC_RST_FLOPS issues in AST block}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"top_earlgrey.u_pinmux_aon.u_reg.u_mio_periph_insel_46.q*")} -comment {pinmux driving}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"IO*")} -comment {PAD RESET driving}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"SPI_DEV_CS_L") && (ReceivingFlop=~"*u_spi_device.*")} -comment {PAD RESET driving to SPI}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"*.u_pinmux_strap_sampling.*hw_debug_en*.q_o*")} -comment {Tester should ensure no jtag transactions when tap_strap is sampled}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"*.u_pinmux_strap_sampling.*dft_en*.q_o*")} -comment {Tester should ensure no jtag transactions when tap_strap is sampled}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"top_earlgrey.u_pinmux_aon.*io_pad_attr_q*")} -comment {pinmux driving}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"top_earlgrey.u_rstmgr_aon.*.u_rst_sync.u_sync_2.gen_generic.u_impl_generic.q_o*")} -comment {rstmgr driving}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"top_earlgrey.u_rv_dm.u_pm_en_sync.gen_flops.u_prim_flop_2sync.u_sync_2.gen_generic.u_impl_generic.q_o*") && (ReceivingFlop =~ "top_earlgrey.u_rv_dm.dap*")} -comment {rv_dm driving}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"top_earlgrey.u_spi_device.u_reg.u_control*.q*") && (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_fwmode.*")} -comment {spi_tx_fifo driving}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"top_earlgrey.u_spi_device.u_reg.u_control*.q*") && (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_memory_2p.b_rvalid_sram_q*")} -comment {spi_tx_fifo driving}
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} -expression {(DrivingSignal=~"top_earlgrey.*.i_dmi_cdc.u_combined_rstn_sync.u_sync_2.gen_generic.u_impl_generic.q_o*") && (ReceivingFlop =~ "top_earlgrey.*.i_dmi_cdc.i_cdc_resp.fifo_rptr*_q[0]*")} -comment {async reset after jtag mux}
