# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Meridian RDC Waivers for SPI_DEVICE
#

# W_RST_COMBO_LOGIC
# rst_rx/txfifo signals are reset signals but also returns data to SW. it is
# recognized as combo reset by tool but reset line is OK.
# TODO: Add buffer to separate other logics from reset
set_rule_status -rule {W_RST_COMBO_LOGIC} -status {Waived}  \
  -expression {(SourceReset=~"*.u_spi_device.u_reg.u_control_rst_*xfifo.q*")} \
  -comment {rst_rx,txfifo are reset signals directly connected to the registers.q}

set_rule_status -rule {W_RST_COMBO_LOGIC} -status {Waived} \
  -expression {(SourceReset=~"*.u_spi_device.rst_*_buf")}  \
  -comment {rst csb, tpm_csb are reset merging with scan chain.}


# RDC could not catch the relation between CSb and SCK. (SCK negedge to CSb
# de-assertion shall take 5ns at minimum)
#
# However, if CSb mis-behaved, the logic may/maynot push entries to CMDADDR
# FIFO and WR FIFO.
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(MetaStableFlop=~"*.u_spi_tpm.u_cmdaddr_buffer.fifo_wptr*")} \
  -comment {when csb de-asserted, SCK should be quiescent. If not, the behavior is unpredictable}

set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(MetaStableFlop=~"*.u_spi_tpm.u_wrfifo.fifo_wptr*")} \
  -comment {when csb de-asserted, SCK should be quiescent. If not, the behavior is unpredictable}

# TODO(#15886): Find better env setup to define the relation between CSb and
#               all SCK generated clocks.
# CSb to RX/TX FIFOs pointers E_RST_METASTABILITY
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.rst_csb_buf") && \
    (ResetFlop=~"*u_spi_device.io_mode_outclk*") && \
    (MetaStableFlop=~"*u_spi_device.u_fwmode.u_*x_fifo.fifo_*ptr*")} \
  -comment {CSb does not conflict to SPI_CLK if host system follows the protocol}

# Rx/Tx FIFO resets are issued when SPI is idle.
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.u_reg.u_control_rst_rxfifo*") && \
    (MetaStableFlop=~"*u_spi_device.u_fwmode.u_rxf_ctrl.*")} \
  -comment {Assumption is to reset RX/TX FIFO when SPI is idle}
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.u_reg.u_control_rst_rxfifo*") && \
    (MetaStableFlop=~"*u_spi_device.rxf_full_q")} \
  -comment {Assumption is to reset RX/TX FIFO when SPI is idle}
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.u_reg.u_control_rst_*xfifo*") && \
    (ResetFlop=~"*u_spi_device.u_fwmode.u_rx_fifo.fifo_rptr_q*") && \
    (MetaStableFlop=~"*u_spi_device.u_reg.u_reg_if.rdata_q*")} \
  -comment {Assumption is to reset RX/TX FIFO when SPI is idle. \
    SW reads FIFO PTR not at the same time.}
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.u_reg.u_control_rst_*xfifo*") && \
    (MetastableFlopReset=~"*u_spi_device.u_reg.u_control_mode.q*")} \
  -comment {CONTROL.mode dose not change.}
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.u_reg.u_control_rst_txfifo*") && \
    (MetaStableFlop=~"*u_spi_device.txf_empty_q")} \
  -comment {Assumption is to reset RX/TX FIFO when SPI is idle}
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.u_reg.u_control_rst_*xfifo*") && \
    (ResetFlop=~"*u_spi_device.u_fwmode.u_tx_fifo.fifo_rptr_*") && \
    (MetaStableFlop=~"*u_spi_device.u_reg.u_reg_if.rdata_q*")} \
  -comment {Assumption is to reset RX/TX FIFO when SPI is idle. \
    SW reads FIFO PTR not at the same time.}
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.u_reg.u_control_rst_*xfifo*") && \
    (ResetFlop=~"*u_spi_device.u_fwmode.u_tx_fifo.fifo_rptr_q*") && \
    (MetaStableFlop=~"*u_spi_device.u_p2s.out_shift*")} \
  -comment {Assumption is to reset RX/TX FIFO when SPI is idle. \
    SW reads FIFO PTR not at the same time.}

set_rule_status -rule {E_RDC_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.u_reg.u_control_rst_txfifo*") && \
    (ResetFlop=~"*u_spi_device.u_fwmode.u_tx_fifo.fifo_rptr*") && \
    (MetaStableFlop=~"*u_spi_device.u_fwmode.u_tx_fifo.storage*")} \
  -comment {TXFIFO reset may cause the output data change (surely). \
    RDC reports the RDC_METASTABILITY caused by this. \
    To avoid the issue, rst_sync + data sync should be implemented. \
    However, due to the lack of the SCK, rst_sync cannot be added.}

# CSb to Any SPI_CLK path (RDC could not figure out the relation between CSb and SPI_CLK)
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.rst_csb_buf") && \
    (ClockDomains=~"SPI_DEV_*_CLK::SPI_DEV_*_CLK")} \
  -comment {RDC does not correctly relate CSB and SCK domains}
# Below waiver is from CSb to Passthrough SCK clock gating logic.
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.rst_csb_buf") && \
    (ClockDomains=~"SPI_DEV_*_CLK::SPI_DEV_CLK")} \
  -comment {RDC does not correctly relate CSB and SCK domains}

# CONTROL.mode CSR does not change when CSb toggles
set_rule_status -rule {E_RDC_METASTABILITY} -status {Waived} \
  -expression {(SourceReset=~"*u_spi_device.rst_csb_buf") && \
    (ObservableFlopReset=~"*u_reg.u_control_mode*")} \
  -comment {CONTROL.mode is configured at the init time.}


# CPHA, CONTROL.mode waivers for main rst
set_rule_status -rule {E_RST_METASTABILITY E_RDC_METASTABILITY} \
  -status {Waived} \
  -expression {(ResetFlop=~"*u_spi_device.u_reg.u_cfg_cp*") && \
    (ClockDomains=="IO_DIV4_CLK::IO_DIV4_CLK")}\
  -comment {If CPHA is set, MainReset, SwRsqRst, POK reset causes a single \
    edge to SPI_DEV_IN or SPI_DEV_OUT clock. As the edge occurs at the same \
    time with the IP reset, it may create metastability issue to many \
    registers inside SPI_DEVICE IP. \
    \
    However, at the time when POR is released, or SW requsts the reset, SPI \
    is assumes as quiescent or stalled. If SPI line is stalled, part of the \
    internal content may not be reset. But, it can be solvable by setting \
    invert to the CSb pad. \
    }
