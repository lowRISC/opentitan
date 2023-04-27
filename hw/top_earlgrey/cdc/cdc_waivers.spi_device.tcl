# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file
# Expression:
#  ControlSignal==""
#  ReconSignal==""
#  MultiClockDomains=="IO_DIV2_CLK::IO_DIV4_CLK"
#

## Waive SPI_DEV clocks <-> SPI_DEV_PASSTHRU clocks

set_rule_status -rule {W_CNTL} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_OUT_CLK,SPI_DEV_PASSTHRU_OUT_CLK::SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}
set_rule_status -rule {W_DATA W_MASYNC} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_OUT_CLK,SPI_DEV_PASSTHRU_OUT_CLK::SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}
set_rule_status -rule {W_CNTL} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::SPI_DEV_OUT_CLK,SPI_DEV_PASSTHRU_OUT_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}
set_rule_status -rule {W_DATA W_MASYNC} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::SPI_DEV_OUT_CLK,SPI_DEV_PASSTHRU_OUT_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}

set_rule_status -rule {W_CNTL} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK::SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}
set_rule_status -rule {W_DATA W_MASYNC} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK::SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}
set_rule_status -rule {W_CNTL} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}
set_rule_status -rule {W_DATA W_MASYNC} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}

set_rule_status -rule {W_CNTL} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK::SPI_DEV_OUT_CLK,SPI_DEV_PASSTHRU_OUT_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}
set_rule_status -rule {W_DATA W_MASYNC} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK::SPI_DEV_OUT_CLK,SPI_DEV_PASSTHRU_OUT_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}
set_rule_status -rule {W_CNTL} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_OUT_CLK,SPI_DEV_PASSTHRU_OUT_CLK::SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}
set_rule_status -rule {W_DATA W_MASYNC} -status {Waived} -expression \
    {(MultiClockDomains == "SPI_DEV_OUT_CLK,SPI_DEV_PASSTHRU_OUT_CLK::SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK")} \
    -comment {Irrelevant clock relationship. Exclusive}

# Asynchronous reset
set_rule_status -rule {W_ASYNC_RST_FLOPS} -status {Waived} \
  -expression {(DrivingSignal=~"*u_spi_device.u_reg.u_control_mode.q*") && \
    (ReceivingFlop=~"*u_spi_device.u_fwmode.*")} \
  -comment {u_control_mode is same clock inside fwmode}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived}            \
   -expression {(ControlSignal=~"*u_status_23_to_1_sync.*") &&     \
                (ReconSignal=~"*u_spid_status.outclk_p2s_byte_*")} \
   -comment {status bits are converged into SPI line. But transmit bit-by-bit. OK to send old and new status bits in a transaction}

set_rule_status -rule {W_CNTL} -status {Waived}          \
   -expression {(Signal=~"*u_spi_device.rxf_full_q*") && \
    (ReceivingFlop=~"*u_spi_device.u_sync_rxf*")}        \
   -comment {2FF synchronizer covers the clock domain crossing. RECONV is not waived.}

# DPSRAM waiver
# DPSRAM B port has clock mux. Unless in SPI Generic mode, B port is in DEV_IN_CLK or SPI_DEV_PASSTHRU_IN_CLK
set_rule_status -rule {W_DATA} -status {Waived} \
  -expression {(ReceivingFlop=~"*u_spi_device.u_memory_2p.u_mem.gen_generic.u_impl_generic.b_rdata_o*") && \
    (MultiClockDomains=="SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK,SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK")} \
  -comment {DPSRAM B port has clock mux. Unless in SPI Generic mode, B port is in DEV_IN_CLK or SPI_DEV_PASSTHRU_IN_CLK}

set_rule_status -rule {W_DATA} -status {Waived} \
  -expression {(ReceivingFlop=~"*u_spi_device.u_memory_2p.*") && \
    (MultiClockDomains == "SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK,SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK")} \
  -comment {DPSRAM runs at SCK in Flash and Passthrough mode}


# FWMode FIFO @ SYS_CLK path
set_rule_status -rule {W_DATA} -status {Waived}                             \
  -expression {(Signal=~"*u_spi_device.u_fwmode.u_*x_fifo.fifo_*ptr*_q*") && \
    (ReceivingFlop=~"*u_spi_device.u_reg.u_reg_if.rdata*")}                  \
  -comment {RD FIFO Read port/ TX FIFO Write port are in SYS_CLK in Generic Mode}

# FWMode: read pointer of rxfifo (SYS -> SYS)
set_rule_status -rule {W_DATA} -status {Waived}                    \
  -expression {(Signal=~"*.u_spi_device.u_reg.u_rxf_ptr_rptr*") && \
    (ReceivingFlop=~"*.u_spi_device.u_fwmode*")}                   \
  -comment {rxf, FwMode sits in SYS_CLK. Synchronous}

# Set from iDebug

set_rule_status -rule {W_CNTL} -expression {(MultiClockDomains == "IO_DIV4_CLK::SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_spid_addr_4b.u_sys2spi_sync.u_sync_1.gen_generic.u_impl_generic.q_o[0]") && (Signal == "top_earlgrey.u_spi_device.u_reg.u_cfg_addr_4b_en.q[0]") && (Association == "Data") && (SyncDepth == "2") && (SyncFlop == "top_earlgrey.u_spi_device.u_spid_addr_4b.u_sys2spi_sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]")} -status {Waived} -lastedit_user {root} -lastedit_time {Thursday, 24 March 2022 13:46:23 PDT} \
  -comment {addr_4b_en signal is static not a pulse signal. No intention of the bit value being changed.}
set_rule_status -rule {W_CNTL} -expression {(MultiClockDomains == "SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_spid_status.u_busy_sync.u_sync_1.gen_generic.u_impl_generic.q_o[0]") && (Signal == "top_earlgrey.u_spi_device.u_spid_status.sck_status_busy") && (Association == "Data") && (SyncDepth == "2") && (SyncFlop == "top_earlgrey.u_spi_device.u_spid_status.u_busy_sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]")} -status {Waived} -lastedit_user {root} -lastedit_time {Thursday, 24 March 2022 13:55:28 PDT} \
  -comment {busy signal is set then stay. 2FF to SYS clock domain is fine}
set_rule_status -rule {W_CNTL} -expression {(MultiClockDomains == "IO_DIV4_CLK::SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_spid_status.u_busy_clr_sync.prim_flop_2sync.u_sync_1.gen_generic.u_impl_generic.q_o[0]") && (Signal == "top_earlgrey.u_spi_device.u_spid_status.u_busy_clr_sync.src_level") && (Association == "Data") && (SyncDepth == "2") && (SyncFlop == "top_earlgrey.u_spi_device.u_spid_status.u_busy_clr_sync.prim_flop_2sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]")} -status {Waived} -lastedit_user {root} -lastedit_time {Thursday, 24 March 2022 14:02:56 PDT}
set_rule_status -rule {W_CNTL} -expression {(MultiClockDomains == "IO_DIV4_CLK::SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_spid_status.u_status_23_to_1_sync.u_sync_1.gen_generic.u_impl_generic.q_o[0]") && (Signal == "top_earlgrey.u_spi_device.u_spid_status.u_busy_sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]") && (Association == "Blocked-Dangling") && (SyncDepth == "2") && (SyncFlop == "top_earlgrey.u_spi_device.u_spid_status.u_status_23_to_1_sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]")} -status {Waived} -lastedit_user {root} -lastedit_time {Thursday, 24 March 2022 14:03:01 PDT}
set_rule_status -rule {W_CNTL} -expression {(MultiClockDomains == "SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_upload.u_payloadptr_clr_psync.prim_flop_2sync.u_sync_1.gen_generic.u_impl_generic.q_o[0]") && (Signal == "top_earlgrey.u_spi_device.u_upload.u_payloadptr_clr_psync.src_level") && (Association == "Data") && (SyncDepth == "2") && (SyncFlop == "top_earlgrey.u_spi_device.u_upload.u_payloadptr_clr_psync.prim_flop_2sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]")} -status {Waived} -lastedit_user {root} -lastedit_time {Thursday, 24 March 2022 14:05:55 PDT}
set_rule_status -rule {W_INTERFACE} -expression {(ComponentClass == "DATA") && (ErrorType == "Uncontrolled-Tx-MASYNC") && (MultiClockDomains == "IO_DIV4_CLK::IO_DIV4_CLK,SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK") && (Signal == "top_earlgrey.u_spi_device.u_reg.u_rxf_ptr_rptr.q[12:2]")} -status {Waived} -lastedit_user {root} -lastedit_time {Thursday, 24 March 2022 14:11:36 PDT}
set_rule_status -rule {W_INTERFACE} -expression {(ComponentClass == "CNTL") && (ErrorType == "") && (MultiClockDomains == "SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK,SPI_DEV_CLK,SPI_DEV_PASSTHRU_CLK") && (Signal == "top_earlgrey.u_spi_device.u_fwmode.u_rx_fifo.fifo_wptr_gray_q[3:0]")} -status {Waived} -lastedit_user {root} -lastedit_time {Thursday, 24 March 2022 14:11:36 PDT}

set_rule_status -rule {W_DATA} -expression {(Signal == "top_earlgrey.u_spi_device.u_fwmode.u_rxf_ctrl.wptr[12:2]") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_reg.u_intr_state_generic_rx_full.q[0]") && (MultiClockDomains == "IO_DIV2_CLK,IO_DIV4_CLK,SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK") && (Association == "None")} -status {Waived} -comment {tool doesn't recognize multiple spi clocks on the same domain}

set_rule_status -rule {W_DATA} -expression {(Signal == "top_earlgrey.u_spi_device.u_fwmode.u_rxf_ctrl.wptr[12:0]") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_reg.u_intr_state_generic_rx_watermark.q[0]") && (MultiClockDomains == "IO_DIV2_CLK,IO_DIV4_CLK,SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK") && (Association == "None")} -status {Waived} -comment {included in waived paths : start signal and receiving signal (flop) have been reviewed and waived in the same error or other errors}
set_rule_status -rule {W_DATA} -expression {(Signal == "top_earlgrey.u_spi_device.u_fwmode.u_txf_ctrl.rptr[12:0]") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_reg.u_intr_state_generic_tx_watermark.q[0]") && (MultiClockDomains == "IO_DIV2_CLK,IO_DIV4_CLK,SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK") && (Association == "None")} -status {Waived} -comment {tool doesn't recognize multiple spi clocks on the same domain}
set_rule_status -rule {W_DATA} -expression {(Signal == "top_earlgrey.u_spi_device.u_fwmode.u_rx_fifo.storage[7:0][7:0]") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_fwmode.u_rx_fifo.rdata_o[7:0]")} -status {Waived} -comment {fwmode uses a special sequence to switch clock}
set_rule_status -rule {W_DATA} -expression {(Signal == "top_earlgrey.u_spi_device.u_fwmode.u_tx_fifo.storage[7:0][7:0]") && (ReceivingFlop == "top_earlgrey.u_spi_device.u_fwmode.u_tx_fifo.rdata_o[7:0]")} -status {Waived} -comment {fwmode uses a special sequence to switch clock}
set_rule_status -rule {W_DATA} -expression {(Signal == "top_earlgrey.u_spi_device.u_fwmode.u_rxf_ctrl.wptr[12:0]") && (ReceivingFlop == "top_earlgrey.u_spi_device.rxlvl") && (MultiClockDomains == "IO_DIV2_CLK,IO_DIV4_CLK,SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK") && (Association == "None")} -status {Waived} -status {Waived} -comment {fwmode uses a special sequence to switch clock}
set_rule_status -rule {W_DATA} -expression {(Signal == "top_earlgrey.u_spi_device.u_fwmode.u_txf_ctrl.rptr[12:0]") && (ReceivingFlop == "top_earlgrey.u_spi_device.txlvl") && (MultiClockDomains == "IO_DIV2_CLK,IO_DIV4_CLK,SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK") && (Association == "None")} -status {Waived} -status {Waived} -comment {fwmode uses a special sequence to switch clock}
set_rule_status -rule {W_DATA} -expression {(Signal == "top_earlgrey.u_spi_device.u_fwmode.u_rxf_ctrl.wptr[12:2]") && (ReceivingFlop == "top_earlgrey.u_spi_device.sram_rxf_full_q") && (MultiClockDomains == "IO_DIV2_CLK,IO_DIV4_CLK,SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK::IO_DIV4_CLK") && (Association == "None")} -status {Waived} -status {Waived} -comment {fwmode uses a special sequence to switch clock}

# Static Config Signals in SPI TPM
set_rule_status -rule {W_DATA} -status {Waived}        \
   -expression {(          \
       (Signal=~"*.u_spi_device.u_reg.u_tpm_did*") ||  \
       (Signal=~"*.u_spi_device.u_reg.u_tpm_int*") ||  \
       (Signal=~"*.u_spi_device.u_reg.u_tpm_rid*")     \
     ) && (MultiClockDomains=="IO_DIV4_CLK::SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK")} \
  -comment {TPM DID/VID/RID, INT_ENABLE, INT_STATUS are static signal. Does not change while in active}

# Static Config (CMD_INFO)
# TODO: Not matched
set_rule_status -rule {W_DATA} -status {Waived}                                       \
  -expression {(Signal =~ "*u_spi_device.u_reg.u_cmd_info*") &&                       \
    ((MultiClockDomains == "IO_DIV4_CLK::SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK") ||  \
     (MultiClockDomains == "IO_DIV4_CLK::SPI_DEV_OUT_CLK,SPI_DEV_PASSTHRU_OUT_CLK"))} \
  -comment {CMD_INFO registers are static value. Configured then stay there}

# TODO: Create more specific Flop instance inside prim_flop_2sync to waive broadly.
set_rule_status -rule {W_CNTL} -status {Waived}            \
   -expression {(Signal=~"*u_spi_device*_*ptr_gray_q*") && \
    (ReceivingFlop=~"*u_spi_device*u_sync_1.*")}           \
   -comment {2FF sync for gray code.}

# Static registers
set_rule_status -rule {W_INTERFACE W_DATA} -status {Waived}     \
  -expression {(Signal =~ "*.u_spi_device.*u_control_mode*") && \
  (MultiClockDomains =~ "IO_DIV4_CLK::*SPI_DEV*CLK*")}          \
  -comment {IO mode control is changed in SPI Idle state}
set_rule_status -rule {W_DATA} -status {Waived}                     \
  -expression {(Signal=~"*.u_spi_device.u_reg.u_control_abort*") && \
    (ReceivingFlop=~"*.u_spi_device.u_fwmode*")}                    \
  -comment {abort -> FwMode sits in SYS_CLK}

set_rule_status -rule {W_INTERFACE W_DATA} -status {Waived}      \
  -expression {(Signal =~ "*.u_spi_device.u_reg*u_cmd_info*") && \
  (MultiClockDomains =~ "IO_DIV4_CLK::*SPI_DEV*CLK*")}           \
  -comment {CMD_INFO is pre-configured, static}
set_rule_status -rule {W_DATA} -status {Waived}             \
  -expression {(Signal =~ "*.u_spi_device.u_reg*u_cmd_info*") && \
  (MultiClockDomains =~ "IO_DIV4_CLK::*SPI_DEV*CLK*")}           \
  -comment {CMD_INFO is pre-configured, static}
set_rule_status -rule {W_DATA} -status {Waived}                      \
  -expression {(Signal =~ "*.u_spi_device.u_reg.u_cfg_*x_order*") && \
  (MultiClockDomains =~ "IO_DIV4_CLK::*SPI_DEV*CLK*")}               \
  -comment {IO mode control is changed in SPI Idle state}

# UNUSED IO_DIV4 clock in Flash/Passthrough mode
set_rule_status -rule {W_DATA} -status {Waived} \
  -expression {(Signal =~ "*u_spi_device*io_mode_outclk*") && \
  (ReceivingFlop =~ "*u_spi_device.u_memory_2p*")} \
  -comment {Other than IO_DIV4_CLK, other clocks are in-phase}

# SPIDEV to pinmux Retention, waived
set_rule_status -rule {W_DATA} -status {Waived} \
  -expression {(Signal =~ "*u_spi_device*") && \
  (ReceivingFlop =~ "*u_pinmux_aon.*retreg_q*")} \
  -comment {retention reg sits in IO_DIV4_CLK, but can be ignored}

# SPI line to registers. Can't add CDC path due to timing

set_rule_status -rule {W_DATA} -status {Waived} \
  -expression {(Signal =~ "SPI_DEV_D*") && \
   (ReceivingFlop =~ "*u_spi_device.u_memory_2p*b_rdata*")} \
  -comment {SPI line cannot have CDC}

# Waive FwMode IO_DIV4 domain
set_rule_status -rule {W_DATA} -status {Waived} \
  -expression {( \
      (ReceivingFlop=~"*u_spi_device.u_fwmode.u_*xf_ctrl.*") || \
      (ReceivingFlop=~"*u_spi_device.u_fwmode.u_tx_fifo.fifo_wptr*") ||   \
      (ReceivingFlop=~"*u_spi_device.u_fwmode.u_rx_fifo.fifo_rptr*") ) && \
    (MultiClockDomains=~"IO_DIV4_CLK::*SPI_DEV_IN_CLK,SPI_DEV_PASSTHRU_IN_CLK")} \
  -comment {?xf_ctrl sits in DIV4, due to clock mux while Generic is not active, tool confused}

# Waive W_G_CLK_GLITCH: When SPI_DEV_CLK toggles, other signals are static
set_rule_status -rule {W_G_CLK_GLITCH} -status {Waived}    \
  -expression {(GatedClock=~"*.u_spi_device.clk_spi_*") || \
    (GatedClock=~"*.u_spi_device.u_sram_clk_*")}           \
  -comment {When SPI_DEV_CLK toggles, other signals are static}
