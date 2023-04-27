# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

# different PADs on different modes
set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(MultiClockDomains =~ "*::IO_DIV4_CLK") &&      \
  (Signal=~"IO*") && \
  (ReceivingFlop =~ "*u_i2c*.i2c_core.s*_rx_val*")} -comment {IOs muxed by different modes}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(MultiClockDomains =~ "*::IO_DIV4_CLK") &&      \
  (ReceivingFlop =~ "*u_pinmux_aon.mio_out_retreg_q*")} -comment {IOs muxed by different modes}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"IO*") && \
  (ReceivingFlop =~ "*u_pinmux_aon.dio_o*_retreg_q*")} -comment {IOs muxed by different modes}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(MultiClockDomains =~ "IO_CLK::IO_DIV4_CLK") &&      \
  (ReceivingFlop =~ "*u_pinmux_aon.dio_o*_retreg_q*")} -comment {IOs muxed by different modes}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"*u_spi_device.u_reg.u_cmd_filter*filter*.q*") && \
  (ReceivingFlop =~ "*u_spi_device.u_passthrough.cmd_filter*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"*u_spi_device.u_reg.u_cmd_info*.q*") && \
  (ReceivingFlop =~ "*u_spi_device.u_cmdparse.intercept_*_o*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"*u_spi_device.u_reg.u_cmd_info*.q*") && \
  (ReceivingFlop =~ "*u_spi_device.u_cmdparse.st*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"*u_spi_device.u_reg.u_cmd_info*.q*") && \
  (ReceivingFlop =~ "*u_spi_device.*readbuf*sync.src_level*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"*u_spi_device.u_reg.u_cmd_info*.q*") && \
  (ReceivingFlop =~ "*u_spi_device.u_readcmd.u_readbuffer.*buffer_addr*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"*u_spi_device.u_reg.u_cmd_info*.q*") && \
  (ReceivingFlop =~ "*u_spi_device.u_readcmd.u_readbuffer.watermark_crossed*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"*u_spi_device.u_reg.u_cmd_info*.q*") && \
  (ReceivingFlop =~ "*u_spi_device.u_readcmd.readbuf_addr*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"*u_spi_device.u_reg.u_*.*q*") && \
  (ReceivingFlop =~ "*top_earlgrey.u_spi_device.u_memory_2p.b_rvalid_sram_q*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"*u_spi_device.u_readcmd.u_*.*_q*") && \
  (ReceivingFlop =~ "*top_earlgrey.u_spi_device.u_memory_2p.b_rvalid_sram_q*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"SPI_DEV_D*") && \
  (ReceivingFlop =~ "*top_earlgrey.u_spi_device.u_memory_2p.b_rvalid_sram_q*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"SPI_HOST_D*") && \
  (ReceivingFlop =~ "*top_earlgrey.u_spi_host0.u_spi_core.u_shift_reg.*q*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"SPI_*") && \
  (ReceivingFlop =~ "*top_earlgrey.u_pinmux_aon.dio_out_retreg_q*")} -comment {SPI PAD to pinmux}

set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"top_earlgrey.u_spi_host*.q*") && (ReceivingFlop=~"top_earlgrey.u_pinmux_aon.dio_out_retreg_q*")} -comment {multiple source to pinmux}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"top_earlgrey.u_spi_host*.*reg*") && (ReceivingFlop=~"top_earlgrey.u_pinmux_aon.dio_out_retreg_q*")} -comment {multiple source to pinmux}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"top_earlgrey.u_xbar_main.u_asf_*.reqfifo.*q*") && (ReceivingFlop=~"top_earlgrey.u_pinmux_aon.dio_out_retreg_q*")} -comment {multiple source to pinmux}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"top_earlgrey.u_spi_host0.u_spi_core.u_fsm*") && (ReceivingFlop=~"top_earlgrey.u_pinmux_aon.dio_out_retreg_q*")} -comment {multiple source to pinmux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.u_spi_host1.*.q*") && \
  (ReceivingFlop =~ "*top_earlgrey.u_pinmux_aon.mio_oe_retreg_q*")} -comment {SPI host to pinmux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.u_spi_host1.*.*_q*") && \
  (ReceivingFlop =~ "*top_earlgrey.u_pinmux_aon.mio_oe_retreg_q*")} -comment {SPI host to pinmux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"IO*") && \
  (ReceivingFlop =~ "*top_earlgrey.u_lc_ctrl.u_dmi_jtag.i_dmi_jtag_tap.*q*")} -comment {SPI read cmds combined}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.u_spi_device.u_memory_2p.u_mem.gen_generic.u_impl_generic.b_rdata_o*") && \
  (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_fwmode.u_tx_fifo.storage*")} -comment {SPI fwmode mux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.u_spi_device.u_memory_2p.u_mem.gen_generic.u_impl_generic.b_rdata_o*") && \
  (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_fwmode.u_txf_ctrl.sram_rdata_q*")} -comment {SPI fwmode mux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.u_spi_device.u_memory_2p.u_mem.gen_generic.u_impl_generic.b_rdata_o*") && \
  (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_readcmd.p2s_byte_o*")} -comment {SPI readcmd mux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.u_spi_device.u_memory_2p.u_mem.gen_generic.u_impl_generic.b_rdata_o*") && \
  (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_readcmd.u_readsram.u_fifo.gen_normal_fifo.storage*")} -comment {SPI readcmd mux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.u_spi_device.u_memory_2p.u_mem.gen_generic.u_impl_generic.b_rdata_o*") && \
  (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_readcmd.u_readsram.u_sram_fifo.gen_normal_fifo.storage*")} -comment {SPI readcmd mux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.u_spi_device.u_fwmode.u_rx_fifo.sync_wptr.u_sync_2.gen_generic.u_impl_generic.q_o[3:0]") && \
  (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_reg.u_reg_if.rdata*")} -comment {SPI reg mux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"top_earlgrey.u_spi_device.u_fwmode.u_tx_fifo.storage*") && \
  (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_p2s.out_shift*")} -comment {SPI p2s mux}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"u_ast.u_ast_clks_byp.u_clk_src*_sel.clk_*_en_q") && \
  (ReceivingFlop =~ "u_ast.u_ast_clks_byp.u_clk_src_*_sel.clk_*_aoff")} -comment {W_DATA issues in AST block}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"u_ast.u_ast_clks_byp.u_clk_src*_sel.clk_*_sel") && \
  (ReceivingFlop =~ "u_ast.u_ast_clks_byp.all_clks_byp_en_src")} -comment {W_DATA issues in AST block}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"u_ast.u_ast_clks_byp.u_clk_src*_sel.clk_*_aoff") && \
  (ReceivingFlop =~ "u_ast.u_ast_clks_byp.all_clks_byp_en_src")} -comment {W_DATA issues in AST block}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"u_ast.u_ast_clks_byp.u_clk_src*_sel.clk_*_en_q") && \

  (ReceivingFlop =~ "u_ast.u_ast_clks_byp.all_clks_byp_en_src")} -comment {W_DATA issues in AST block}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"u_ast.u_ast_clks_byp.u_clk_src*_sel.clk_ext*") && \
  (ReceivingFlop =~ "u_ast.u_ast_clks_byp.u_clk_src_*_sel.clk_ext_en_q")} -comment {W_DATA issues in AST block}

set_rule_status -rule {W_DATA} -status {Waived} -expression             \
  {(Signal=~"u_ast.u_ast_clks_byp.*_clk_byp_dgl.gen_generic.u_impl_generic.q_o*") && \
  (ReceivingFlop =~ "u_ast.u_ast_clks_byp.u_clk_src_*_sel.clk_*_sel")} -comment {W_DATA issues in AST block}

set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"u_ast.dft_scan_md_o*") && (ReceivingFlop =~ "top_earlgrey.u_clkmgr_aon*_scan*")} -comment {W_DATA issues in AST block}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"top_earlgrey.u_spi_device.u_memory_2p.b_rvalid_sram_q*") && (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_readcmd*")} -comment {W_DATA from 2 port memory}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"top_earlgrey.u_spi_device.u_reg.u_cmd_info_0_valid_0.q*") && (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_cmdparse.intercept_jedec_o*")} -comment {W_DATA from SPI mux}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(ReceivingFlop=~"top_earlgrey.u_pinmux_aon.dio_oe_retreg_q*")} -comment {multiple source to pinmux output}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"IO*") && (ReceivingFlop =~ "u_ast.padmux2ast_i*")} -comment {W_DATA issues in AST block}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"top_earlgrey.u_spi_device.u_reg.u_intercept_en_*") && (ReceivingFlop =~ "top_earlgrey.u_spi_device.u_cmdparse.intercept_jedec_o*")} -comment {W_DATA issues in spi_device jedec}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(ReceivingFlop =~ "top_earlgrey.u_spi_device.u_readcmd.mailbox_assumed_o*")} -comment {Pre-configured, static}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"IO*") && (ReceivingFlop =~ "top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.*_strap_q*")} -comment {W_DATA issues in pinmux dft strap}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(ReceivingFlop=~"top_earlgrey.u_spi_device.u_readcmd.readbuf_addr*")} -comment {multiple source to spi readcmd readbuf}
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"top_earlgrey.u_spi_device.u_reg.*mailbox*.q*")} -comment {demux output from mailbox in spi device }
set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"top_earlgrey.u_spi_device.u_reg.u_intercept_en_*.q*")} -comment {demux output from mailbox in spi device}

set_rule_status -rule {W_DATA} -status {Waived} -expression {(ReceivingFlop=~"top_earlgrey.u_spi_device.u_flash_readbuf_watermark_pulse_sync.src_level*")} -comment {multiple source to readbuf watermark spi_device}

set_rule_status -rule {W_DATA} -status {Waived} -expression {(Signal=~"IO*") && (ReceivingFlop =~ "top_earlgrey.u_spi_host1.u_spi_core.u_shift_reg.rx_buf_q[3:0]*")} -comment {W_DATA issues caused by duplicate clocks on PAD}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_clkmgr_aon*_scan*") && (Signal =~ "top_earlgrey.u_clkmgr_aon.u_no_scan_io_div4_div.*_o") && (Association =~ "None")} -status {Waived} -comment {clock mux}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_clkmgr_aon.u_clkmgr_byp.u_step_down_acks_sync.gen_generic.u_impl_generic.q_o[1]") && (Signal =~ "top_earlgrey.u_clkmgr_aon.u_no_scan_io_div4_div.step_down_ack_o") && (Association =~ "None")} -status {Waived} -comment {clock mux}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_clkmgr_aon.u_clkmgr_byp.u_step_down_acks_sync.gen_generic.u_impl_generic.q_o[0]") && (Signal =~ "top_earlgrey.u_clkmgr_aon.u_no_scan_io_div2_div.gen_div2.step_down_nq") && (Association =~ "None")} -status {Waived} -comment {clock mux}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_spi_device.u_spid_status.u_stage_to_commit.gen_generic.u_impl_generic.q_o[23:0]") && (Signal =~ "top_earlgrey.u_spi_device.u_spid_status.sck_status_staged[23:0]") && (Association =~ "None")} -status {Waived}  -comment {tool doesn't recognize multiple spi clocks on the same domain}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_spi_host1.u_spi_core.u_shift_reg.sd_i_q[3:0]") && (Signal =~ "IOR3") && (Association =~ "None")} -status {Waived} -comment {tool does not recognize duplicate clocks on PAD}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_spi_host1.u_spi_core.u_shift_reg.sr_q[3:0]") && (Signal =~ "IOR3") && (Association =~ "None")} -status {Waived} -comment {tool does not recognize duplicate clocks on PAD}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_spi_device.u_spid_status.outclk_p2s_byte_o*") && (Signal =~ "top_earlgrey.u_spi_device.u_spid_status.u_stage_to_commit.gen_generic.u_impl_generic.q_o*") && (Association =~ "None")} -status {Waived} -comment {tool does not recognize duplicate clocks on PAD}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_spi_device.u_spid_status.sys_status_o[23:0]") && (Signal =~ "top_earlgrey.u_spi_device.u_spid_status.u_stage_to_commit.gen_generic.u_impl_generic.q_o[23:0]") && (Association =~ "None")} -status {Waived} -comment {signal is qualified by synchronized pulse}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_rv_dm.dap.*_q*") && (Signal =~ "top_earlgrey.u_rv_dm.u_pm_en_sync.gen_flops.u_prim_flop_2sync.u_sync_2.gen_generic.u_impl_generic.q_o[3:0]") && (Association =~ "None")} -status {Waived} -comment {signal is synchronized and qualified}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_rv_dm.dap.*_q*") && (Signal =~ "IOR*") && (Association =~ "None")} -status {Waived} -comment  {W_DATA issues caused by duplicate clocks on PAD}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_spi_device.u_spi_tpm.is_*_reg*") && (Signal =~ "top_earlgrey.u_spi_device.u_spi_tpm.sys_clk_tpm_cfg*") && (Association =~ "None")} -status {Waived} -comment {signal is qualified by synchronized pulse}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_spi_device.u_upload.*_cmdfifo_set*") && (Signal =~ "top_earlgrey.u_spi_device.u_upload.*_cmdfifo_set*") && (Association =~ "None")} -status {Waived} -comment {tool doesn't recognize multiple spi clocks on the same domain}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.u_spi_device.u_readcmd.u_readbuffer.watermark_crossed*") && (Signal =~ "top_earlgrey.u_spi_device.u_reg.u_read_threshold.q[9:0]*") && (Association =~ "None")} -status {Waived} -comment {tool doesn't recognize multiple spi clocks on the same domain}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.*.i_dmi_jtag_tap.bypass_q*") && (Signal =~ "top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.u_prim_lc_sender_pinmux_hw_debug_en.gen_flops.u_prim_flop.u_secure_anchor_flop.gen_generic.u_impl_generic.q_o*") && (Association =~ "None")} -status {Waived}  -comment {JTAG mux in quasi-static}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.*.i_dmi_jtag_tap.bypass_q*") && (Signal =~ "top_earlgrey.u_pinmux_aon.mio_pad_attr_q*") && (Association =~ "None")} -status {Waived}  -comment {included in waived paths : start signal and receiving signal (flop) have been reviewed and waived in the same error or other errors} -comment {JTAG mux in quasi-static}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.*.i_dmi_jtag_tap.bypass_q*") && (Signal =~ "top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q*") && (Association =~ "None")} -status {Waived}   -comment {JTAG mux in quasi-static}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "top_earlgrey.*.i_dmi_jtag_tap.bypass_q*") && (Signal =~ "top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.u_prim_lc_sync_lc_dft_en.gen_flops.u_prim_flop_2sync.u_sync_2.gen_generic.u_impl_generic.q_o*") && (Association =~ "None")} -status {Waived}   -comment {JTAG mux in quasi-static}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "u_ast.rng_en_i*") && (Signal =~ "top_earlgrey.u_entropy_src.*") && (Association =~ "None")} -status {Waived}   -comment {Clarified by Nuvoton : ast liberty model does not have a synchronizer}
set_rule_status -rule {W_DATA} -expression {(ReceivingFlop =~ "u_ast.rng_fips_i*") && (Signal =~ "top_earlgrey.u_entropy_src.*") && (Association =~ "None")} -status {Waived}   -comment {Clarified by Nuvoton : ast liberty model does not have a synchronizer}
