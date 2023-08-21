## Copyright lowRISC contributors.
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0

## Clock Signal
create_clock -add -name sys_clk_pin -period 10.00 -waveform {0 5} [get_ports IO_CLK]

## Rename MMCM outputs for less bug-prone parsing.
## Some auto-derived clocks can have names that include brackets.
create_generated_clock -name clk_main [get_pin clkgen/pll/CLKOUT0]
create_generated_clock -name clk_io_pre [get_pin clkgen/pll/CLKOUT2]
create_generated_clock -name clk_usb_48 [get_pin clkgen/pll/CLKOUT1]
create_generated_clock -name clk_aon [get_pin clkgen/pll/CLKOUT4]

# Create separate sets of clocks for the 48 MHz ext clock tree and the 96 MHz
# I/O clock tree. Then make them physically exclusive, so they don't produce
# invalid combinations.
# The 48 MHz ext clocks all have a _lc suffix.
create_generated_clock -name clk_io -divide_by 1 \
    -source [get_pins u_ast/u_ast_clks_byp/u_no_scan_clk_src_io_d1ord2/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_stepdown/I] \
    [get_pins u_ast/u_ast_clks_byp/u_no_scan_clk_src_io_d1ord2/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_stepdown/O]

set u_div2 top_*/u_clkmgr_aon/u_no_scan_io_div2_div
create_generated_clock -name clk_io_div2 -divide_by 2 \
    -add -master_clock clk_io \
    -source [get_pins u_ast/u_ast_clks_byp/u_no_scan_clk_src_io_d1ord2/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_mux/O] \
    [get_pins ${u_div2}/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_full/O]
set_clock_sense -stop_propagation -clocks clk_io \
    [get_pins ${u_div2}/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_stepdown/I]


set u_div4 top_*/u_clkmgr_aon/u_no_scan_io_div4_div
create_generated_clock -name clk_io_div4 -divide_by 4 \
    -add -master_clock clk_io \
    -source [get_pins u_ast/u_ast_clks_byp/u_no_scan_clk_src_io_d1ord2/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_mux/O] \
    [get_pins ${u_div4}/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_full/O]
set_clock_sense -stop_propagation -clocks clk_io \
    [get_pins ${u_div4}/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_stepdown/I]


create_generated_clock -name clk_io_ext_lc -divide_by 2 \
    -source [get_pins u_ast/u_ast_clks_byp/u_no_scan_clk_src_io_d1ord2/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_full/I] \
    [get_pins u_ast/u_ast_clks_byp/u_no_scan_clk_src_io_d1ord2/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_full/O]

create_generated_clock -name clk_io_div2_ext_lc -divide_by 1 \
    -add -master_clock clk_io_ext_lc \
    -source [get_pins u_ast/u_ast_clks_byp/u_no_scan_clk_src_io_d1ord2/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_mux/O] \
    [get_pins ${u_div2}/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_stepdown/O]

set_clock_sense -stop_propagation -clocks clk_io_ext_lc \
    [get_pins ${u_div2}/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_full/I]

create_generated_clock -name clk_io_div4_ext_lc -divide_by 2 \
    -add -master_clock clk_io_ext_lc \
    -source [get_pins u_ast/u_ast_clks_byp/u_no_scan_clk_src_io_d1ord2/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_mux/O] \
    [get_pins ${u_div4}/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_stepdown/O]

set_clock_sense -stop_propagation -clocks clk_io_ext_lc \
    [get_pin ${u_div4}/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_div_bufg.u_bufg_div_full/I]

set_clock_groups -physically_exclusive \
    -group [get_clocks [list clk_io clk_io_div2 clk_io_div4]] \
    -group [get_clocks [list clk_io_ext_lc clk_io_div2_ext_lc clk_io_div4_ext_lc]]


## USB
# USB input delay to accommodate T_FST (full-speed transition time) and the
# PHY's sampling logic. The PHY expects to only see up to one transient / fake
# SE0. The phase relationship with the PHY's sampling clock is arbitrary, but
# for simplicity, constrain the maximum path delay to something smaller than
# `T_sample - T_FST(max)` to help keep the P/N skew from slipping beyond one
# sample period.
set_input_delay -clock clk_usb_48 -min 3 [get_ports {IO_USB_DP_RX IO_USB_DN_RX IO_USB_D_RX}]
set_input_delay -clock clk_usb_48 -add_delay -max 17 [get_ports {IO_USB_DP_RX IO_USB_DN_RX IO_USB_D_RX}]

# USB output max skew constraint
# Use the output-enable as a "clock" and time the P/N relative to it. Keep the skew within T_FST.
create_generated_clock -name usb_embed_out_clk -multiply_by 1 \
    -source [get_pin clkgen/pll/CLKOUT1] \
    [get_ports IO_USB_OE_N]
set_output_delay -min -clock usb_embed_out_clk 7 [get_ports {IO_USB_DP_TX IO_USB_DN_TX}]
set_output_delay -max -clock usb_embed_out_clk 14 [get_ports {IO_USB_DP_TX IO_USB_DN_TX}] -add_delay

## Muxed I/Os
set ioa_muxed_ports [get_ports IOA*]
set iob_muxed_ports [get_ports IOB*]
set ioc_muxed_ports [get_ports IOC*]
set ior_muxed_ports [get_ports -filter {NAME != IOR8 && NAME != IOR9} IOR*]
set all_muxed_ports "${ioa_muxed_ports} ${iob_muxed_ports} ${ioc_muxed_ports} ${ior_muxed_ports}"

## JTAG clocks and I/O delays
# Create clocks for the various TAPs.
create_clock -add -name jtag_tck -period 100.00 -waveform {0 50} [get_ports IOR3]
create_generated_clock -name lc_jtag_tck -source [get_ports IOR3] -divide_by 1 \
    [get_pins top_*/u_pinmux_aon/u_pinmux_strap_sampling/u_pinmux_jtag_buf_lc/prim_clock_buf_tck/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_fpga_buf.bufg_i/O]
create_generated_clock -name rv_jtag_tck -source [get_ports IOR3] -divide_by 1 \
    [get_pins top_*/u_pinmux_aon/u_pinmux_strap_sampling/u_pinmux_jtag_buf_rv/prim_clock_buf_tck/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_fpga_buf.bufg_i/O]

# Assign input and output delays.
# Note that incidental combinatorial paths through the pinmux do not get removed
# from timing below, but the half cycle timing for JTAG leaves a fairly generous
# requirement. If the JTAG constraints need to be tightened and overly constrain
# the combinational port-to-port paths,
#   set_max_delay -datapath_only
# may be used to apply timing exceptions for those paths.
# However, remember that the input and output delays contribute to the path
# delay for such a case, so the constraint value for set_max_delay must
# accommodate them. In other words, for the constraint
#   set_max_delay -datapath_only -from [get_ports] -through ${combo_path_pin} \
#                 -to [get_ports] ${max_delay_value}
# ${max_delay_value} =
#     ${max_input_delay} + ${max_output_delay} + ${max_port_to_port_delay}
set_output_delay -add_delay -clock jtag_tck -max 10.0 [get_ports IOR1]
set_output_delay -add_delay -clock jtag_tck -min -5.0 [get_ports IOR1]
set_input_delay  -add_delay -clock_fall -clock jtag_tck -min  0.0 [get_ports {IOR0 IOR2}]
set_input_delay  -add_delay -clock_fall -clock jtag_tck -max 15.0 [get_ports {IOR0 IOR2}]

## SPI clocks
set spi_dev_period 50.0
set spi_dev_half_period [expr ${spi_dev_period} / 2]
# Max board skew between signals
set spi_dev_board_skew  0.5
# Max board delay
set spi_dev_board_delay 0.85
# Board skew affects input path for sampling
set spi_dev_in_delay_min [expr -2.0 - ${spi_dev_board_skew}]
set spi_dev_in_delay_max [expr  3.0 + ${spi_dev_board_skew}]
# The board delay affects time remaining on the output path.
set spi_dev_out_hold      -5.0
set spi_dev_out_hold_fc   -3.0
set spi_dev_out_setup     [expr  5.0 + 2 * ${spi_dev_board_delay}]

create_clock -add -name clk_spi  -period ${spi_dev_period} \
    -waveform "0 ${spi_dev_half_period}" [get_ports SPI_DEV_CLK]

create_generated_clock -name clk_spi_in  -divide_by 1 -add \
    -source [get_ports SPI_DEV_CLK] \
    -master_clock [get_clocks clk_spi] \
    [get_pins top_*/u_spi_device/u_clk_spi_in_buf/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_fpga_buf.bufg_i/O]
create_generated_clock -name clk_spi_out -divide_by 1 -invert -add \
    -source [get_ports SPI_DEV_CLK] \
    -master_clock [get_clocks clk_spi] \
    [get_pins top_*/u_spi_device/u_clk_spi_out_buf/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_fpga_buf.bufg_i/O]

set spi_dev_data [get_ports {SPI_DEV_D0 SPI_DEV_D1 SPI_DEV_D2 SPI_DEV_D3}]
set_input_delay -clock clk_spi -clock_fall -min ${spi_dev_in_delay_min} ${spi_dev_data} -add_delay
set_input_delay -clock clk_spi -clock_fall -max ${spi_dev_in_delay_max} ${spi_dev_data} -add_delay

## For half-cycle
#set_output_delay -clock clk_spi -min ${spi_dev_out_hold}  ${spi_dev_data} -add_delay
#set_output_delay -clock clk_spi -max ${spi_dev_out_setup} ${spi_dev_data} -add_delay

## For full-cycle
set_output_delay -clock clk_spi -clock_fall -min ${spi_dev_out_hold_fc} ${spi_dev_data} -add_delay
set_output_delay -clock clk_spi -clock_fall -max ${spi_dev_out_setup}   ${spi_dev_data} -add_delay

# CSB must act as a clock, in addition to data and a reset.
# The waveform is semi-arbitrary: This choice shows that both edges happen near
# the falling edge of clk_spi. The source clock latency constraints then
# function like set_input_delay where SPI_DEV_CS_L acts as data.
create_clock -name clk_spid_csb -period [expr 2 * ${spi_dev_period}] \
    -waveform "${spi_dev_half_period} [expr ${spi_dev_half_period} + ${spi_dev_period}]" \
    [get_ports SPI_DEV_CS_L]
set_clock_latency -source -min ${spi_dev_in_delay_min} [get_ports SPI_DEV_CS_L]
set_clock_latency -source -max ${spi_dev_in_delay_max} [get_ports SPI_DEV_CS_L]

# CSB-clocked status bits to various negedge-triggered flops, especially in the
# serializer.
# Advance the hold edge by one cycle, since CSB changes nominally on the same
# edge as SPI_DEV_OUT_CLK, but SPI_DEV_OUT_CLK isn't actually toggling.
set_multicycle_path -hold -end -from [get_clocks clk_spid_csb] \
    -to [get_clocks clk_spi_out] 1
# Because this section does full-cycle sampling, the same moving of the capture
# edge is needed for SPI_DEV_CSB_CLK -> SPI_DEV_D* hold analysis. The default
# falling edge of SPI_DEV_CLK would not be active.
set_multicycle_path -hold -end -from [get_clocks clk_spid_csb] \
    -to [get_clocks clk_spi] -through [get_ports ${spi_dev_data}] 1
# Relax the hold time constraint for the passthrough clock gate. Really this is
# to accommodate the gate for the inverted clock, which isn't active for the
# modes used for these constraints. However, it would be an okay outcome if the
# filter result reached the gate before even the 7th clock edge got out.
set_multicycle_path -hold -end 1 -from [get_clocks clk_spi] \
    -to [get_pins -filter "DIRECTION == IN && IS_LEAF" -of_objects \
        [get_nets -segments top_earlgrey/u_spi_device/u_passthrough/sck_gate_en]]
# Since this section is for full-cycle sampling, move the capture edge out for
# data driven clk_spi_in. These cases would actually wait for the clk_spi_out
# edge to change the data on the port and get sampled by the host on the next
# clk_spi_out edge.
set_multicycle_path -setup -end 2 -from [get_clocks clk_spi_in] \
    -through [get_ports ${spi_dev_data}] \
    -to [get_clocks clk_spi]
set_multicycle_path -hold -end 2 -from [get_clocks clk_spi_in] \
    -through [get_ports ${spi_dev_data}] \
    -to [get_clocks clk_spi]

## SPI TPM constraints
set spi_tpm_period 100.00
create_clock -add -name clk_spi_tpm -period ${spi_tpm_period} [get_ports SPI_DEV_CLK]

create_generated_clock -name clk_spi_tpm_in -divide_by 1 -add -master_clock clk_spi_tpm \
    -source [get_ports SPI_DEV_CLK] \
    [get_pins top_*/u_spi_device/u_clk_spi_in_buf/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_fpga_buf.bufg_i/O]
create_generated_clock -name clk_spi_tpm_out -divide_by 1 -add -master_clock clk_spi_tpm \
    -source [get_ports SPI_DEV_CLK] \
    [get_pins top_*/u_spi_device/u_clk_spi_out_buf/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_fpga_buf.bufg_i/O] -invert

set_input_delay -clock clk_spi_tpm -clock_fall -min ${spi_dev_in_delay_min} \
    ${spi_dev_data} -add_delay
set_input_delay -clock clk_spi_tpm -clock_fall -max ${spi_dev_in_delay_max} \
    ${spi_dev_data} -add_delay

# TPM CSB
set_input_delay -clock clk_spi_tpm -clock_fall -min ${spi_dev_in_delay_min} \
    [get_ports ${all_muxed_ports}] -add_delay
set_input_delay -clock clk_spi_tpm -clock_fall -max ${spi_dev_in_delay_max} \
    [get_ports ${all_muxed_ports}] -add_delay

# Use half-cycle sampling to comply with TPM spec.
set_output_delay -clock clk_spi_tpm -min ${spi_dev_out_hold}  ${spi_dev_data} -add_delay
set_output_delay -clock clk_spi_tpm -max ${spi_dev_out_setup} ${spi_dev_data} -add_delay

# Relax the hold time constraint for the passthrough clock gate. Really this is
# to accommodate the gate for the inverted clock, which isn't active for the
# modes used for these constraints. However, it would be an okay outcome if the
# filter result reached the gate before even the 7th clock edge got out.
set_multicycle_path -hold -end 1 -from [get_clocks clk_spi_tpm] \
    -to [get_pins -filter "DIRECTION == IN && IS_LEAF" -of_objects \
        [get_nets -segments top_earlgrey/u_spi_device/u_passthrough/sck_gate_en]]


## SPI Passthrough constraints
create_generated_clock -name clk_spi_pt -divide_by 1 -add \
    -source [get_ports SPI_DEV_CLK] \
    -master_clock [get_clocks clk_spi] \
    [get_ports SPI_HOST_CLK]

set spi_pt_data [get_ports {SPI_HOST_D0 SPI_HOST_D1 SPI_HOST_D2 SPI_HOST_D3}]
set spi_host_board_skew 0.5
set spi_host_board_delay 0.85
set spi_host_out_hold      [expr -3.0 - ${spi_host_board_skew}]
set spi_host_out_setup     [expr  3.0 + ${spi_host_board_skew}]
set spi_host_in_delay_min 0
set spi_host_in_delay_max [expr  9.0 + 2 * ${spi_host_board_delay}]

set_output_delay -clock clk_spi_pt -min ${spi_host_out_hold}  ${spi_pt_data} -add_delay
set_output_delay -clock clk_spi_pt -max ${spi_host_out_setup} ${spi_pt_data} -add_delay
set_output_delay -clock clk_spi_pt -min ${spi_host_out_hold}  [get_ports SPI_HOST_CS_L] -add_delay
set_output_delay -clock clk_spi_pt -max ${spi_host_out_setup} [get_ports SPI_HOST_CS_L] -add_delay

set_input_delay  -clock clk_spi_pt -clock_fall -min ${spi_host_in_delay_min} \
    ${spi_pt_data} -add_delay
set_input_delay  -clock clk_spi_pt -clock_fall -max ${spi_host_in_delay_max} \
    ${spi_pt_data} -add_delay

set_multicycle_path -hold 1 -end \
    -from [get_clocks clk_spid_csb] \
    -to [get_clocks clk_spi_pt]

## SPI Host constraints
# SPI Host clock origin buffer
set spi_host_0_peri [get_pins top_earlgrey/u_clkmgr_aon/u_clk_io_peri_cg/gen_xilinx_ultrascale.u_impl_xilinx_ultrascale/gen_gate.u_bufgce/O]

# Even though it's 2x the max possible frequency, keep the peripheral clock
# frequency for the output. This will enable shifting the latch edge for hold
# analysis by the proper amount to effect "half-cycle sampling" of SPI.
create_generated_clock -name clk_spi_host0 -divide_by 2 -add \
  -source ${spi_host_0_peri} \
  -master_clock [get_clocks clk_io] \
  [get_ports SPI_HOST_CLK]

# Multi-cycle path to adjust the hold edge, since launch and capture edges are
# opposite in the SPI_HOST_CLK domain.
set_multicycle_path -setup 1 -start \
    -from [get_clocks -of_objects ${spi_host_0_peri}] \
    -to [get_clocks clk_spi_host0]
set_multicycle_path -hold 1 -start \
    -from [get_clocks -of_objects ${spi_host_0_peri}] \
    -to [get_clocks clk_spi_host0]

# set multicycle path for data going from SPI_HOST_CLK to logic
# the SPI host logic will read these paths at "full cycle"
set_multicycle_path -setup -end 2 \
    -from [get_clocks clk_spi_host0] \
    -to [get_clocks -of_objects ${spi_host_0_peri}]
set_multicycle_path -hold -end 2 \
    -from [get_clocks clk_spi_host0] \
    -to [get_clocks -of_objects ${spi_host_0_peri}]

set spi_host_0_data [get_ports {SPI_HOST_D0 SPI_HOST_D1 SPI_HOST_D2 SPI_HOST_D3 SPI_HOST_CS_L}]
set_output_delay -clock clk_spi_host0 -min ${spi_host_out_hold} \
    ${spi_host_0_data} -add_delay
set_output_delay -clock clk_spi_host0 -max ${spi_host_out_setup} \
    ${spi_host_0_data} -add_delay
set_input_delay  -clock clk_spi_host0 -clock_fall -min ${spi_host_in_delay_min} \
    ${spi_host_0_data} -add_delay
set_input_delay  -clock clk_spi_host0 -clock_fall -max ${spi_host_in_delay_max} \
    ${spi_host_0_data} -add_delay

## Set asynchronous clock groups
set_clock_groups -asynchronous \
    -group clk_main \
    -group {clk_usb_48 usb_embed_out_clk} \
    -group clk_aon \
    -group {clk_io_div2 clk_io_div2_ext_lc} \
    -group {clk_io_div4 clk_io_div4_ext_lc} \
    -group {clk_io_pre clk_io clk_io_ext_lc clk_spi_host0} \
    -group [get_clocks -include_generated_clocks jtag_tck] \
    -group {clk_spi clk_spi_in clk_spi_out clk_spi_pt clk_spid_csb clk_spi_tpm clk_spi_tpm_in clk_spi_tpm_out} \
    -group sys_clk_pin

# TPM and non-TPM modes can't be active simultaneously
set_clock_groups -physically_exclusive \
    -group {clk_spi clk_spi_in clk_spi_out clk_spi_pt clk_spid_csb} \
    -group {clk_spi_tpm clk_spi_tpm_in clk_spi_tpm_out}

# CSB and clocks are not active simultaneously, and CSB does not actually sample
# data from these clocks.
set_clock_groups -logically_exclusive \
    -group {clk_spi clk_spi_tpm} \
    -group {clk_spid_csb}

# CSB to SPI_DEV output enables. Primarily affects generic mode with CPHA=0
# and the first bit.
# Because SPI_DEV_CS_L is a clock pin, various constraint styles will not take.
# Use output delay to constrain the allowed CSB-to-Q outputs.
set spi_dev_csb_clk_q_min -5.0
set spi_dev_csb_clk_q_max 30.0
set spi_dev_csb_out_delay_min [expr 0 - ${spi_dev_csb_clk_q_min}]
set spi_dev_csb_out_delay_max [expr ${spi_dev_period} - ${spi_dev_csb_clk_q_max}]
set_output_delay -clock clk_spid_csb -add_delay -min ${spi_dev_csb_out_delay_min} \
    ${spi_dev_data}
set_output_delay -clock clk_spid_csb -add_delay -max ${spi_dev_csb_out_delay_max} \
    ${spi_dev_data}

# Then mark the paths using other clocks as false paths. CSB does not actually
# sample these clocks.
set_false_path -from [get_clocks {clk_spi_in clk_spi_out clk_spi_pt}] -through ${spi_dev_data} \
    -to [get_clocks clk_spid_csb]

# CSB-clocked status bits to various negedge-triggered flops, especially in the
# serializer. Also may include the path to something for passthrough...
# Advance the hold edge by one cycle, since CSB changes nominally on the same
# edge as clk_spi_out, but clk_spi_out isn't actually toggling.
#set_multicycle_path -hold -end -from [get_clocks clk_spid_csb] \
#    -to [get_clocks clk_spi_out] 1
set_multicycle_path -hold -end -from [get_clocks clk_spi_tpm] \
    -through [get_ports ${all_muxed_ports}] \
    -to [get_clocks clk_spi_tpm_out] 1


## The usb calibration handling inside ast is assumed to be async to the outside world
## even though its interface is also a usb clock.
set_false_path -from [get_clocks clk_usb_48] -to [get_pins u_ast/u_usb_clk/u_ref_pulse_sync/u_sync*/u_sync_1/gen_*/q_o_reg[0]/D]
