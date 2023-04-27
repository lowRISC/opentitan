# While the code below looks messy, it was taken directly from a vivado example
# See here (https://www.xilinx.com/support/answers/66386.html)
# See also this link (https://github.com/lowRISC/opentitan/pull/8138#issuecomment-916696830)
# for a thorough explanation of why such a custom placement helps.
#
# The placement location has been chosen by evaluating the resulting place and route times of
# all possible options.
#
# The most suitable locations include: X0Y4, X0Y2, X1Y6, X1Y5
# The following locations lead to excessive implementation times: X0Y0, X0Y6, X1Y1
#
# The evaluation has been performed using commit df3c4caee8df70af6b6f3182078ca94ad0022578.
# It may become necessary in the future to tweak this if other congestion issues arise.

# Clock net "top_earlgrey/u_clkmgr_aon/u_clk_main_aes_trans/u_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]" driven by instance "top_earlgrey/u_clkmgr_aon/u_clk_main_aes_trans/u_cg/gen_xilinx.u_impl_xilinx/gen_gate.gen_bufhce.u_bufhce" located at site "BUFHCE_X0Y2"
#startgroup
create_pblock {CLKAG_top_earlgrey/u_clkmgr_aon/u_clk_main_aes_trans/u_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]}
set aes_cells [get_cells -filter { PRIMITIVE_GROUP != I/O && IS_PRIMITIVE==1 && PRIMITIVE_LEVEL !=INTERNAL } -of_object [get_pins -filter {DIRECTION==IN} -of_objects [get_nets -hierarchical -filter {PARENT=="top_earlgrey/u_clkmgr_aon/u_clk_main_aes_trans/u_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]"}]]]
add_cells_to_pblock [get_pblocks  {CLKAG_top_earlgrey/u_clkmgr_aon/u_clk_main_aes_trans/u_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]}] ${aes_cells}
resize_pblock [get_pblocks {CLKAG_top_earlgrey/u_clkmgr_aon/u_clk_main_aes_trans/u_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]}] -add {CLOCKREGION_X0Y2:CLOCKREGION_X0Y2}
#endgroup
