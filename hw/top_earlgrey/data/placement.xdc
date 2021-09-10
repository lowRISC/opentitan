# While the code below looks messy, it was taken directly from a vivado example
# See here (https://www.xilinx.com/support/answers/66386.html)
# See also this link (https://github.com/lowRISC/opentitan/pull/8138#issuecomment-916696830)
# for a thorough explanation of why such a custom placement helps.
# Note the placement location was not chosen through any systematic means, but through trial
# and error, it may become necessary in the future to tweak this if other congestion
# issues arise.

# Clock net "top_earlgrey/u_clkmgr_aon/u_clk_main_aes_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]" driven by instance "top_earlgrey/u_clkmgr_aon/u_clk_main_aes_cg/gen_xilinx.u_impl_xilinx/gen_gate.gen_bufhce.u_bufhce" located at site "BUFHCE_X1Y0"
#startgroup
create_pblock {CLKAG_top_earlgrey/u_clkmgr_aon/u_clk_main_aes_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]}
add_cells_to_pblock [get_pblocks  {CLKAG_top_earlgrey/u_clkmgr_aon/u_clk_main_aes_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]}] [get_cells -filter { PRIMITIVE_GROUP != I/O && IS_PRIMITIVE==1 && PRIMITIVE_LEVEL !=INTERNAL } -of_object [get_pins -filter {DIRECTION==IN} -of_objects [get_nets -hierarchical -filter {PARENT=="top_earlgrey/u_clkmgr_aon/u_clk_main_aes_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]"}]]]
resize_pblock [get_pblocks {CLKAG_top_earlgrey/u_clkmgr_aon/u_clk_main_aes_cg/gen_xilinx.u_impl_xilinx/clocks_o[clk_main_aes]}] -add {CLOCKREGION_X1Y0:CLOCKREGION_X1Y0}
#endgroup
