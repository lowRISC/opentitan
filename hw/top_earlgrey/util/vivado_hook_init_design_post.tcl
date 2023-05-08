# Load synthesized ILA from checkpoint.
# TODO: This does not load constraints, so there may be timing issues.  Can/should we load the .xci
# file instead?
add_files ../../lowrisc_systems_chip_earlgrey_cw310_0.1.runs/synth_1/lowrisc_systems_chip_earlgrey_cw310_0.1.runs/ila_0_synth_1/ila_0.dcp

# Link design (again) as otherwise the ILA would remain a black box for implementation.
link_design -top chip_earlgrey_cw310 -part xc7k410tfbg676-1
