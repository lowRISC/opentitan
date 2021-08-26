open_project ../../lowrisc_ibex_top_artya7_0.1.xpr
set saif_name "detailed_power.saif"

open_run impl_1

# Runs a post implementation functional simulation with the memory initialized with SRAMInitFile.
# Feeds clock (100mhz) and reset switch and records switching activity for 3ms.
set_property top top_artya7 [current_fileset sim_1]
launch_simulation -mode post-implementation -type functional
open_saif "$saif_name"
log_saif [get_objects -r *]
add_force {/top_artya7/IO_CLK} -radix bin {1 0ns} {0 5ns} -repeat_every 10ns
add_force {/top_artya7/IO_RST_N} -radix bin {1 0ns}
run 3ms
close_saif


# Reporting power using .saif generated above
open_run impl_1
set_operating_conditions -process maximum
read_saif "../../lowrisc_ibex_top_artya7_0.1.sim/sim_1/impl/func/xsim/$saif_name" 
read_saif "../../lowrisc_ibex_top_artya7_0.1.sim/sim_1/impl/func/xsim/$saif_name"  -strip_path top_artya7 
set_units -power uW
report_power -name {detailed_power_report} -verbose -file post_implementation_power_result.log -hierarchical_depth 20
