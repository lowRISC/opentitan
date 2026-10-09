# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Setup hook scripts, to be called at various stages during the build process
# See Xilinx UG 894 ("Using Tcl Scripting") for documentation.

# fusesoc-generated workroot containing the Vivado project file
set workroot [pwd]

# Pre synthesize design hook
set_property STEPS.SYNTH_DESIGN.TCL.PRE "${workroot}/vivado_hook_synth_design_pre.tcl" [get_runs synth_1]

# Pre implementation (init design) post hook
set_property STEPS.INIT_DESIGN.TCL.POST "${workroot}/vivado_hook_init_design_post.tcl" [get_runs impl_1]

# Post opt design hook
set_property STEPS.OPT_DESIGN.TCL.POST "${workroot}/vivado_hook_opt_design_post.tcl" [get_runs impl_1]

# TODO: This hook is not getting called by Vivado when running through our
# fusesoc flow (it gets called when writing a bitstream through the GUI).
# Requires an update to edalize, see https://github.com/olofk/edalize/pull/60.
#set_property STEPS.WRITE_BITSTREAM.TCL.PRE "${workroot}/vivado_hook_write_bitstream_pre.tcl" [get_runs impl_1]

# As workaround, we use the post route design hook, which gets called.
set_property STEPS.ROUTE_DESIGN.TCL.POST "${workroot}/vivado_hook_write_bitstream_pre.tcl" [get_runs impl_1]

# Abort if a constraint matches no object, in all runs.
set_msg_config -id {[Vivado 12-4739]} -new_severity ERROR

# Build-time optimized flow. Build with --//hw/bitstream/vivado:fpga_cw340_debug, which sets
# CW340_DEBUG=1, to run the Vivado flow with the default flow settings instead: the "Vivado
# Synthesis Defaults" and "Vivado Implementation Defaults" strategies with all their reports.
if {!([info exists ::env(CW340_DEBUG)] && [string is true -strict $::env(CW340_DEBUG)])} {
  # synth_design:
  # - FLATTEN_HIERARCHY full: flatten the whole design. The default, rebuilt, flattens it to
  #   optimize across module boundaries and then rebuilds the hierarchy.
  # - -no_timing_driven: synthesis does not apply the timing constraints and does not optimize
  #   for them.
  set_property STEPS.SYNTH_DESIGN.ARGS.FLATTEN_HIERARCHY full [get_runs synth_1]
  set_property -name {STEPS.SYNTH_DESIGN.ARGS.MORE OPTIONS} -value {-no_timing_driven} \
    -objects [get_runs synth_1]
  # With -no_timing_driven, synthesis cannot apply the generated clocks of the constraints and
  # raises a critical warning (Synth 8-3321). Implementation applies them and aborts on unmatched
  # objects (Vivado 12-4739 above).
  set_msg_config -id {[Synth 8-3321]} -new_severity WARNING

  # opt_design: the RuntimeOptimized directive runs the fewest logic optimization iterations.
  set_property STEPS.OPT_DESIGN.ARGS.DIRECTIVE RuntimeOptimized [get_runs impl_1]
  # place_design: the Quick directive is not timing driven and does only the placement work that
  # a legal design requires.
  set_property STEPS.PLACE_DESIGN.ARGS.DIRECTIVE Quick [get_runs impl_1]
  # phys_opt_design: skip the post-placement optimization of timing-critical paths.
  set_property STEPS.PHYS_OPT_DESIGN.IS_ENABLED false [get_runs impl_1]
  # route_design keeps its default directive: it is timing driven and fixes hold violations,
  # which Quick routing would not. The post-route hook checks that the design meets timing.

  # The default strategies also write DRC, methodology, power, clock utilization and other
  # reports. Only keep the two that .github/workflows/bitstream.yml prints: the utilization after
  # placement and the timing summary after routing.
  set kept_reports {impl_1_place_report_utilization_0 impl_1_route_report_timing_summary_0}
  foreach run {synth_1 impl_1} {
    foreach report [get_report_configs -of_objects [get_runs $run]] {
      if {$report ni $kept_reports} {
        set_property IS_ENABLED false $report
      }
    }
  }
}
