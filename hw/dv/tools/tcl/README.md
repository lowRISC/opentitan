# tools/tcl

This directory contains default .tcl scripts and helper procedures that can be used to drive third-party simulators in the run-phase of a simulation.

The file `sim.tcl` is the default run-script that can be passed to any supported simulator.
Configuration of this script is done by a number of environment variables, which are first checked for internal consistency and then used to select tool-specifc TCL procedures.
This script includes the following features/actions:
- (Configurably) Opens a waveform database and dumps waveforms from a single heirarchy, by default the testbench top (i.e. everything)
- Supports interactive simulations (i.e. gui mode) by returning early to reliquish control
- Run the simulation to completion and exits

## Procedure libraries

The following tool-agnostic TCL procedure libraries are provided.

- `procs.tcl` \
Misc. helper procedures.
- `procs_run.tcl` \
Helper procedures for running the simulation.
- `procs_waves.tcl` \
Helper procedures for setting up waveform capture.

## Passing a custom tcl run-script via dvsim

The included run-script `sim.tcl` provides some sensible defaults for unattended runs and basic waveform capture and debugging.
However, developers may wish to make fuller use of their tool's provided features to collect data more judiciously and control simulations on a more granular level.
To do this, the `dvsim` tool can override the `.tcl` run-script on a case-by-case basis using the `--dump-script` argument, such as shown in the following example:

```sh
util/dvsim/dvsim.py <sim_cfg.hjson> -i <test> --fixed-seed=1 --dump-script=my_dump_script.tcl
```

When using custom run-scipts, the OpenTitan TCL procedure libraries can be re-used for convenience.
An example of a custom run-script that re-uses the tool-agnostic procedures is shown in the following section.

By default when using `sim.tcl`, if wave dumping is enabled, all hierarchies of the top level testbench are dumped.
For large designs, this may slow down the simulation considerably.
One way to solve this issue is to provide a custom `.tcl` run-script that probes only the hierarchies that are relevant to the debugging process.
The provided procedure `wavedumpScope` in the `procs_waves.tcl` library can be re-used to create waveform probes if desired.

## Example custom waveform dump script

```tcl
# BOILERPLATE
# ↓
# Locate the 'dv_root' directory from the environment variable
if {[info exists ::env(dv_root)]} {set dv_root "$::env(dv_root)";} \
else {puts "ERROR: Script run without dv_root environment variable."; exit;}
# Helper procedure libraries
source "$dv_root/tools/tcl/procs.tcl"
source "$dv_root/tools/tcl/procs_waves.tcl"
source "$dv_root/tools/tcl/procs_run.tcl"
# ↑
# BOILERPLATE

# Set the global variables used by the default procedures (could also use EnvVar values)
set simulator "vcs"
set waves "fsdb"
set gui 0

# Open a new database
set wavedump_db "waves.$waves"
puts "INFO: Dumping waves to $wavedump_db."
waveOpenDB $wavedump_db $waves $simulator

# Selectively choose the scopes you wish to dump
wavedumpScope $waves $simulator "/tb/dut/top_earlgrey/u_uart0" 1
wavedumpScope $waves $simulator "/tb/dut/top_earlgrey/u_spi_device" 2
wavedumpScope $waves $simulator "/tb/dut/top_earlgrey/u_rv_core_ibex" 2
wavedumpScope $waves $simulator "/tb/dut/chip_if/gpios_if"

run

quit
```
