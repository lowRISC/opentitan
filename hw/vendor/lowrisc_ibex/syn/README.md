**This synthesis flow is experimental and under development, it does not produce
tape-out quality netlists and area/timing numbers it generates are not
representative of what would be achievable with a tape-out quality flow**

# Building

In order to build the netlist and get the output outlined below, run
```console
./bazelisk.sh build //hw/ip/aes/pre_syn:aes_synthesis
```

This build target uses the `syn_setup.sh` and `syn_yosys.sh` bash files.
Note that this file sets LR_SYNTH_TIMING_RUN to 0, meaning that the Bazel target
skips the OpenSTA timing run. OpenSTA should be installed to use that path.

# Yosys/OpenSTA synthesis flow

This is a synthesis-only implementation flow using Yosys for Synthesis and
OpenSTA to produce timing reports. Its outputs are:

* A pre-mapping netlist - Gate-level verilog using generic gates that hasn't
  been mapped to a standard-cell library yet
* A post synthesis netlist - Gate-level verilog after optimisation mapped to a
  standard-cell library
* An STA netlist - Logically equivilent to the netlist above but with changes to
  allow processing by OpenSTA
* Area/Cell Usage report - Total area consumed by utilised cells and counts of
  each cell instance used
* Timing reports - Overal timing report and reports broken down into various
  path groups (register to register paths and per IO reports)

Yosys doesn't yet support the full subset of SystemVerilog so the
sv2v tool is used to first convert the RTL into the SystemVerilog subset
Yosys can process.

# Synthesis flow setup

The synthesis flow is configured via environment variables. The `syn_setup.sh`
file is used to set the environment variables for the flow. 
The Bazel build target `//hw/ip/aes/pre_syn:aes_cipher_core_netlist` sets these
variables automatically.

The environment variables that are set in `syn_setup.sh` are

* `LR_SYNTH_CELL_LIBRARY_PATH` - The path to the standard cell library, this
  should point to the absolute path of the Nangate45 library
  (`nangate.lib`).
* `LR_SYNTH_CELL_LIBRARY_NAME` - The name of the standard cell library, this is
  used to alter the flow configuration for the library, currently 'nangate' is
  the only supported value

# Running the synthesis flow

Once `syn_setup.sh` is called, `syn_yosys.sh` is used to run the entire
flow. The Bazel target provides some key output files and places all outputs
in `synthesis_outputs.tar.gz`. This tarfile consists of

- `reports` - All of the generated reports
  - area.rpt - Total area used and per cell instance counts
  - `timing`
    - *.rpt - Raw reports from OpenSTA, gives full paths
    - *.csv.rpt - CSV reports gives start and end point and slack
  - `log`
    - syn.log - Log of the Yosys run
    - sta.log - Log of the OpenSTA run
  - `generated`
    - *.v - RTL after sv2v processing
    - *.pre_map.v - Pre-mapping synthesis netlists
    - *_netlist.v - Post-synthesis netlist
    - *_netlist.sta.v - Post-synthesis netlist usable by OpenSTA
    - *.[library-name].out.sdc - Generated .sdc timing constraints
      file

# Timing constraints

Two files specify the timing constraints and timing related settings for the
flow. These are used to generate a single .sdc file

* `*_lr_synth_core.tcl` - This specifies the constraints on all inputs
  and outputs as a fraction of a clock cycle, the names of the clock and reset
  inputs and the desired clock period in ps
* `*.[library-name].sdc` - Header to include in generated .sdc file. Settings
  can be library dependent so the `LR_SYNTH_CELL_LIBRARY_NAME` environment
  varible is used to supply the `[library-name]` part of the name

# Timing reports

Timing reports are produced for the following path groups
* Overall - Every path in the design, WNS (worst negative slack) from this report is the design WNS
  that limits the frequency
* reg2reg - Paths from register to register
* in2reg - Paths from any input to any register
* reg2out - Paths from any register to any output
* in2out - Paths from any input to any output

They are available in two formats .rpt and .csv.rpt. The .rpt is the full output
from OpenSTA and gives the full path between the start and end points. The CSV
version contains the start-point, end-point and WNS (one path per line). CSV
reports have had their start and end points translated to human readable names
(though this isn't 100% reliable). The raw OpenSTA reports generally contain
only generated cell names so will require further netlist inspection (via Yosys
or simply looking at the netlist .v) to make sense of.

# Post-synthesis inspection

Both Yosys and OpenSTA can be run to perform further inspection on the generated
synthesis. TCL is provided to setup the tools appropriately.

First the environment variables must be setup for the flow and the directory
containing the synthesis output set. This can be done with `syn_setup.sh`

```
$ source syn_setup.sh syn_out/
```

Where `syn_out/` is directory containing the synthesis
outputs from untarring a `synthesis_outputs.tar.gz` output.
Then start Yosys or OpenSTA and run one of the provided TCL files

* `./tcl/yosys_pre_map.tcl` - Loads the pre-mapping netlist
* `./tcl/yosys_post_synth.tcl` - Load the post-synthesis netlist

So to load the post-synthesis netlist in Yosys:

```
$ yosys
yosys> tcl ./tcl/yosys_post_synth.tcl
```

To open the design in OpenSTA

```
$ sta
% source ./tcl/sta_open_design.tcl
```
