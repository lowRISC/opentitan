# Debugging on an FPGA with an ILA

This document provides instructions on observing signals on an FPGA with an integrated logic analyzer (ILA) in the scope of the OpenTitan project.


## Background

When you observe a problem with OpenTitan instantiated on an FPGA, we recommend first exploring software-based and simulation-based approaches to debug it.
First, try to increase the verbosity of software running on OpenTitan as well as on the workstation to which the FPGA is connected.
Second, try to reproduce the problem in RTL simulation.
A gate-level simulation of the FPGA design is possible in theory, but it may not be practical when peripherals are involved in the problem and no cycle-accurate model of those peripherals is available.
Even if those approaches do not reveal the root cause itself, they often provide valuable insight into the involved internal processes.
If none of those approaches reveal the root cause, it may be necessary to observe FPGA-internal signals, which is the purpose of an ILA.


## Steps

In a nutshell, we will take the following steps:
1. [Instantiate an ILA module to debug signals in RTL.](#selecting-signals-and-instantiating-an-ila)
2. [Parametrize the ILA and get it synthesized in Vivado.](#parametrizing-the-ila-and-getting-it-synthesized-in-vivado)
3. [Build a bitstream that includes the ILA.](#building-and-splicing-bitstreams-that-include-an-ila)
4. [Program the FPGA, connect to the ILA, and run a test.](#programming-the-fpga-controlling-the-ila-and-running-a-test)


## Requirements

This guide was written for OpenTitan on a [NewAE CW310 board](./get_a_board.md#chipwhisperer-cw310) with a Kintex 7 FPGA on it.
You further need to have Xilinx Vivado installed; see [Install Vivado](../../getting_started/install_vivado/README.md) for the currently supported version and installation instructions.
Finally, you need a connection to the JTAG port of the FPGA.
This guide was written using [Xilinx's Platform Cable USB II](https://www.xilinx.com/products/boards-and-kits/hw-usb-ii-g.html), although the first generation Platform Cable USB or the SmartLynq Data Cable may also work.

[Set up the FPGA board](../../getting_started/setup_fpga.md) and connect the JTAG plug of Platform Cable USB II to J18 on the CW310 and its USB plug to your workstation where Vivado is installed.
Make sure that the [drivers for Platform Cable USB II are installed](https://support.xilinx.com/s/article/59128?language=en_US) on that workstation.


## Selecting signals and instantiating an ILA

The first steps are to select signals for debugging and to instantiate an ILA that samples those signals.

Select signals in the RTL code based on your understanding of the on-chip processes that are involved in the problem.
As every change of signals selected for debugging requires a new FPGA implementation run, which can take tens of minutes to a few hours, generously including signals often pays off.
However, keep in mind that the resources required for the ILA increase with the number of signals, so it's often infeasible to select thousands of wires at once.
For these reasons, our general advice is to generously select control signals (e.g., FSM states, inputs, and outputs) and only selectively select data signals for debugging.

There are different approaches for connecting an ILA to the signals selected for debugging; see [*Probing the Design for In-System Debugging* in Xilinx UG908](https://docs.xilinx.com/r/2020.2-English/ug908-vivado-programming-debugging/Probing-the-Design-for-In-System-Debugging) for details.
In our experience, the most reliable approach is to instantiate an ILA in RTL and connect it to the debug signals in the design, and we'll take this approach in this document.

Open the RTL code for a module in which you have identified a substantial portion of the signals for debugging and append the following instantiation of an ILA module:
```sv
ila_0 u_ila_0 (
  .clk      (),
  .probe0   ()
);
```

The `clk` input of the ILA needs to be assigned to a free-running clock; i.e., it cannot be clock-gated.
This clock must also be sufficiently fast to sample all signals that will be connected to the `probe0` input.
If the `clk_i` input of the module in which you are inserting the ILA does not fulfill these requirements, wire an additional, suitable clock from the top-level design through the hierarchy into that module.

The `probe0` input of the ILA takes the signals identified for debugging.
Ideally, these signals are all in the same clock domain as the ILA.
If that is not the case, we recommend syncing those signals that are in a different clock domain into the clock domain of the ILA by instantiating a `prim_flop_2sync`.
Calculate the total bit width of the signals assigned to the `probe0` input; you will need that number in the next step.

Here is a complete example of an ILA and a synchronizer instantiated in `dmi_jtag` to sample the JTAG I/Os of that module:
```sv
localparam SyncWidth = 6;
logic [SyncWidth-1:0] probe0_presync, probe0_synced;
assign probe0_presync = {
  tck_i,
  tms_i,
  trst_ni,
  td_i,
  td_o,
  tdo_oe_o
};

prim_flop_2sync #(
  .Width(SyncWidth)
) u_prim_flop_2sync_probe0 (
  .clk_i  (clk_i),
  .rst_ni (rst_ni),
  .d_i    (probe0_presync),
  .q_o    (probe0_synced)
);

ila_0 u_ila_0 (
  .clk    (clk_i),
  .probe0 (probe0_synced)
);
```

You may not want to instantiate the ILA in all instances of the module for which you have modified the RTL.
In that case, add a `parameter logic` to the module with a default value of `1'b0`, set its value to `1'b1` for the instance in which you would like to instantiate the ILA, and use that parameter to conditionally instantiate the ILA.
For example, to debug `dmi_jtag` in `rv_dm` only, change `dmi_jtag.sv` like this:
```sv
module dmi_jtag #(
  parameter logic [31:0] IdcodeValue = 32'h00000001,
  parameter logic DebugIla = 1'b0 // add this
) (
  /* ... */

  if (DebugIla) begin : gen_ila // wrap instance into this `if (...) begin end`
    ila_0 u_ila_0 (
      /* ... */
    );
  end
);
```
And change the instantiation of `dmi_jtag` in `rv_dm` like this:
```sv
dmi_jtag #(
  .IdcodeValue (IdcodeValue),
  .DebugIla    (1'b1) // add this
) dap (
  /* ... */
);
```

If you need to debug signals in different modules, you can either instantiate one ILA in each of them or route signals from other modules into one in which you have already instantiated an ILA.
Routing is more effort than instantiating multiple ILAs, but it may be required to sample signals from different modules in the same clock cycle.
If you need to debug signals from many different modules, you may want to instantiate one ILA at the lowest common design hierarchy and route the signals there.


## Parametrizing the ILA and getting it synthesized in Vivado

Next, we need to create an ILA *IP core* from Vivado's library, parametrize it, and synthesize it before synthesizing the rest of our design.
To execute commands in Vivado before synthesis of the Earlgrey design, we have to add them to `hw/top_earlgrey/util/vivado_hook_synth_design_pre.tcl`.
The commands to create and configure an ILA core can be obtained from Vivado's GUI, although we have to tweak them to work with our flow, which uses Vivado *in-memory projects*.

Open Vivado's GUI (creating a project is not necessary), click on *Window* -> *IP Catalog*, and search for *ILA*.
Double-click on *ILA (Integrated Logic Analyzer)* to open the customization window.
Set *Component Name* to the name of the module in RTL (`ila_0` in our example above).
In the *General Options* tab:
- Keep *Monitor Type* to *Native*.
- Keep *Number of Probes* to 1 unless you have added additional probe ports (`probe1` etc.) in RTL.
- Select *Sample Data Depth* according to your needs; this determines how many samples can be saved per trigger action.
  4096 should be feasible unless you are probing many signals.
- Keep *Same Number of Comparators for All Probe Ports* ticked and *Number of Comparators* at 1 unless you know you need different settings.
- If you can define a trigger condition based on probe signals, leave *Trigger In Port* unticked.
  If you need to trigger the ILA from RTL, tick it and connect the added `trig_in` and `trig_in_ack` ports (see diagram on the left of the GUI window with *Show disabled ports* unticked).
- If metastability of probed signals is a concern, add one or multiple *Input Pipe Stages*.
- Tick *Capture Control*, which allows you to filter samples for capturing based on probe inputs.
- Leave *Advanced Trigger* unticked unless you know you need it (see [Xilinx PG172](https://docs.xilinx.com/v/u/en-US/pg172-ila) for more information).
In the *Probe_Ports* tab:
- For each *Probe Port*, set *Probe Width* to the total bit width of the signals assigned to that input (e.g., `probe0`), which you have calculated above.
- Leave all other settings at their default value.

Click *OK* and then *Generate*.
You will now get an error ("[Common 17-53] User Exception: No open project. Please use Save Project As to save your work and re-do this operation"), which you can close as it is not critical.

The output we need from this step is the `set_property` command that configures the ILA, which got printed in the *Tcl Console* window.
Copy that command from the Vivado GUI, open `hw/top_earlgrey/util/vivado_hook_synth_design_pre.tcl`, and paste it at the end of that file.

Add the following two commands *before* the command that configures the ILA:
```tcl
# Save the current 'in-memory' project as actual project.  This is required for some of the commands
# below, such as `get_fileset`.
save_project_as -force lowrisc_systems_chip_earlgrey_cw310_0.1

# Create ILA IP core.
set ila_xci_path [ create_ip -name ila -vendor xilinx.com -library ip -version 6.2 -module_name ila_0 ]
```
If your ILA has a different module name than `ila_0`, change it in the second command; it must match the name used in `get_ips` for the configuration command.

Add the following seven commands *after* the command that configures the ILA:
```tcl
# Generate synthesis and implementation targets.
generate_target {instantiation_template} [get_files $ila_xci_path]
generate_target -force all [get_files $ila_xci_path]
config_ip_cache -export [get_ips -all ila_0]
export_ip_user_files -of_objects [get_files $ila_xci_path] -no_script -sync -force -quiet
create_ip_run [get_files -of_objects [get_fileset sources_1] $ila_xci_path]

# Synthesize ILA OOC ahead of Earlgrey synthesis.
launch_runs ila_0_synth_1 -jobs 12
wait_on_run ila_0_synth_1
```
Again, replace `ila_0` with the module name of your ILA if necessary.

As a complete example for the ILA instantiated above, the end of `hw/top_earlgrey/util/vivado_hook_synth_design_pre.tcl` now could look as follows:
```tcl
# Save the current 'in-memory' project as actual project.  This is required for some of the commands
# below, such as `get_fileset`.
save_project_as -force lowrisc_systems_chip_earlgrey_cw310_0.1

# Create ILA IP core.
set ila_xci_path [ create_ip -name ila -vendor xilinx.com -library ip -version 6.2 -module_name ila_0 ]

# Configure ILA.
set_property -dict [list \
  CONFIG.C_PROBE0_WIDTH {6} \
  CONFIG.C_DATA_DEPTH {4096} \
  CONFIG.C_EN_STRG_QUAL {1} \
  CONFIG.C_PROBE0_MU_CNT {2} \
  CONFIG.ALL_PROBE_SAME_MU_CNT {2} \
] [get_ips ila_0]

# Generate synthesis and implementation targets.
generate_target {instantiation_template} [get_files $ila_xci_path]
generate_target -force all [get_files $ila_xci_path]
config_ip_cache -export [get_ips -all ila_0]
export_ip_user_files -of_objects [get_files $ila_xci_path] -no_script -sync -force -quiet
create_ip_run [get_files -of_objects [get_fileset sources_1] $ila_xci_path]

# Synthesize ILA OOC ahead of Earlgrey synthesis.
launch_runs ila_0_synth_1 -jobs 12
wait_on_run ila_0_synth_1
```

If you have more than one ILA module, repeat the commands starting from *Create ILA IP core* with a different module name for each module.

Finally, open `hw/top_earlgrey/util/vivado_hook_init_design_post.tcl` in your editor.
The commands in this file get executed at the end of initialization of Vivado's implementation step.
As we synthesize the ILA out of context (OOC), we need to load those synthesis results separately before running Earlgrey's implementation.
Append the following two commands to do this:
```tcl
# Load synthesized ILA from checkpoint.
add_files ../../lowrisc_systems_chip_earlgrey_cw310_0.1.runs/synth_1/lowrisc_systems_chip_earlgrey_cw310_0.1.runs/ila_0_synth_1/ila_0.dcp

# Link design (again) as otherwise the ILA would remain a black box for implementation.
link_design -top chip_earlgrey_cw310 -part xc7k410tfbg676-1
```
Again, change the `ila_0` module name and/or repeat the first command as required for your setup.

A known limitation of loading the design checkpoint (DCP) of the ILA will manifest itself in a critical warning ("[Project 1-840] The design checkpoint file '...' was generated for an IP by an out of context synthesis run and should not be used directly as a source in a Vivado flow. Constraints and other files related to the IP are only stored in the xci/xcix, not the checkpoint. It is strongly recommended that the original IP source file (.xci/.xcix) be used.") during implementation.
In practice, we have not seen problems (e.g., due to missing constraints) yet, and using the "original IP source file (.xci/.xcix)" for implementation does not seem to work.
So you can ignore this warning, but it's worth keeping in mind *if* you should see any problems (e.g., due to timing violations).


## Building and splicing bitstreams that include an ILA

With the steps above complete, building a first bitstream that includes the defined ILAs is as simple as `bazel build //hw/bitstream:rom --define bitstream=vivado`.
While synthesis, implementation, and bitstream generation runs (which can easily take 2 h), keep an eye on the logs.
Especially during RTL elaboration, which happens very early, check the logs for any unexpected warnings.
The path to the synthesis log file is usually `bazel-out/k8-fastbuild/bin/hw/bitstream/vivado/build.fpga_cw310/synth-vivado/lowrisc_systems_chip_earlgrey_cw310_0.1.runs/synth_1/runme.log`.

Once Vivado has successfully generated a bitstream, locate its directory with `dirname $(./bazelisk.sh outquery-all //hw/bitstream:rom --define bitstream=vivado)` (it will usually be `bazel-out/k8-fastbuild/bin/hw/bitstream/vivado`).
Append `/build.fpga_cw310/synth-vivado` to that path.
In the resulting directory, you should find `otp.mmi`, `rom.mmi`, and `lowrisc_systems_chip_earlgrey_cw310_0.1.bit`.
We will next copy those files into a local bitstream cache that Bazel can use.

If you don't have a local bitstream cache yet, create one as follows:
Firstly, choose a local directory to store the cache and assign its path to the `BAZEL_BITSTREAMS_CACHE` environment variable.
For example:
```sh
export BAZEL_BITSTREAMS_CACHE=$HOME/local-bitstreams-cache
```
Secondly, create a `cache` directory in that directory:
```sh
mkdir -p $BAZEL_BITSTREAMS_CACHE/cache
```

Create a directory with the name of the Git hash for which you have built the bitstream under `$BAZEL_BITSTREAMS_CACHE/cache/` (e.g,. `$BAZEL_BITSTREAMS_CACHE/cache/2e5a31b7d80b6eb97e114b2ca8f9e132ec7c83a6`).
(You can find the relevant Git hash with `git log`, for example.
If you have not committed the changes to implement the ILA yet, we recommend doing so at least locally.)
Copy `otp.mmi` and `rom.mmi` to that directory.
Copy `lowrisc_systems_chip_earlgrey_cw310_0.1.bit` also to that directory, then rename the copy to `lowrisc_systems_chip_earlgrey_cw310_0.1.bit.orig`.

Now instruct Bazel to use a bitstream from the local cache by setting an `--offline` argument in the `BITSTREAM` environment variable; for example:
```sh
export BITSTREAM="--offline 2e5a31b7d80b6eb97e114b2ca8f9e132ec7c83a6"
```
Then invoke `bazel build //hw/bitstream:rom_otp_test_unlocked0` to splice the desired ROM and OTP image into the bitstream with an ILA.
The resulting bitstream can be located with `./bazelisk.sh outquery-all //hw/bitstream:rom_otp_test_unlocked0`.


## Programming the FPGA, controlling the ILA, and running a test

Start the Vivado GUI on the workstation to which the Platform Cable USB II is connected and click *Open Hardware Manager*.
Open a hardware target by clicking *Open target* -> *Auto Connect*.
If that does not work, click *Open New Target...* (instead of *Auto Connect*) and *Next*, then select *Local server* and click *Next*.
If there are no hardware targets in this window, check that Platform Cable USB II is properly connected, its drivers installed on the workstation, and the user under which you run Vivado has access to USB devices.
Otherwise, select the only targets and click *Next* and *Finish* to connect to the FPGA.

Click *Program device*.
As *Bitstream file*, select the file identified at the end of the previous section.
As *Debug probes file*, navigate to the `synth-vivado` directory identified in the previous section, then go to `lowrisc_systems_chip_earlgrey_cw310_0.1.runs/impl_1` and select `debug_nets.ltx`.
Click *Program* and wait for programming to complete.

You should now see a window with one tab per ILA.
Each tab has a waveform viewer at the top and two setting windows at the bottom.
The left bottom window has two tabs.
In the *Settings* tab, useful settings are mainly the number of windows and the position of the trigger in the window.
In the *Status* tab, the ILA trigger can be armed, disarmed, and activated immediately.
The right bottom window also has two tabs; the first defines the trigger conditions and the second the capture conditions (both based on probe signals of the ILA).
Configure each ILA according to your needs and hit the 'play' button in the *Status* tab to arm its trigger.

Last but not least, you need to run a test in which the FPGA does not get reprogrammed (otherwise the ILA or at least its configuration is lost).
To this end, make two modifications to prevent tests from loading a bitstream:
```diff
diff --git a/rules/opentitan_test.bzl b/rules/opentitan_test.bzl
--- a/rules/opentitan_test.bzl
+++ b/rules/opentitan_test.bzl
@@ -197,7 +197,6 @@ def cw310_params(
         tags = _BASE_PARAMS["tags"],
         test_runner = _BASE_PARAMS["test_runner"],
         test_cmds = [
-            "--exec=\"fpga load-bitstream --rom-kind={rom_kind} $(location {bitstream})\"",
             "--exec=\"bootstrap --clear-uart=true $(location {flash})\"",
             "--exec=\"console --exit-success={exit_success} --exit-failure={exit_failure}\"",
             "{clear_bitstream}",
diff --git a/sw/host/opentitanlib/src/test_utils/init.rs b/sw/host/opentitanlib/src/test_utils/init.rs
--- a/sw/host/opentitanlib/src/test_utils/init.rs
+++ b/sw/host/opentitanlib/src/test_utils/init.rs
@@ -138,9 +138,6 @@ impl InitializeTest {
         // Create the UART first to initialize the desired parameters.
         let _uart = self.bootstrap.options.uart_params.create(&transport)?;

-        // Load a bitstream.
-        Self::print_result("load_bitstream", self.load_bitstream.init(&transport))?;
-
         // Bootstrap an rv32 test program.
         Self::print_result("bootstrap", self.bootstrap.init(&transport))?;
         Ok(transport)
```

Finally, run the test by invoking `opentitantool` or `bazel` as you would usually.
The ILA should trigger during the test and display waves.
If that does not happen, revise the trigger conditions.
You could also click the 'fast forward' button while the test is running to trigger the ILA immediately and see the waves captured at that time; this is particularly useful in combination with precise capture conditions.
