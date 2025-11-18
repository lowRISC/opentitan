# lowRISC Hardware Primitives

[`prim_alert`](https://reports.opentitan.org/hw/ip/prim/dv/prim_alert/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_alert/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_alert/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_alert/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_alert/code.svg)<br>
[`prim_esc`](https://reports.opentitan.org/hw/ip/prim/dv/prim_esc/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_esc/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_esc/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_esc/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_esc/code.svg)<br>
[`prim_lfsr`](https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_lfsr/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_lfsr/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_lfsr/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_lfsr/code.svg)<br>
[`prim_present`](https://reports.opentitan.org/hw/ip/prim/dv/prim_present/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_present/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_present/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_present/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_present/code.svg)<br>
[`prim_prince`](https://reports.opentitan.org/hw/ip/prim/dv/prim_prince/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_prince/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_prince/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_prince/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_prince/code.svg)<br>

## Concepts

One of the ways that complexity is managed and reuse is promoted in hardware design is by encapsulating parts of our designs in 'modules'.
Modules, a standard language feature in HDLs, define their abstraction boundary using 'ports', which can be understood as a finite set of wires via which signals move in and out of the module.
Additionally, modules support 'parameterization' via compile time constant inputs, which can control features of the module which would otherwise be static such as the number of wires in each port.

When designing at an RTL level, systems are typically composed of common low-level design patterns and well-understood or optimized circuits, which can be abstracted and implemented as modules.
The OpenTitan project contains a number of these low-level reuseable components, which we refer to as '***Primitives***'.
Different projects and contexts may have different definitions about what level of abstraction and complexity may constitute a primitive.
Here, there is no strict limit on the size of the logic inside a primitive, but they tend to be small and fixed-function.
Examples include fifos, counters, arbiters, synchronizers and codecs.

There may be different implementations of primitives that achieve the same fixed function, but with different trade-offs in how this is achieved.
Modules can contain additional metadata that informs and specializes the process of lowering abstract RTL descriptions of behaviour into hardware that implements the equivalent function.
Tools that perform this lowering undertake a mapping process where higher-level functionality is decomposed into lower and lower level components.
These components exist in, or can be created in, the physical hardware or technology that is being targeted.
In ASIC or FPGA targets, the lower level components may be macro cells or other fixed-function hardware blocks.
An alternative lowering could be to gate-level models of an equivalent hardware implementation, where additional information is added to increase simulation accuracy for prediction of timing and power characteristics.
The process undertaken by these tools is described as 'inferring' (alt. 'inferencing') a combination of lower level components that best implement the circut functionality that is described.
There are many reasons that we may wish to constrain or modify our source files to control inferencing of a set of hardware components to make up a final circuit.

## Primitive Implementations & Libraries

Primitives in OpenTitan exist at a low level of RTL abstraction where it may be desirable under different circumstances to swap-out implementations to obtain better optimized hardware.
For this reason, our definition of a primitive is "*a module with a fixed name and set of ports*".
This minimizes the changes required for different implementations of a primitive to be substituted for each other.

However, not all primitives need to have multiple implementations.
- Primitives with a single generic implementation, where any lowering process is able to infer a suitable hardware implementation from language-level RTL features, are called '***Technology-Independent Primitives***'.
- Primitives with multiple implementations, each of which may be optimized for or targeted towards a certain hardware platform, are called '***Technology-Dependent Primitives***'.

Technology-dependent primitive implementations may be grouped together into '***Technology Libraries***'.
For example, a technology library of primitive implementations may be created for a certain ASIC technology, where the implementations are optimized for desirable synthesis characteristics in that technology.
Within the OpenTitan repository, each technology library has its own directory within `hw/ip/` with the prefix `prim`, such as `hw/ip/prim_xilinx/` for synthesis targeting Xilinx FPGAs.

For each technology-dependent primitive, there should be an implementation that is 'generic' in that it is constructed using language-level RTL constructs, and can be consumed by most downstream tooling.
These implementations are commonly used as input to simulation engines for verification and as a functional reference.
- Technology-dependent 'generic' primitive implementations live inside the `hw/ip/prim_generic` directory.
- Technology-independent 'generic' primitives live inside the `hw/ip/prim` directory.

While primatives are defined primarily by their interface, SystemVerilog does not allow a module interface to be defined without an implementation.
This is unlike constructs in other languages such as Abstract Methods and Interfaces in Java or Traits in Rust.
To determine the interface for a primitive (the module ports and parameters), the generic module implementation should be consulted.

### Virtual Primitives

OpenTitan utilizes the *[Fusesoc][]* build system and package manager to manage RTL at a fileset level.
To allow hardware blocks to be generic across implementations of technology-dependent primitives, a feature of FuseSoC called *[Virtual Cores][]* is used.
Virtual Cores allow FuseSoC to swap in a chosen implementation of a module without changing the RTL instantiation itself.
These can be thought of as similar to virtual methods in C++ or SystemVerilog.

[Fusesoc]: https://github.com/olofk/fusesoc
[Virtual Cores]: https://fusesoc.readthedocs.io/en/stable/user/build_system/virtual_cores.html

All technology-dependent primitives in OpenTitan use Virtual Cores to allow them to be substituted at build time.
For this reason, they are also referred to as ***Virtual Primitives***.

FuseSoC Virtual Cores work by adding additional metadata to a Core, marking it as an implementation of another 'virtual' Core.
The Virtual Core is a unique *[VLNV][]*, and does not exist as a named `.core` file in the tree.
Taking `hw/ip/prim_generic/prim_generic_flop_2sync.core` as an example, you will see the following at the head of the file:

[VLNV]: https://fusesoc.readthedocs.io/en/stable/user/build_system/core_files.html#the-core-name-version-and-description

```yaml
CAPI=2:
name: "lowrisc:prim_generic:flop_2sync"
description: "Generic implementation of a flop-based synchronizer"
virtual:
  - lowrisc:prim:flop_2sync
```
Descriptively, we might say that the virtual core VLNV is `lowrisc:prim:flop_2sync`, and one possible implementation of this virtual core is `lowrisc:prim_generic:flop_2sync`.
As a virtual primitive, the interface (module name and ports) for `flop_2sync` is common among all implementations, and hence all instantiations.
Fundamentally, if multiple modules with the same name and ports are available, controlling the include paths and fileset inputs to a tool allows FuseSoC to select which module will be used to provide the implementation.

By depending only on the virtual VLNV of a virtual primative, cores become generic over that primitive.
Any core that implements this virtual core may be selected at build time to provide the implementation for all instantiations.
During build time, all virtual cores must be resolved to a concrete implementation.
If a virtual core cannot be resolved because no implementations are found or specified at build time, a "conflicting-requirements" error will be generated by the FuseSoC solver.
The following section further describes the resolution process.

It is still possible and valid for a Core to depend only on a specific implementation of a technology-dependent primitive, however the implementation cannot be substituted at build time in this case, and it functions as a normal FuseSoC Core.

### Resolution of Concrete Implementations

When invoking FuseSoC, a 'target' in a Core file is selected to choose the flow we wish to run.
Targets can depend on one or more 'filesets' defined within the Core, and each fileset can optionally depend on other Cores.
Therefore, when FuseSoC is run a dependency graph comprised of Cores and filesets is constructed.

If a fileset depends on a Virtual Core, a resolution process must take place at build time to determine which of the possible implementations becomes the chosen or 'Concrete' implementation.
This resolution can be controlled in two ways:

1) **Dependency tree resolution**

   If a single implementation of a virtual core exists in the target dependency tree, it will be selected.
   Multiple implementations of a virtual core in the target dependency tree will result in a 'conflicting-requirements' build time error from the FuseSoC solver.

2) **Mappings**

   Mappings are an explicit directive for an implementation to be used to resolve a virtual core.
   They are described in more detail below.

If a virtual core cannot be resolved according to the methods above, an implementation is chosed non-deterministically from all known cores in the input libraries that implement this Virtual Core.
The following build time warning will be emitted:
```
WARNING: Non-deterministic selection of virtual core <Virtual_VLNV> selected <Concrete_VLNV>
```

Many targets will choose option 1) to resolve their virtual cores by adding a specific implementation core into their dependencies.
Top-level cores will typically specialize generic systems and modules for a particular hardware target or application by adding constraints and wrappers for that target.
One part of this may be choosing a Technology Library to resolve all technology-dependent primitives to implementations that are specialized or optimized for the application.
To reduce the hassle of pulling in implementations for all virtual cores in a Technology Libraries into a dependency tree, the library will provide an `:all` core, e.g. `lowrisc:prim_generic:all` or `lowrisc:prim_xilinx_ultrascale:all`.
For example, the core `hw/top_earlgrey/chip_earlgrey_cw310.core` targeting a synthesis for a specific Xilinx FPGA depends on `lowrisc:prim_xilinx:all` to select a Xilinx Technology Library for primitives.


### Mappings


Fusesoc .core files may contain a 'mapping' key, which can define injective/one-to-one *[mappings][]* from virtual cores to a implementation of that virtual core.
Passing `--mapping=<VLNV>` via the CLI will cause any 'mapping' keys in the core to be used to resolve virtual cores to concrete implementations.
The concrete implementation core needs only to be discoverable in the input libraries, not in the target dependency tree.
The mapping applies to all uses of the virtual core anywhere in the dependency tree.

[mappings]: https://fusesoc.readthedocs.io/en/stable/user/build_system/mappings.html

An example set of mappings for the Xilinx Technology Library can be found in the following .core file.
Notice that there are not Xilinx specific implementations for all primitives, so we fallback to the generic implementation in those cases.

```yaml
# hw/ip/prim_xilinx/prim_xilinx.core
name: "lowrisc:prim_xilinx:all:0.1"
description: "Xilinx 7-series prim library"

mapping:
  "lowrisc:prim:and2"         : lowrisc:prim_xilinx:and2
  "lowrisc:prim:buf"          : lowrisc:prim_xilinx:buf
  "lowrisc:prim:clock_buf"    : lowrisc:prim_xilinx:clock_buf
  "lowrisc:prim:clock_div"    : lowrisc:prim_generic:clock_div
  "lowrisc:prim:clock_gating" : lowrisc:prim_xilinx:clock_gating
  "lowrisc:prim:clock_inv"    : lowrisc:prim_generic:clock_inv
  "lowrisc:prim:clock_mux2"   : lowrisc:prim_xilinx:clock_mux2
  # ...
```

One specific use of mappings is the lints for each block, such as the lint target for the OpenTitan UART in `hw/ip/uart/uart.core`.
At the HWIP level, the UART is generic across technology-dependent primitives, and hence its dependencies do not contain any concrete primitive implementations.
Instead, the 'dvsim' verification tool passes a set of mappings via CLI flags to FuseSoC to resolve all virtual cores for the specific linting job.
This allows the block to be linted for multiple different primitives (and top-level constants).

Mappings may be present in top-level core files, e.g. in `hw/top_earlgrey/top_earlgrey.core`, to specialize block-level flows for top specific implementations as described previously.
```yaml
# hw/top_earlgrey/top_earlgrey.core
name: "lowrisc:systems:top_earlgrey:0.1"
description: "Technology-independent Earl Grey toplevel"

mapping:
  "lowrisc:virtual_constants:top_pkg": "lowrisc:earlgrey_constants:top_pkg"
  "lowrisc:virtual_constants:top_racl_pkg": "lowrisc:earlgrey_constants:top_racl_pkg"
  "lowrisc:systems:ast_pkg": "lowrisc:systems:top_earlgrey_ast_pkg"
  "lowrisc:virtual_ip:flash_ctrl_prim_reg_top": "lowrisc:earlgrey_ip:flash_ctrl_prim_reg_top"
```

The following example shows how the UART lint flow is specialized for the earlgrey top.
```yaml
# hw/top_earlgrey/lint/top_earlgrey_lint_cfgs.hjson
{
  name: uart
  fusesoc_core: lowrisc:ip:uart
  import_cfgs: ["{proj_root}/hw/lint/tools/dvsim/common_lint_cfg.hjson"]
  additional_fusesoc_argument: "--mapping=lowrisc:systems:top_earlgrey:0.1"
  rel_path: "hw/ip/uart/lint/{tool}"
},
```

Mappings cannot be used to override a virtual core which has already been resolved to a implementation in the target dependency tree.

If multiple mappings are provided for a virtual core, the following build time error will be generated:
```
RuntimeError: The following sources are in multiple mappings:
	{<Virtual_VLNV>, ...}.
```


## User Guide

### Using primitives

Primitives are normal SystemVerilog modules, and can be used as usual:
1. Instantiate it like a normal SystemVerilog module.
   ```systemverilog
   prim_fifo_sync #(
     .Width   (8),
     .Pass    (1'b0),
     .Depth   (TxFifoDepth)
   ) u_uart_txfifo (
     .clk_i,
     // ..
     .err_o   ()
   )
   ```
2. Add it as a dependency in the FuseSoC core file.
   ```yaml
   name: "lowrisc:ip:uart:0.1"
   description: "uart"
   filesets:
     files_rtl:
       depend:
         - lowrisc:virtual_constants:top_pkg
         - lowrisc:prim:prim_fifo_sync
   ```

### Creating a technology library

To create a technology library follow these steps:

1. Choose a name for the new technology library.
   Names are all lower-case.
   To ease sharing of technology libraries it is encouraged to pick a very specific name, rather than a generic name like `asic`.
   `mytech` will be used as a placeholder name in the examples.
2. Create a directory in `hw/ip` with the prefix `prim_` followed by the name of your technology library.
3. Copy `hw/ip/prim_generic/prim_generic.core` into the new directory renaming it to match your primitive library, e.g. `hw/ip/prim_mytech/prim_mytech.core`
   Change the vendor and name in this file, e.g. `lowrisc:prim_generic` would become `partner:prim_mytech` where your organisation's name can be used in the place of 'partner'.
   Also, edit the description to better describe the specific implementation.
4. For every primitive implemented by your library:
   1. Copy across the generic implementation into your library, e.g. `cp hw/ip/prim_generic/rtl/prim_flop.sv hw/ip/prim_mytech/rtl/prim_flop.sv`.
   2. Make your changes to the implementation without modifying the module name, ports or removing parameters.
   3. Copy the generic primitive's core description into your library, e.g. `cp hw/ip/prim_generic/prim_generic_flop.core hw/ip/prim_mytech/prim_mytech_flop.core`.
   4. Edit this copied primitive core file so that it has the new primitive library name, e.g. replacing `lowrisc:prim_generic:flop` with `partner:prim_mytech:flop`.
   5. Then in the libraries main core file, e.g. `hw/ip/prim_mytech/prim_mytech.core`, replace all instances of the generic implementation with your specific implementation, e.g. replacing `lowrisc:prim_generic:flop` with `partner:prim_mytech:flop` again.

You don't have to have your own implementation for every primitive.
You can rely on the generic implementation or even another library's implementation for other primitives.

Technology libraries also do not have to live in the OpenTitan repository.
If they are not in the OpenTitan repository, you need to make sure the path to them is given to FuseSoC with either an additional `--cores-root=` argument or set in `fusesoc.conf`.
This is useful in cases where technology libraries contain vendor-specific code which cannot be shared widely or openly.


### Selecting a technology library

As outlined in [Resolution of Concrete Implementations](#resolution-of-concrete-implementations), you can select a technology library in one of two ways.

If you have your own target which requires a particular primitive, you should add the technology library's VLNV to its dependencies.
`hw/top_earlgrey/chip_earlgrey_cw310.core` is an example of an core requiring a particular technology library, namely `lowrisc:prim_xilinx:all`.
You'll notice this VLNV in its dependencies.

If you are running a target which is generic across different technology libraries, then you should use mappings to select the technology library you would like to use.
In some cases, a default technology library may already by included, but this will be removable using FuseSoC CLI *[Flags][]* to modify the build process.
`hw/top_earlgrey/chip_earlgrey_asic.core` is an example of one of these cores.
You should provide the `fileset_partner` flag to disable the default implementation, as well as your mapping to select an alternate implementation.

[Flags]: https://fusesoc.readthedocs.io/en/stable/user/build_system/flags.html

```yaml
# hw/top_earlgrey/chip_earlgrey_asic.core
name: "lowrisc:systems:chip_earlgrey_asic:0.1"
description: "Earl Grey chip level"

filesets:
  files_rtl:
    depend:
      - lowrisc:systems:top_earlgrey:0.1
      - lowrisc:systems:top_earlgrey_pkg
      - lowrisc:systems:top_earlgrey_padring
      - lowrisc:earlgrey_ip:flash_ctrl_prim_reg_top
      - "fileset_partner ? (partner:systems:top_earlgrey_ast)"
      - "fileset_partner ? (partner:systems:top_earlgrey_scan_role_pkg)"
      - "fileset_partner ? (partner:prim_tech:all)"
      - "fileset_partner ? (partner:prim_tech:flash)"
      - "!fileset_partner ? (lowrisc:systems:top_earlgrey_ast)"
      - "!fileset_partner ? (lowrisc:earlgrey_systems:scan_role_pkg)"
      - "!fileset_partner ? (lowrisc:prim_generic:all)"
      - "!fileset_partner ? (lowrisc:prim_generic:flash)"
```

```sh
fusesoc \
    --cores-root=$OT_REPO \
    run \
    --flag fileset_partner \               # Disable default implementation
    --mapping partner:prim_mytech:all \    # Select alternate implementation via mappings
    lowrisc:systems:chip_earlgrey_asic
```
### prim_asap7 example

 [ASAP7](https://github.com/The-OpenROAD-Project/asap7) is an open-source standard-cell library.
 It serves as an example for partners to integrate their own technology specific prim library.

The steps in [creating a tech library](#creating-a-technology-library) were followed to create this prim library.

Each standard-cell instance name is prefixed with a `u_size_only_` such that these instances can be easily identified during synthesis and preserved.

### Important synthesis constraints to keep important redundant constructs

The basic prim instances cannot be removed or merged with other cells through logic optimization or constant propagation as this would remove important security countermeasures from the design.

All instantiated basic gates (`buf`, `mux2`, `inv`, `clock_gating`, `and2`, `xor2`, `xnor2`, `flop`) should be instantiated with a name prefix of `u_size_only_` such that preserve attributes can be set during synthesis.
The syntax to set a preserved attribute varies across tool providers.
To make sure the right constraints are applied, a simple example design (`prim_sdc_example`) is provided.
This design can be synthesized, and its netlist can be analyzed to verify that the correct constraints are applied and all important cells are preserved.

The required files for synthesis can be generated with the following command:

```shell
fusesoc  --cores-root . \
		 run \
		 --target=syn \
		 --flag fileset_partner \
		 --mapping lowrisc:prim_asap7:all \
		 --setup \
		 --build-root build lowrisc:prim:sdc_example
```

By setting the `fileset_partner` flag, the generic prim implementation is not used, and the one provided through the mapping argument is used instead.
Please note, on designs with other technology dependent files, the `fileset_partner` flag also selects other technology specific implementations (e.g. OTP, Flash, JTAG, AST, pads).
If those are not used, they can be mapped to the generic implementations.

#### Checks on the generated netlist

After synthesizing the top module `prim_sdc_example` the following checks should be performed on the netlist:

1. In the synthesized netlist, the following number of size_only instances must be present:

| cell names |  buf  | and2 |  xor  |  xnor  | flop | clock_mux2 | clock_gating |
| -----------|  ---- |------|-----  |------  |------|------------|--------------|
| #instances |  328  |  56  |  120  |  56    |  252 |  2         |  2           |

2. None of the test_*_o signals can be driven by a constant 0 or 1.
The instantiated `size_only` instances must prevent logic optimizations and keep the output comparators.
This can be checked with the synthesis tool, e.g. `check_design -constant`

3. None of the buffers or flip flops in this example design are unloaded if constraints are applied correctly.
This can be checked by the synthesis tool, e.g. `check_design -unloaded_comb/-unloaded_seqs`

4. `lc_en_o`, `mubi_o` signals cannot be driven to a constant value because optimization or constant propagation across preserved instances is not allowed.

5. `lc_en_i`, `mubi_i` signals can only be connected to variables, or legal values (`MuBi4True`, `MuBi4False`, `On`, `Off`)

If all checks are successful, the same constraints can be applied to the full design.
The script `utils/design/check-netlist.py` [check-netlist] can be used to report a summary of size_only cells in a netlist.
It can also automate an initial version of checks (4) and (5) but it does **not** replace a final manual inspection of the netlist.

[check-netlist]: https://github.com/lowRISC/opentitan/tree/master/util/design#netlist-checker-script
