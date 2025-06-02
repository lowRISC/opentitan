# lowRISC Hardware Primitives

[`prim_alert`](https://reports.opentitan.org/hw/ip/prim/dv/prim_alert/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_alert/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_alert/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_alert/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_alert/code.svg)

[`prim_esc`](https://reports.opentitan.org/hw/ip/prim/dv/prim_esc/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_esc/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_esc/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_esc/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_esc/code.svg)

[`prim_lfsr`](https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_lfsr/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_lfsr/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_lfsr/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_lfsr/code.svg)

[`prim_present`](https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_present/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_present/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_present/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_present/code.svg)

[`prim_prince`](https://reports.opentitan.org/hw/ip/prim/dv/prim_lfsr/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/prim_prince/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_prince/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_prince/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/prim_prince/code.svg)

## Concepts

This directory contains basic building blocks to create a hardware design, called primitives.
A primitive is described by its name, and has a well-defined list of ports and parameters.

Under the hood, primitives are slightly special, as they can have multiple implementations.
In contrast to many other modules in a hardware design, primitives must often be implemented in technology-dependent ways.
For example, a clock multiplexer for a Xilinx FPGA is implemented differently than one for a specific ASIC technology.

Not all primitives need to have multiple implementations.

* Primitives with a single, generic, implementation are normal SystemVerilog modules inside the `hw/ip/prim/rtl` directory.
  We call these primitives *technology-independent primitives*.
* Primitives with multiple implementations are called *technology-dependent primitives*.
  Each implementation has its own directory within `hw/ip/` with the prefix `prim`, e.g. `hw/ip/prim_generic/` or `hw/ip/prim_xilinx/`.

Collections of technology-dependent primitives are called technology libraries.
The *generic* technology library contains a pure-SystemVerilog implementation of primitives' functionality.
This library is commonly used for simulations and as functional reference.
It also serves as a definition of a technology-dependent primitive's interface.
However, other technology libraries can be supersets of the generic technology library.


### Virtual primitives

To allow hardware blocks to be generic across implementations of *technology-dependent primitives*, a feature of FuseSoC called *[virtual cores][]* is used.
Any implementation of a virtual core must provide the same functionality and interface.
The module name must be the same, and the parameter and port lists must include all the required members of the interface.
For an analogy, virtual cores can be thought of as similar to virtual methods in C++ or SystemVerilog.
A hardware block can depend on a virtual core, which can then be substituted for a *concrete* implementation by the user.

To find the interface of a given virtual primitive look at its generic implementation in `hw/prim_generic/`.
Taking `hw/ip/prim_generic/prim_generic_flop_2sync.core` as an example, you'll see the following at the head of the file.

```yaml
name: "lowrisc:prim_generic:flop_2sync"
description: "Generic implementation of a flop-based synchronizer"
virtual:
  - lowrisc:prim:flop_2sync
```

The VLNV (Vendor Library Name Version) of the core is `lowrisc:prim_generic:flop_2sync`, but it also declares itself a provider of the virtual VLNV of `lowrisc:prim:flop_2sync`.
Hardware blocks should depend on this virtual VLNV, so that the user can change implementations.

If an implementation of a virtual core exists in an invokable core's dependency tree, it will be selected.
You can't have multiple implementations of a virtual core in a core's dependency tree.
*An invokable core is the core with its target being run by FuseSoC.*

For this reason, an invokable core may be constructed to have their chosen concrete implementation in their dependency tree.
To reduce the hassle of pulling in a set of implementations into a dependency tree, technology libraries can provide an `:all` core, e.g. `lowrisc:prim_generic:all`.
The invokable core `hw/top_earlgrey/chip_earlgrey_cw310.core`, for example, depends on `lowrisc:prim_xilinx:all`.
However, where it is appropriate to be able to swap prim implementations, it is best to punt this selection to fusesoc mappings, which are described later in this guide.

[virtual cores]: https://fusesoc.readthedocs.io/en/stable/user/build_system/virtual_cores.html


### Mappings

Some invokable cores are expected to be used with multiple different implementations.
To allow users to change primitive implementations, OpenTitan makes use of a FuseSoC feature called *[mappings][]*.
This can be used to request a substitution of particular virtual cores with the desired implementation.
An example of their use is in `hw/ip/prim_xilinx/prim_xilinx.core`:

```yaml
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

Notice that there aren't Xilinx specific implementations for all primitives, so the generic implementation is requested.

Beyond primitives, mappings are also used in the top-level core files, e.g. in `hw/top_earlgrey/top_earlgrey.core`, to ask for top specific implementations.

A specific use of mappings is the lints for each block, for example `hw/ip/uart/uart.core`'s lint target.
None of its dependencies contain concrete primitive implementations.
Instead mappings are used when dvsim invokes the core.
This allows the block to be linted for multiple different primitives (and top-level constants).

[mappings]: https://fusesoc.readthedocs.io/en/stable/user/build_system/mappings.html


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


If you'd like to depend on a specific implementation, you can add the specific implementation's VLNV instead of the virtual VLNV.
For example, you would depend on `lowrisc:prim_xilinx:prim_fifo_sync` instead of `lowrisc:prim:prim_fifo_sync` if you wanted to forcefully use the Xilinx implementation.
Because this method can restrict the flexibility to swap compatible cores, **this is not recommended.**


### Create a technology library

To create a technology library follow these steps:

1. Choose a name for the new technology library.
   Names are all lower-case.
   To ease sharing of technology libraries it is encouraged to pick a very specific name, rather than a generic name like `asic`.
   `mytech` will be used as a placeholder name in the examples.
2. Create a directory in `hw/ip` with the prefix `prim_` followed by the name of your technology library.
3. Copy `hw/ip/prim_generic/prim_generic.core` into the new directory renaming it to match your primitive library, e.g. `hw/ip/prim_mytech/prim_mytech.core`
   Change the vendor and name in this file, e.g. `lowrisc:prim_generic` would become `partner:mytech` where your organisation's name can be used in the place of 'partner'.
   Also, edit the description to better describe the specific implementation.
4. For every primitive implemented by your library:
   1. Copy across the generic implementation into your library, e.g. `cp hw/ip/prim_generic/rtl/prim_flop.sv hw/ip/prim_mytech/rtl/prim_flop.sv`.
   2. Make your changes to the implementation without modifying the module ports or removing parameters.
   3. Copy the generic primitive's core description into your library, e.g. `cp hw/ip/prim_generic/prim_generic_flop.core hw/ip/prim_mytech/prim_mytech_flop.core`.
   4. Edit this copied primitive core file so that it has the new primitive library name, e.g. replacing `lowrisc:prim_generic:flop` with `partner:prim_mytech:flop`.
   5. Then in the libraries main core file, e.g. `hw/ip/prim_mytech/prim_mytech.core`, replace all instances of the generic implementation with your specific implementation, e.g. replacing `lowrisc:prim_generic:flop` with `partner:prim_mytech:flop` again.

You don't have to have your own implementation for every primitive.
You can rely on the generic implementation or even another library's implementation for other primitives.

Technology libraries don't have to live in the OpenTitan repository.
If they are not in the OpenTitan repository, you need to make sure the path to them is given to FuseSoC with either an additional `--cores-root=` argument or set in `fusesoc.conf`.
This is useful in cases where technology libraries contain vendor-specific code which cannot be shared widely or openly.


### Selecting a technology library

You can select a technology library in one of two ways.

If you have your own invokable core which requires a particular primitive, you should add the technology library's VLNV to its dependencies.
`hw/top_earlgrey/chip_earlgrey_cw310.core` is an example of an invokable core requiring a particular technology library, namely `lowrisc:prim_xilinx:all`.
You'll notice this VLNV in its dependencies.

If you are using an invokable core which is generic across different technology libraries, then you should use mappings to select the technology library you'd like to use.
A default technology library sometimes exists for these invokable cores.
The default technology library needs to be disabled with a flag.
`hw/top_earlgrey/chip_earlgrey_asic.core` is an example of one of these invokable cores.
You provide the `fileset_partner` flag to disable the default implementation as well as your mapping.

```sh
fusesoc --cores-root=$OT_REPO run \
    --flag fileset_partner \
    --mapping partner:prim_mytech:all \
    lowrisc:systems:chip_earlgrey_asic
```
