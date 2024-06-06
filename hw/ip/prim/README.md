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

This directory contains basic building blocks to create a hardware design,
called primitives. A primitive is described by its name, and has a well-defined
list of ports and parameters.

Under the hood, primitives are slightly special, as they can have multiple
implementations. In contrast to many other modules in a hardware design,
primitives must often be implemented in technology-dependent ways. For example,
a clock multiplexer for a Xilinx FPGA is implemented differently than one for
a specific ASIC technology.

Not all primitives need to have multiple implementations.

* Primitives with a single, generic, implementation are normal SystemVerilog
  modules inside the `hw/ip/prim/rtl` directory. We call these primitives
  "technology-independent primitives".
* Primitives with multiple implementations have only a FuseSoC core file in the
  `hw/ip/prim` directory. The actual implementations are in "technology
  libraries". We call these primitives "technology-dependent primitives".

### Abstract primitives

Abstract primitives are wrappers around technology-dependent implementations of
primitives, with the ability to select a specific implementation if needed.

In more technical terms, abstract primitives are SystemVerilog modules. The
example below shows one.

```systemverilog
`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_pad_wrapper
#(
  parameter int unsigned AttrDw = 6
) (
  inout wire         inout_io, // bidirectional pad
  output logic       in_o,     // input data
  input              out_i,    // output data
  input              oe_i,     // output enable
  // additional attributes {drive strength, keeper, pull-up, pull-down, open-drain, invert}
  input [AttrDw-1:0] attr_i
);
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;

  if (Impl == prim_pkg::ImplGeneric) begin : gen_generic
    prim_generic_pad_wrapper u_impl_generic (
      .*
    );
  end else if (Impl == prim_pkg::ImplXilinx) begin : gen_xilinx
    prim_xilinx_pad_wrapper u_impl_xilinx (
      .*
    );
  end else begin : gen_failure
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule
```

As seen from the source code snippet, abstract primitives have the following
properties:

- They have an `Impl` parameter which can be set to choose a specific
  implementation of the primitive.
- The `Impl` parameter is set to a system-wide default determined by the
  `PRIM_DEFAULT_IMPL` define.
- All ports and parameters of the abstract primitive are forwarded to the
  implementations.

### Technology libraries

Technology libraries collect implementations of primitives.

At least one technology library must exist: the `generic` technology library,
which contains a pure-SystemVerilog implementation of the functionality. This
library is commonly used for simulations and as functional reference. The
`generic` technology library is contained in the `hw/ip/prim_generic` directory.

In addition to the implementation in the `generic` library, primitives may be
implemented by as many other libraries as needed.

Technology libraries are referenced by their name.


## User Guide

### Use primitives

Primitives are normal SystemVerilog modules, and can be used as usual:
* instantiate it like a normal SystemVerilog module, and
* add a dependency in the FuseSoC core file.

Technology-dependent primitives have an additional parameter called `Impl`.
Set this parameter to use a specific implementation of the primitive for this
specific instance. For example:

```systemverilog
prim_ram_2p #(
  .Width (TotalWidth),
  .Depth (Depth),
  // Force the use of the tsmc40lp technology library for this instance, instead
  // of using the build-time default.
  .Impl(prim_pkg::ImplTsmc40lp)
) u_mem (
  .clk_a_i    (clk_i),
  ...
)
```


### Set the default technology library

If no specific technology library is chosen for an instantiated primitive the
default library is used. The SystemVerilog define `PRIM_DEFAULT_IMPL` can be
used to set the default for the whole design. Set this define to one of the enum
values in `prim_pkg.sv` in the form `prim_pkg::ImplTechlibname`. `Techlibname`
is the capitalized name of the technology library.

In the top-level FuseSoC core file the default technology library can be chosen
like this:

```yaml
# my_toplevel.core

# Declare filesets and other things (omitted)

parameters:
  # Make the parameter known to FuseSoC to enable overrides from the
  # command line. If not overwritten, use the generic technology library.
  PRIM_DEFAULT_IMPL:
    datatype: str
    paramtype: vlogdefine
    description: Primitives implementation to use, e.g. "prim_pkg::ImplGeneric".
    default: prim_pkg::ImplGeneric

targets:
  fpga_synthesis:
    filesets:
      - my_rtl_files
    parameters:
      # Use the xilinx technology library for this target by default.
      - PRIM_DEFAULT_IMPL=prim_pkg::ImplXilinx
    toplevel: my_toplevel
```


### Create a technology library

To create a technology library follow these steps:

1. Choose a name for the new technology library. Names are all lower-case.
   To ease sharing of technology libraries it is encouraged to pick a very specific name, e.g. `tsmc40lp`, and not `asic`.
2. Copy the `prim_generic` folder into an arbitrary location (can be outside of this repository). Name the folder `prim_YOURLIBRARYNAME`.
3. Replace the word `generic` everywhere with the name of your technology library. This includes
    - file and directory names (e.g. `prim_generic_ram1p.sv` becomes
      `prim_tsmc40lp_ram1p.sv`),
    - module names (e.g. `prim_generic_ram1p` becomes `prim_tsmc40lp_ram1p`), and
    - all other references (grep for it!).
4. Implement all primitives. Replace the module body of the generic implementation with a technology-specific implementation as needed.
   Do *not* modify the list of ports or parameters in any way!
5. Add the new technology library to the enum in `prim_pkg.sv` with a value in the form `prim_pkg::ImplTechlibname`.
6. For each of the technology library's primitives add an instantiation to the associated wrapper module in `rtl/`.
