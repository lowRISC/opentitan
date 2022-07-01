---
title: "`ralgen`: A FuseSoC generator for UVM RAL package"
---

The `ralgen.py` script is implemented as a
[FuseSoC generator](https://fusesoc.readthedocs.io/en/master/user/generators.html).
which enables the automatic creation of the SystemVerilog UVM RAL package and
its insertion into the dependency tree when compiling the DV testbench.

This approach is useful for DV simulation flows that use FuseSoC as the backend
to generate the filelist for compilation. A separate RAL package generation
step is no longer needed since it gets handled within FuseSoC.

## Generator

The adjoining `ralgen.core` file registers the `ralgen` generator. The FuseSoC
core file that 'calls' the generator adds it as a dependency. When calling the
generator, the following parameters are set:
* **name (mandatory)**: Name of the RAL package (typically, same is the IP).
* **dv_base_names (optional)**: The base class names from which the register
  classes are derived. Set this option to derive the register classes not from
  the default `dv_base_reg`, but from user defined custom class definitions.
  This argument follows the following format:
  `--dv-base-names block:type:entity-name block:type:entity-name ...`.
  `block`: can be any block names.
  `type`: can be `block`, `reg`, `field`, `pkg`, `mem`, or use `all` to override
  all types within the block.
  `entity_name`: the name of the base class / package. If the `type` is set to `all`,
  then this represents the prefix of the bass class / package. The suffixes
  `_reg_block`, `_reg`, `_reg_field`, `_mem`, `_reg_pkg` are applied to infer the
  actual base class / package names from which the generated DV classes will extend.
  Note that we assume the fusesoc core file naming convention follows the package
  name without the `_pkg` suffix.
* **ip_hjson**: Path to the hjson specification written for an IP which includes
  the register descriptions. This needs to be a valid input for `reggen`.
* **top_hjson**: Path to the hjson specification for a top level design. This
  needs to be a valid input for `topgen`.

Only one of the last two arguments is mandatory. If both are set, or if neither
of them are, then the tool throws an error and exits.

The following snippet shows how it is called:
```
generate:
  ral:
    generator: ralgen
    parameters:
      name: <name>
      ip_hjson|top_hjson: <path-to-hjson-spec>
      [dv_base_names:
        - block_1:type:entity_name_1
        - block_2:type:entity_name_2]


targets:
  default:
    ...
    generate:
      - ral
```

Note that the path to `hjson` specification in the snippet above is relative
to the core file in which the generator is called.

## `ralgen` script

When FuseSoC processes the dependency list and encounters a generator, it
passes a YAML file containing the above parameters to the generator tool
(the `ralgen.py`) as a single input. It then parses the YAML input to
extract those parameters.

`ralgen.py` really is just a wrapper around
[`reggen`]({{< relref "util/reggen/doc" >}}) and the `util/topgen.py`
scripts, which are the ones that actually create the RAL package.
Due to the way those scripts are implemented, RAL packages for the IP level
testbenches are generated using
[`reggen`](({{< relref "util/reggen/doc" >}})), and for the chip level
testbench, `util/topgen.py`. Which one to choose is decided by whether
the `ip_hjson` or `top_hjson` parameter is supplied.

In addition, the `ralgen.py` script also creates a FuseSoC core file. It uses
the `name` parameter to derive the
[VLNV](https://fusesoc.readthedocs.io/en/master/user/overview.html#core-naming-rules)
name for the generated core file.

The generated core file adds **`lowrisc:dv:dv_base_reg`** as a dependency for
the generated RAL package. This is required because our DV register block,
register and field models are derived from the
[DV library]({{< relref "hw/dv/sv/dv_lib/doc" >}}) of classes. This
ensures the right compilation order is maintained. If the `dv_base_names`
argument is set, then it adds **`lowrisc:dv:my_base_reg`** as an extra
dependency, where `my_base` is the value of the argument as shown in the
example above. This core file and the associated sources are assumed to be
available in the provided FuseSoC search paths.

## Limitations

The script is not designed to be manually invoked, but in theory, it can be, if
a YAML file that contains the right set of parameters is presented to it
(compliant with FuseSoC).

If the user wishes to create the RAL package manually outside of the DV
simulation flow, then the `make` command can be invoked in the `hw/'` area
instead. It generates the RTL, DV and SW collaterals for all IPs, as well as
the top level in a single step.
