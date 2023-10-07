# Ibex RISC-V Core

Ibex is a production-quality open source 32-bit RISC-V CPU core written in SystemVerilog.

Ibex was initially developed as part of the PULP platform under the name "Zero-riscy", and has been contributed to lowRISC who maintains it and develops it further.
It is under active development, and has seen multiple tape-outs.

- [Github Page](https://github.com/lowrisc/ibex)
- [Documentation Portal](https://ibex-core.readthedocs.io/en/latest/index.html)

As Ibex pre-dates OpenTitan, it is developed as a standalone project in its own lowRISC [repository](https://github.com/lowrisc/ibex), and is [*vendored in*](../../doc/contributing/hw/vendor.md) to this repository for use within [OpenTitan Earl Grey](../top_earlgrey/README.md).
Ibex is integrated into OpenTitan using a [Wrapper](../ip/rv_core_ibex/README.md) HWIP block which instantiates the core and the necessary glue-logic to expose a [Comportable interface](../../doc/contributing/hw/comportability/README.md), as well as adding a few small pieces of helper logic.

- [Ibex Wrapper](../ip/rv_core_ibex/README.md)
