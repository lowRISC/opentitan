{{% lowrisc-doc-hdr UART DV Plan }}
{{% import_testplan uart_testplan.hjson }}

{{% toc 4 }}

## Goals
* **DV**
  * Verify all UART IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench

## Current status
* [Design & verification stage](../../../../doc/project/hw_dashboard.md)
  * [HW development stages](../../../../doc/ug/hw_stages.md)
* DV regression results dashboard (link TBD)

## Design features
For detailed information on UART design features, please see the
[UART design specification](../doc/uart.md).

## Testbench architecture
UART testbench has been constructed based on the
[CIP testbench architecture](../../../dv/sv/cip_lib/README.md).

### Block diagram
<!-- ![Block diagram](tb.svg) -->

### Top level testbench
Top level testbench is located at `hw/ip/uart/dv/tb/tb.sv`. It instantiates the UART DUT module `hw/ip/uart/rtl/uart.sv`.
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* [Clock and reset interface](../../../dv/sv/common_ifs/README.md)
* [TileLink host interface](../../../dv/sv/tl_agent/README.md)
* UART IOs
* Interrupts ([`pins_if`](../../../dv/sv/common_ifs/README.md))

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [common_ifs](../../../dv/sv/common_ifs/README.md)
* [dv_utils_pkg](../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../dv/sv/csr_utils/README.md)

### Global types & methods
All common types and methods defined at the package level can be found in
`uart_env_pkg`. Some of them in use are:
```systemverilog
parameter uint UART_FIFO_DEPTH = 32;
```

### TL_agent
UART instantiates (already handled in CIP base env) [tl_agent](../../../dv/sv/tl_agent/README.md)
which provides the ability to drive and independently monitor random traffic via
TL host interface into UART device.

### UART agent
[describe or provide link to UART agent documentation]

### RAL
The UART RAL model is constructed using the [regtool.py script](../../../../util/doc/rm/RegisterTool.md) and is placed at `env/uart_reg_block.sv`.

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/uart/dv/env/seq_lib`.
The `uart_base_vseq` virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from `uart_base_vseq`.
It provides commonly used handles, variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as follows:
* task 1:
* task 2:

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:
* cg1:
* cg2:

### Self-checking strategy
#### Scoreboard
The `uart_scoreboard` is primarily used for end to end checking.
It creates the following analysis ports to retrieve the data monitored by corresponding interface agents:
* analysis port1:
* analysis port2:

#### Assertions
* TLUL assertions: The `tb/uart_bind.sv` binds the `tlul_assert` [assertions](../../tlul/doc/TlulProtocolChecker.md) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.
* assertion 1
* assertion 2

## Building and running tests
We are using our in-house developed [regression tool](../../../dv/tools/README.md) for building and running our tests and regressions.
Please take a look at the link for detailed information on the usage, capabilities, features and known issues.
Here's how to run a basic sanity test:
```console
$ cd hw/ip/foo/dv
$ make TEST_NAME=uart_sanity
```

## Testplan
{{% insert_testplan x }}
