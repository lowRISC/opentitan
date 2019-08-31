<!-- Copy this file to hw/ip/foo/dv/plan.md and make changes as needed. For
convenience 'foo' in the document can be searched and replaced easily with the
desired IP (with case sensitivity!). Also, use the testbench block diagram here:
https://drive.google.com/open?id=1LfnTSutIW5E6zSCOCf4-scS8MQ8lXhPAPgSfFx2Aqh0
as a starting point and modify it to reflect your foo testbench and save it
to hw/ip/foo/dv/tb.svg. It should get linked and rendered under the block
diagram section below. Once done, remove this comment before making a PR. -->

{{% lowrisc-doc-hdr Foo DV Plan }}

{{% toc 3 }}

## Current status
* [FOO regression dashboard](../../../dv/regressions/weekly/foo/dashboard.html)
* Design milestone: D#
* Verification milestone: [V#](v#_cl.md)

## Design features
For detailed information on FOO design features, please see the
[FOO design specification](../doc/foo.md).

## Testplan
<!-- TODO add automation to get the testplan hjson to expand here -->
{{% path to testplan hjson }}

## Testbench architecture
FOO testbench has been constructed based on the
[CIP testbench architecture](../../../dv/sv/cip_lib/README.md).
<!-- TODO if FOO is not a CIP, then indicated that it is extended from DV
library instead, if applicable. -->

### Block diagram
![Block diagram](tb.svg)

### Testbench
Top level testbench is located at `hw/ip/foo/dv/tb/tb.sv`. It instantiates the
FOO DUT module `hw/ip/foo/rtl/foo.sv`. In addition, it instantiates several
interfaces for driving/sampling clock and reset, devmode, interrupts, alerts and
tilelink host.

### Common DV utility components
* [common_ifs](../../../dv/sv/common_ifs/README.md)
* [dv_utils_pkg](../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../dv/sv/csr_utils/README.md)

### Compile-time configurations
[list compile time configurations, if any]

### Local types & methods
The following local types and methods defined in `foo_env_pkg` are in use:

[list parameters, types & methods]

### UVC/agent 1
[Describe here or add link to its README]

### UVC/agent 2
[Describe here or add link to its README]

### RAL
The FOO RAL model is constructed using the
[regtool.py script](../../../../util/doc/rm/RegisterTool.md)
and is placed at `env/foo_reg_block.sv`.

### Reference models
[Describe reference models in use if applicable, example: SHA256/HMAC]

### Stimulus strategy
#### Test sequences
All test sequences reside in `hw/ip/foo/dv/env/seq_lib`. The `foo_base_vseq`
virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from it. It provides commonly used handles,
variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as
follows:
* task 1:
* task 2:

#### Functional coverage
To ensure high quality constrained random stimulus, it is necessary to develop
functional coverage model. The following covergroups have been developed to prove
that the test intent has been adequately met:
* cg1:
* cg2:

### Self-checking strategy
#### Scoreboard
The `foo_scoreboard` is primarily used for end to end checking. It creates the
following analysis ports to retrieve the data monitored by corresponding
interface agents:
* analysis port1:
* analysis port2:
<!-- explain inputs monitored, flow of data and outputs checked -->

#### Assertions
* TLUL assertions: The `tb/foo_bind.sv` binds the `tlul_assert` assertions
  to foo to ensure TileLink interface protocol compliance.
* assert prop 1:
* assert prop 2:

## Building and running tests
We are using our in-house developed
[regression tool](../../../dv/tools/README.md)
for building and running our tests and regressions. Please take a look at the link
for detailed information on the usage, capabilities, features and known
issues. Here's how to run a basic sanity test:
```
  $ cd hw/ip/foo/dv
  $ make TEST_NAME=foo_sanity
```

### Test list
Tests developed towards executing the testplan are specifed in `hw/ip/foo/dv/sim/tests`.

### Regression list
Regressions are specified in `hw/ip/foo/dv/sim/regressions`.
