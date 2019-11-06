<!-- Copy this file to hw/ip/aes/dv/plan.md and make changes as needed. For
convenience 'aes' in the document can be searched and replaced easily with the
desired IP (with case sensitivity!). Also, use the testbench block diagram here:
https://drive.google.com/open?id=1LfnTSutIW5E6zSCOCf4-scS8MQ8lXhPAPgSfFx2Aqh0
as a starting point and modify it to reflect your aes testbench and save it
to hw/ip/aes/dv/tb.svg. It should get linked and rendered under the block
diagram section below. Once done, remove this comment before making a PR. -->

{{% lowrisc-doc-hdr Foo DV Plan }}

{{% toc 3 }}

* [AES regression dashboard](../../../dv/regressions/weekly/aes/dashboard.html)
* Design milestone: D#
* Verification milestone: [V#](v#_cl.md)

For detailed information on AES design features, please see the
[AES design specification](../doc/aes.md).

<!-- TODO add automation to get the testplan hjson to expand here -->
{{% path to testplan hjson }}

AES testbench has been constructed based on the
[CIP testbench architecture](../../../dv/sv/cip_lib/README.md).
<!-- TODO if AES is not a CIP, then indicated that it is extended from DV
library instead, if applicable. -->

![Block diagram](tb.svg)

Top level testbench is located at `hw/ip/aes/dv/tb/tb.sv`. It instantiates the
AES DUT module `hw/ip/aes/rtl/aes.sv`. In addition, it instantiates several
interfaces for driving/sampling clock and reset, devmode, interrupts, alerts and
tilelink host.

* [common_ifs](../../../dv/sv/common_ifs/README.md)
* [dv_utils_pkg](../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../dv/sv/csr_utils/README.md)

[list compile time configurations, if any]

The following local types and methods defined in `foo_env_pkg` are in use:

[list parameters, types & methods]

[Describe here or add link to its README]

[Describe here or add link to its README]

The AES RAL model is constructed using the
[regtool.py script](../../../../util/doc/rm/RegisterTool.md)
and is placed at `env/foo_reg_block.sv`.

[Describe reference models in use if applicable, example: SHA256/HMAC]

All test sequences reside in `hw/ip/aes/dv/env/seq_lib`. The `foo_base_vseq`
virtual sequence is extended from `cip_base_vseq` and serves as a starting point.
All test sequences are extended from it. It provides commonly used handles,
variables, functions and tasks that the test sequences can simple use / call.
Some of the most commonly used tasks / functions are as
follows:
* task 1:
* task 2:

To ensure high quality constrained random stimulus, it is necessary to develop
functional coverage model. The following covergroups have been developed to prove
that the test intent has been adequately met:
* cg1:
* cg2:

The `foo_scoreboard` is primarily used for end to end checking. It creates the
following analysis ports to retrieve the data monitored by corresponding
interface agents:
* analysis port1:
* analysis port2:
<!-- explain inputs monitored, flow of data and outputs checked -->

* TLUL assertions: The `tb/foo_bind.sv` binds the `tlul_assert` assertions
  to aes to ensure TileLink interface protocol compliance.
* assert prop 1:
* assert prop 2:

We are using our in-house developed
[regression tool](../../../dv/tools/README.md)
for building and running our tests and regressions. Please take a look at the link
for detailed information on the usage, capabilities, features and known
issues. Here's how to run a basic sanity test:
```
  $ cd hw/ip/aes/dv
  $ make TEST_NAME=foo_sanity
```

Tests developed towards executing the testplan are specifed in `hw/ip/aes/dv/sim/tests`.

Regressions are specified in `hw/ip/aes/dv/sim/regressions`.
