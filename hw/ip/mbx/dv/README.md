# MBX DV document

## Goals
* **DV**
  * Verify all MBX IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench.

## Current status
* [Design & verification stage](../../../README.md)
  * [HW development stages](../../../../doc/project_governance/development_stages.md)
* [Simulation results]()

## Testbench architecture

The MBX testbench has been constructed based on the [CIP testbench architecture](../../../dv/sv/cip_lib/README.md).

### Block diagram

TBD

### Top level testbench

The top level testbench for the MBX IP is located at `hw/ip/mbx/dv/tb.sv`. It instantiates the MBX DUT module `hw/ip/mbx/rtl/mbx.sv`.
Additionally, the testbench instantiates the following interfaces and connects them to the DUT:
* [Clock and reset interface](../../../dv/sv/common_ifs/README.md#clk_rst_if)
* [TileLink host interfaces](../../../dv/sv/tl_agent/README.md) for the RoT-side and the SoC-side.
* [TileLink device interface](../../../dv/sv/tl_agent/README.md) for mailbox SRAM.
* [Interrupts](../../../dv/sv/common_ifs/README.md#pins_if)

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [common_ifs](../../../dv/sv/common_ifs/README.md)
* [dv_utils_pkg](../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../dv/sv/csr_utils/README.md)

### UVM RAL Model

The MBX IP blocks employs two RAL models for the RoT-side registers and the SoC-side registers:
* mbx_core_ral_pkg.sv
* mbx_soc_ral_pkg.sv

Both are created with the [`ralgen`](../../../dv/tools/ralgen/README.md) FuseSoC generator script automatically when the simulation is at the build stage.

They may be created manually by invoking [`regtool`](../../../../util/reggen/doc/setup_and_use.md).
```console
$ $REPO_TOP/util/regtool.py $REPO_TOP/hw/ip/mbx/data/mbx.hjson -s --outdir <path_to_directory>
```
### Stimulus Strategy
#### Test sequences
The test sequences for the MBX IP may be found in `hw/ip/mbx/dv/env/seq_lib`.

#### Functional coverage
TBD

### Self-checking strategy
#### Scoreboard
TBD

#### Assertions
* TLUL assertions: The `sva/mbx_bind.sv` binds the `tlul_assert` [assertions](../../tlul/doc/TlulProtocolChecker.md) to the IP to ensure TileLink interface protocol compliance.
* 'Unknown' checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

### Building and running tests
The MBX IP has been verified using the in-house regression tool [`dvsim`](../../../../util/dvsim/README.md) for building and running tests/regressions.
```console
$ $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/ip/mbx/dv/mbx_sim_cfg.hjson -i mbx_smoke
```

## Testplan
[Testplan](../data/mbx_testplan.hjson)
