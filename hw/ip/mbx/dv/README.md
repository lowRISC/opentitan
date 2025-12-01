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
To ensure the quality of the constrained random stimuli, it is necessary to develop a functional coverage model.
The following covergroups have been developed to ensure that the stimulus intent is met:

* common covergroup for interrupts `hw/dv/sv/cip_lib/cip_base_env_cov.sv`: Cover interrupt value, interrupt enable, intr_test, interrupt pin
* common covergroups for alerts `hw/dv/sv/alert_esc_agent/alert_esc_agent_cov.sv`: Cover alert handshake signaling (RoT side).
* common covergroups for CSRs `hw/dv/sv/dv_base_reg/*cov.sv`: Cover lockable register fields (RoT side; SoC side has no REGWENs).
* common covergroups for TL-UL accesses `hw/dv/sv/tl_agent/tl_agent_cov.sv`: Covert TL-UL A/D channel traffic (RoT and SoC registers).
* mbx_mem_range_cg `hw/ip/mbx/dv/env/mbx_env_cov.sv`: Ensure that different Inbound and Outbound mailbox addresses have been tested.
* mbx_rot_control_cg `hw/ip/mbx/dv/env/mbx_env_cov.sv`: Check that all control functions on the RoT side have been stimulated.
* mbx_soc_control_cg `hw/ip/mbx/dv/env/mbx_env_cov.sv`: Ensure that all bits of the SoC-side control register have been stimulated.
* mbx_rot_status_cg `hw/ip/mbx/dv/env/mbx_env_cov.sv`: Ensure that all status indications on the RoT side have been observed.
* mbx_soc_status_cg `hw/ip/mbx/dv/env/mbx_env_cov.sv`: Cover all SoC-side status indications.
* mbx_object_size_cg `hw/ip/mbx/dv/env/mbx_env_cov.sv`: Ensure that RoT responses of different sizes have been tested.
* mbx_soc_intr_pins_cg `hw/ip/mbx/dv/env/mbx_env_cov.sv`: Check all interrupt pins on the SoC side have been stimulated.
* mbx_doe_intr_msg_addr_cg `hw/ip/mbx/dv/env/mbx_env_cov.sv`: Cover the 32-bit `MSG_ADDR` channel from the SoC side to the RoT.
* mbx_doe_intr_msg_data_cg `hw/ip/mbx/dv/env/mbx_env_cov.sv`: Cover the 32-bit `MSD_DATA` channel.

### Self-checking strategy
#### Scoreboard
The `mbx_scoreboard` forms predictions of all memory traffic to be performed by the DUT on its SRAM interface, and checks the observed DUT traffic against those predictions. Additionally, where possible, it predicts observable changes to the register state on the two TL-UL device interfaces (RoT- and SoC-side) and checks the observed DUT register state against those predictions.
TBD: Interrupt prediction and checking.

#### Assertions
* TLUL assertions: The `sva/mbx_bind.sv` binds the `tlul_assert` [assertions](../../tlul/doc/TlulProtocolChecker.md) to the IP to ensure TileLink interface protocol compliance.
* 'Unknown' checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

### Building and running tests
The [dvsim](https://github.com/lowRISC/dvsim) tool is used for building and running our tests and regressions.
```console
$ dvsim $REPO_TOP/hw/ip/mbx/dv/mbx_sim_cfg.hjson -i mbx_smoke
```

## Testplan
[Testplan](../data/mbx_testplan.hjson)
