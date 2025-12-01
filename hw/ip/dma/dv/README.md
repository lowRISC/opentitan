# DMA DV document

## Goals
* **DV**
  * Verify all DMA IP features by running dynamic simulations with a SV/UVM based testbench.
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage on the IP and all of its sub-modules.
  * Achieve the required level of code and functional coverage.
* **FPV**
  * Verify TileLink device protocol compliance with an SVA based testbench.

## Current status
* [Design & verification stage](../../../README.md)
  * [HW development stages](../../../../doc/project_governance/development_stages.md)
* [Simulation results]()

## Testbench architecture

The DMA testbench has been constructed based on the [CIP testbench architecture](../../../dv/sv/cip_lib/README.md).

### Block diagram

![Block diagram](./doc/tb.svg)

### Top level testbench

The top level testbench for the DMA IP is located at `hw/ip/dma/dv/tb/tb.sv`. It instantiates the DMA DUT module `hw/ip/dma/rtl/dma.sv`.
Additionally, the following interfaces are instantiated to connect to the DUT:
* [Clock and reset interface](../../../dv/sv/common_ifs/README.md)
* [TileLink host interface](../../../dv/sv/tl_agent/README.md)
* DMA System Bus to TL-UL adapter ([`dma_sys_tl_if`](../dv/env/dma_sys_tl_if.sv))
* Interrupts ([`pins_if`](../../../dv/sv/common_ifs/README.md))

There are four TileLink interfaces:
* The configuration register interface (device).
* OpenTitan Internal bus (host).
* SoC Control Network bus (host).
* SoC System Bus (host).

An adapter is used to connect the SoC System Bus port of the DMA controller to a TL-UL agent to support verification of this non-TileLink port.
Since the OpenTitan TL-UL components support only a 32-bit address space presently but the SoC System Bus carries a 64-bit address, the base address of this adapter is randomized and it presents a 4GiB window within the 64-bit address space.
The adapter will respond with an error if the DMA IP attempts to access an address outside of this window.

### Common DV utility components
The following utilities provide generic helper tasks and functions to perform activities that are common across the project:
* [common_ifs](../../../dv/sv/common_ifs/README.md)
* [dv_utils_pkg](../../../dv/sv/dv_utils/README.md)
* [csr_utils_pkg](../../../dv/sv/csr_utils/README.md)

### UVM RAL Model
The DMA RAL model is created with the [`ralgen`](../../../dv/tools/ralgen/README.md) FuseSoC generator script automatically when the simulation is at the build stage.

It can be created manually by invoking [`regtool`](../../../../util/reggen/doc/setup_and_use.md).
```console
$ $REPO_TOP/util/regtool.py $REPO_TOP/hw/ip/dma/data/dma.hjson -s --outdir <path_to_directory>
```

### Stimulus Strategy
#### Test sequences
The test sequences for the DMA IP may be found in `hw/ip/dma/dv/env/seq_lib`.
All sequences derive from `dma_base_vseq` which provides basic access to the DMA configuration registers, as well as functionality that is common to many of the derived sequences.
Deriving from `dma_base_vseq` is a sequence called `dma_generic_vseq` which is capable of performing any transfer that the DMA IP supports, and this sequence is further specialized in derived sequences by the use of constraints.
There are two main categories of derived sequences called `dma_handshake_<>` and `dma_memory_<>` which, respectively, perform DMA transfers with and without the use of hardware-handshaking to/from a Low Speed I/O peripheral.

#### Functional coverage
To ensure high-quality constrained random stimuli, it is necessary to develop a functional coverage model.
The following covergroups have been developed to prove that the test intent has been adequately met:
* common covergroup for interrupts `hw/dv/sv/cip_lib/cip_base_env_cov.sv`: Cover interrupt value, interrupt enable, intr_test, interrupt pin
* common covergroups for alerts `hw/dv/sv/alert_esc_agent/alert_esc_agent_cov.sv`: Cover alert handshake signaling
* common covergroups for CSRs `hw/dv/sv/dv_base_reg/*cov.sv`: Cover lockable register fields
* common covergroups for TL-UL accesses `hw/dv/sv/tl_agent/tl_agent_cov.sv`: Covert TL-UL A/D channel traffic
* dma_config_cg `hw/ip/dma/dv/env/dma_env_cov.sv`: Cover the different DMA transfer configurations
* dma_tlul_error_cg `hw/ip/dma/dv/env/dma_env_cov.sv`: Cover TL-UL error and non-error responses on all ports
* dma_status_cg `hw/ip/dma/dv/env/dma_env_cov.sv`: Cover the different status indicators
* dma_error_code_cg `hw/ip/dma/dv/env/dma_env_cov.sv`: Cover all of the error conditions that the DMA controller reports
* dma_interrupt_cg `hw/ip/dma/dv/env/dma_env_cov.sv`: Interrupt-clearing configuration in hardware-handshaking mode
* dma_intr_src_cg `hw/ip/dma/dv/env/dma_env_cov.sv`: Interrupt-clearing address and data.

### Self-checking strategy
#### Scoreboard
Within the DV environment the `dma_scoreboard` checks every transaction within a transfer occurs as expected, checking the read data, the write data and the write strobes.
Additionally any expected interrupts from the DMA IP are modeled using a variable-timing model to accommodate variations in the timing of randomized bus activity, as well as future changes to the IP.

For most configurations of the DMA controller, the scoreboard will also check the contents of the destination memory/FIFO once a transfer has completed.
This just provides additional confidence and the output from the DMA IP is as expected.
The scoreboard performs complete prediction and checking of both the read and the write traffic, i.e. everything is checked during transfer itself.

Finally the scoreboard incorporates independent behavioral code for calculating the SHA2 digest on the data being transferred, and thus checks the digest against that produced by the RTL for inline hashing operations.

#### Assertions
* TLUL assertions: The `sva/dma_bind.sv` binds the `tlul_assert` [assertions](../../tlul/doc/TlulProtocolChecker.md) to the IP to ensure TileLink interface protocol compliance.
* Unknown checks on DUT outputs: The RTL has assertions to ensure all outputs are initialized to known values after coming out of reset.

### Building and running tests
The [dvsim](https://github.com/lowRISC/dvsim) tool is used for building and running our tests and regressions.
```console
$ dvsim $REPO_TOP/hw/ip/dma/dv/dma_sim_cfg.hjson -i dma_generic_smoke
```

## Testplan
[Testplan](../data/dma_testplan.hjson)
