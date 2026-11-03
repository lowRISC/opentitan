# I3C DV document

## Goals
* Verify the I3C IP with a SV/UVM testbench based on the [CIP testbench architecture](../../../dv/sv/cip_lib/README.md).
* Run the tests in the [testplan](#testplan) towards closing code and functional coverage.

## Current status
* [Design & verification stage](../../../README.md)
  * [HW development stages](../../../../doc/project_governance/development_stages.md)

The testbench currently runs the common CSR, memory, TL-UL access, interrupt, alert and security countermeasure tests.
It has no I3C bus agent yet, and the scoreboard does not model the I3C functionality.

## Design features
See the [I3C HWIP technical specification](../README.md).

## Testbench
`hw/ip/i3c/dv/tb/tb.sv` instantiates `hw/ip/i3c/rtl/i3c.sv` with the Earl Grey parameters (`i3c_env_pkg`) and:
* [Clock and reset interfaces](../../../dv/sv/common_ifs/README.md) for `clk_i` and `clk_aon_i`.
  The base vseq resets both domains together.
* [TileLink host interface](../../../dv/sv/tl_agent/README.md)
* [Alert interface](../../../dv/sv/alert_agent/README.md) for `fatal_fault`
* [Interrupt pins interface](../../../dv/sv/common_ifs/README.md) for `intr_hci_o` and `intr_targ_o`
* A model of the I3C bus:
  * SCL and SDA are driven by the DUT outputs and resolved by strength.
  * The pull-ups (`ctrl_scl_pu_en_o`, `cio_ctrl_sda_pu_en_o`) and high-keepers (`scl_hk_en_o`, `sda_hk_en_o`) of the DUT act on the bus, and a [pins interface](../../../dv/sv/common_ifs/README.md) observes their enables.
  * Board-level pull-ups, a weak [pins interface](../../../dv/sv/common_ifs/README.md), keep the bus at a defined level when the DUT disables all of its pull-ups and high-keepers.
    They are disabled by default; tests that are not about I/O correctness enable them with `+en_board_pullup=1`.
    The common CSR tests do so, because they write random values to `PHY_CONFIG`.

The other inputs are tied off as in Earl Grey: there is no Target Reset detector, RACL is disabled, and the RAM configuration and DFT inputs take their default values.

### UVM RAL model
The RAL model is created with the [`ralgen`](../../../dv/tools/ralgen/README.md) FuseSoC generator from `hw/ip/i3c/data/i3c.hjson`.
`i3c_env_cfg` adjusts it to the DUT configuration:
* The CSRs describe `MaxTargets` Virtual Targets, but the DUT implements `NumTargets`.
  The register view of the Tx state and free levels of the other Virtual Targets reads as zero, so their reset values are set to zero.
* `PRESENT_STATE_DEBUG` and `TARG_STATE_DEBUG` reflect the SCL and SDA pin levels.
  `i3c.hjson` excludes them from all CSR checks, because the chip-level simulation does not drive the pins.
  The bus model drives the pins, so `i3c_env_cfg` restricts these exclusions to the non-init CSR tests.

### CSR and memory tests
All CSR tests cover the registers of both clock domains.
Every register except `INTR_STATE` is checked by at least `csr_hw_reset`; reggen excludes the state register of status-type interrupts from all CSR tests.
Instead, the scoreboard predicts `INTR_STATE` from the value written to `INTR_TEST` and checks it while the hardware cannot signal an interrupt, and `i3c_intr_test` checks the interrupt outputs against this prediction.
The register and field exclusions and their reasons are in `i3c.hjson`.
In addition, `i3c_env_cfg` excludes fields that accesses to the queue ports change (`BUFFER_STATUS`, `TARG_PIO_CONTROL`) from `csr_mem_rw_with_rand_reset`, the only CSR test that accesses these ports.

The memory windows are handled as follows:
* `HCI_PORTS` and `TTI_PORTS` are queue ports, not storage.
  They are excluded from `mem_walk`, and the scoreboard does not check reads from them.
* The DAT and the DCT do not store the reserved fields of their entries, which read as zero.
  `i3c_csr_mem_walk_seq` walks them with a mask of the stored bits, and the scoreboard applies the same masks.
* `BUFFER` gets the generic `mem_walk`.
  As the queues store their data in the message buffer, the hardware also writes to it, e.g. when data enters a queue through a queue port or on an Asynchronous Event.
  An interface in the testbench observes the writes to the message buffer memory, and the scoreboard does not check message buffer words that the hardware has written since the last software write.

## Building and running tests
The [dvsim](https://github.com/lowRISC/dvsim) tool is used for building and running our tests and regressions.

To run the CSR test smoke regression, use:
```console
$ dvsim hw/ip/i3c/dv/i3c_sim_cfg.hjson -i smoke
```
To run all tests, use:
```console
$ dvsim hw/ip/i3c/dv/i3c_sim_cfg.hjson
```

## Testplan
[Testplan](../data/i3c_testplan.hjson)
