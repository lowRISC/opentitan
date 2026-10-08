# CHERIoT Memory Subsystem DV document

## Goals
* Verify the CHERIoT memory subsystem with a SV/UVM testbench based on the
  [CIP testbench architecture](../../../dv/sv/cip_lib/README.md).
* Run the tests in the [testplan](#testplan) towards closing code and functional coverage.

## Current status
* [Design & verification stage](../../../README.md)
  * [HW development stages](../../../../doc/project_governance/development_stages.md)

## Design features
See the [CHERIoT Memory Subsystem HWIP technical specification](../README.md).

## Testbench
`hw/ip/cheriot_mem_sys/dv/tb.sv` instantiates `hw/ip/cheriot_mem_sys/rtl/cheriot_mem_sys.sv` with:
* [Clock and reset interface](../../../dv/sv/common_ifs/README.md)
* [TileLink host interface](../../../dv/sv/tl_agent/README.md) on the `regs` CSR port
* [Alert interface](../../../dv/sv/alert_agent/README.md) for `fatal_fault`
* [Interrupt pins interface](../../../dv/sv/common_ifs/README.md) for `intr_tbre_done_o`

## Building and running tests
The [dvsim](https://github.com/lowRISC/dvsim) tool is used for building and running our tests and regressions.

To run a smoke test, use:
```console
$ dvsim hw/ip/cheriot_mem_sys/dv/cheriot_mem_sys_sim_cfg.hjson -i cheriot_mem_sys_smoke
```
To run the CSR, alert, interrupt and TL-UL suites, use:
```console
$ dvsim hw/ip/cheriot_mem_sys/dv/cheriot_mem_sys_sim_cfg.hjson
```

## Testplan
[Testplan](../data/cheriot_mem_sys_testplan.hjson)
