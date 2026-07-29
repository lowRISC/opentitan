# CHERIoT DV document

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
`hw/ip/cheriot/dv/tb.sv` instantiates `hw/ip/cheriot/rtl/cheriot.sv` with:
* [Clock and reset interface](../../../dv/sv/common_ifs/README.md)
* [TileLink host interface](../../../dv/sv/tl_agent/README.md) on the `regs` CSR port
* Alerts ([`alert_esc_if`](../../../dv/sv/alert_esc_agent/README.md)) for `fatal_fault`

## Building and running tests
Built and run with `dvsim.py`.

```console
$ dvsim hw/ip/cheriot/dv/cheriot_sim_cfg.hjson -i cheriot_smoke   # smoke only
$ dvsim hw/ip/cheriot/dv/cheriot_sim_cfg.hjson                    # CSR, alert and TL-UL suites
```

## Testplan
[Testplan](../data/cheriot_testplan.hjson)
