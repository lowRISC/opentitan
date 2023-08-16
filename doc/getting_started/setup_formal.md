# Formal Verification Setup

_Before following this guide, make sure you've followed the [dependency installation and software build instructions](README.md)._

This document aims to enable a contributor to get started with a formal verification effort within the OpenTitan project.
While most of the focus is on development of a testbench from scratch, it should also be useful to understand how to contribute to an existing effort.

Please refer to the [OpenTitan Assertions](../../hw/formal/README.md) for information on how formal verification is done in OpenTitan.

## Formal property verification (FPV)

The formal property verification is used to prove assertions in the target.
There are three sets of FPV jobs in OpenTitan. They are all under the directory `hw/top_earlgrey/formal`.
* `top_earlgrey_fpv_ip_cfgs.hjson`: List of IP targets.
* `top_earlgrey_fpv_prim_cfgs.hjson`: List of prim targets (such as counters, fifos, etc) that are usually imported by an IP.
* `top_earlgrey_fpv_sec_cm_cfgs.hjson`: List of IPs that contains standard security countermeasure assertions. This FPV environment only proves these security countermeasure assertions. Detailed description of this FPV use case is documented in [Running FPV on security blocks for common countermeasure primitives](../../hw/formal/README.md#running-fpv-on-security-blocks-for-common-countermeasure-primitives).

To automatically create a FPV testbench, it is recommended to use the [fpvgen](../../util/fpvgen/README.md) tool to create a template.
To run the FPV tests in `dvsim`, please add the target to the corresponding `top_earlgrey_fpv_{category}_cfgs.hjson` file , then run with command:
```console
util/dvsim/dvsim.py hw/top_earlgrey/formal/top_earlgrey_fpv_{category}_cfgs.hjson --select-cfgs {target_name}
```

It is recommended to add the FPV target to [lint](../../hw/lint/README.md) script `hw/top_earlgrey/lint/top_earlgrey_fpv_lint_cfgs.hjson` to quickly find typos.

## Formal connectivity verification

The connectivity verification is mainly used for exhaustively verifying system-level connections.
User can specify the connection ports via a CSV format file in `hw/top_earlgrey/formal/conn_csvs` folder.
User can trigger top_earlgrey's connectivity test using `dvsim`:
```
util/dvsim/dvsim.py hw/top_earlgrey/formal/chip_conn_cfgs.hjson
```

The connectivity testplan is documented under `hw/top_earlgrey/data/chip_conn_testplan.hjson`.
