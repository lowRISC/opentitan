---
title: "Formal Verification Setup"
---

_Before following this guide, make sure you've followed the [dependency installation and software build instructions]({{< relref "getting_started" >}})._

This document aims to enable a contributor to get started with a formal verification effort within the OpenTitan project.
While most of the focus is on development of a testbench from scratch, it should also be useful to understand how to contribute to an existing effort.

Please refer to the [OpenTitan Assertions]({{< relref "hw/formal/README" >}}) for information on how formal verification is done in OpenTitan.

## Formal property verification (FPV)

It is recommended to use the [fpvgen]({{< relref "util/fpvgen/README.md" >}}) tool to automatically create an FPV testbench template.
To run the FPV tests in `dvsim`, please add the target in `hw/top_earlgrey/formal/top_earlgrey_fpv_cfgs.hjson`, then run with command:
```console
$ util/dvsim/dvsim.py hw/top_earlgrey/formal/top_earlgrey_fpv_cfgs.hjson --select-cfgs {target_name}
```
It is recommended to add the FPV target to [lint]({{< relref "hw/lint/doc/README" >}}) script `hw/top_earlgrey/lint/top_earlgrey_fpv_lint_cfgs.hjson` to quickly find typos.

## Formal connectivity verification

The connectivity verification is mainly used for exhaustively verifying system-level connections.
User can specify the connection ports via a CSV format file in `hw/top_earlgrey/formal/conn_csvs` folder.
User can trigger top_earlgrey's connectivity test using `dvsim`:
```
  util/dvsim/dvsim.py hw/top_earlgrey/formal/chip_conn_cfgs.hjson
```
