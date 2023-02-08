---
title: Install OpenOCD
---

OpenOCD is a tool to connect with the target chip over JTAG and similar transports.
It also provides a GDB server which is an "intermediate" when debugging software on the chip with GDB.

It is recommended to use the regular upstream version of OpenOCD instead of the [RISC-V downstream fork](https://github.com/riscv/riscv-openocd).

It is trivial to install OpenOCD because we manage the dependency with Bazel.
The Bazel-built OpenOCD binary lives at `//third_party/openocd:openocd_bin`.
It's not runnable, but we also provide a runnable wrapper: `//third_party/openocd`.

OpenOCD also ships with a library of config files.
Instead of using use whichever config files happen to be installed on the system, prefer the Bazel-exposed config files that match OpenOCD source.
Currently, we only expose OpenTitan's default JTAG adapter config as `//third_party/openocd:jtag_adapter_cfg`.

```console
# Manually run OpenOCD:
./bazelisk.sh run //third_party/openocd -- arg1 arg2

# Get the path of the OpenOCD binary:
./bazelisk.sh outquery //third_party/openocd:openocd_bin
```
