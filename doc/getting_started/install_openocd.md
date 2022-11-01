---
title: Install OpenOCD
---

OpenOCD is a tool to connect with the target chip over JTAG and similar transports.
It also provides a GDB server which is an "intermediate" when debugging software on the chip with GDB.

It is recommended to use the regular upstream version of OpenOCD instead of the [RISC-V downstream fork](https://github.com/riscv/riscv-openocd).

It is trivial to install OpenOCD because we manage the dependency with Bazel.
The OpenOCD binary lives at `@openocd//:openocd_bin` and `//third_party/openocd` is a runnable wrapper script.

```console
# Manually run OpenOCD:
./bazelisk.sh run //third_party/openocd -- arg1 arg2

# Get the path of the OpenOCD binary:
./bazelisk.sh outquery @openocd//:openocd_bin
```
