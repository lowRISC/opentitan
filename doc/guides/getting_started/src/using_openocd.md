# Using OpenOCD

OpenOCD is a tool to connect with the target chip over JTAG and similar transports.
It also provides a GDB server which is an "intermediate" when debugging software on the chip with GDB.

There's no need to install OpenOCD yourself because we manage the dependency with Bazel.
We use the regular upstream version of OpenOCD rather than the [RISC-V downstream fork](https://github.com/riscv/riscv-openocd).

The Bazel-built OpenOCD binary is exposed as a Bazel target: `//third_party/openocd:openocd_bin`.
It's not directly runnable, so we provide a runnable wrapper: `//third_party/openocd`.

OpenOCD ships with a library of config files.
Instead of using whichever config files happen to be installed on the system, users should prefer Bazel targets that expose config files directly from OpenOCD's source tree.
Currently, we only expose OpenTitan's default JTAG adapter config as `//third_party/openocd:jtag_adapter_cfg`.

```sh
# Manually run OpenOCD:
./bazelisk.sh run //third_party/openocd -- arg1 arg2

# Get the path of the OpenOCD binary:
./bazelisk.sh outquery //third_party/openocd:openocd_bin
```
