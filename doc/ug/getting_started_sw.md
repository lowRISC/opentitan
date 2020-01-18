# Build Software

## Prerequisites

_Make sure you followed the install instructions to [prepare the system]({{< relref "install_instructions#system-preparation" >}}) and install the [compiler toolchain]({{< relref "install_instructions#compiler-toolchain" >}})._

## Building software

OpenTitan software is built using [Meson](https://mesonbuild.com).
However, Meson is not an exact fit for a lot of things OpenTitan does (such as distinguishing between FPGA, ASIC, and simulations), so the setup is a little bit different.

For example, the following commands build the `boot_rom` and `hello_world` binaries for FPGA:

```console
# Configure the Meson environment.
$ cd $REPO_TOP
$ ./meson_init.sh

# Build the two targets we care about, specifically.
$ ninja -C build-out/sw/fpga sw/device/boot_rom/boot_rom_export
$ ninja -C build-out/sw/fpga sw/device/examples/hello_world/hello_world_export

# Build *everything*.
$ ninja -C build-out/sw/fpga all
```

In general, `clean` rules are unnecessary, and Meson will set up `ninja` such that it reruns `meson.build` files which have changed.

Build intermediates will show up in `$REPO_TOP/build-out`, including unlinked object files and libraries, while completed executables are exported to `$REPO_TOP/build-bin`.
As a rule, you should only ever need to refer to artifacts inside of `build-bin`; the exact structure of `build-out` is subject to change.
Complete details of these semantics are documented in `util/build_consts.sh`.

The locations of `build-{out,bin}` can be controled by setting the `$BUILD_ROOT` enviromnent variable, which defaults to `$REPO_TOP`.

`./meson_init.sh` itself is idempotent, but this behavior can be changed with additional flags; see `./meson_init.sh` for more information.
For this reason, most examples involving Meson will include a call to `./meson_init.sh`, but you will rarely need to run it more than once per checkout.

Building an executable `foo` destined to run on an OpenTitan device (i.e., under `sw/device`) will output the following files under `build-bin/sw/device`:
* `foo.elf`: the linked program, in ELF format.
* `foo.bin`: the linked program, as a plain binary with ELF debug information removed.
* `foo.dis`: the disassembled program with inline source code.
* `foo.vmem`: a Verilog memory file which can be read by `$readmemh()` in Verilog code.

Building an executable destined to run on a host machine (i.e., under `sw/host`) will output a host excecutable under `build-bin/sw/host`, which can be run directly.
Currently, each "platform" (`fpga`, `sim-verilator`, etc) have their own copies of all host targets; this is a limitation of our Meson setup, and they are otherwise indistinguishable.
