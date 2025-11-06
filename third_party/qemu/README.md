# QEMU

For instructions on setting up QEMU for local development and troubleshooting steps, see the [setup guide](./setup.md).

## Introduction

[QEMU](https://www.qemu.org/) is an open-source project which primarily aims to support virtualization, user-mode emulation and full-system (machine) emulation flows.
Its primary goal is to provide fast functional emulation in a generic manner that supports many host devices, at the cost of losing the accuracy offered by simulation.
OpenTitan is an example of full-system emulation, where we emulate an OpenTitan RISC-V 32-bit machine to support running OpenTitan programs on any supported host, such as an x86-64 PC.
In this context, a QEMU OpenTitan "machine" is a system consisting of an Ibex core, optionally including other cores and attached peripherals (equivalent to a "top").

The predominant advantage of QEMU is its speed: internally, QEMU uses a dynamic translation backend called [TCG](https://www.qemu.org/docs/master/devel/tcg.html) (_Tiny Code Generator_) which translates blocks of guest code (RISC-V for the Ibex core used in OpenTitan) into equivalent optimized host code (e.g. x86-64) for execution.
By using QEMU, tests and custom software stacks for OpenTitan can be executed and tested by integrators, all running on a single host device without requiring any specialized hardware.
This can often allow parallel execution at faster speeds than hardware simulation, at the cost of completely accurate behavior.

OpenTitan's emulated machines are currently developed on a [fork](https://github.com/lowRISC/qemu) of upstream QEMU to better facilitate the implementation of non-standard RISC-V extensions implemented in the Ibex CPU, and other extensions required to support OpenTitan functionality.
There are currently two main emulation targets: Earlgrey 1.0.0, and Darjeeling (targeting the moving `master` branch).
You can refer to the QEMU repository's documentation for more information on the development and usage of the QEMU OpenTitan machines - this page instead focuses on providing details for testing software with QEMU.

## Scope

Currently only the Earlgrey machine (`ot-earlgrey`) has any support within OpenTitanLib for test integration, primarily on the `earlgrey_1.0.0` branch.
It is important to note that emulation is **ongoing** and **incomplete** - there are many devices and features which are not yet implemented or are infeasible to emulate within QEMU.
Before using QEMU, it is strongly advised to read relevant QEMU [Earlgrey](https://github.com/lowRISC/qemu/blob/ot-9.2.0/docs/opentitan/ot_earlgrey.md) and [Darjeeling](https://github.com/lowRISC/qemu/blob/ot-9.2.0/docs/opentitan/ot_darjeeling.md) documentation pages to better understand whether the devices and features that you need are supported.
Note that these also may not be up-to-date compared to the implementation, and as such the source files should be treated as the root source of truth.
Furthermore, QEMU releases are pinned in Bazel, meaning that the supported features may differ compared to when this release was taken (see the [setup guide](./setup.md)).

As of the time of writing, there are several unimplemented devices and many devices with partial emulation / missing features.
The most important such examples to be aware of are:
* The Power manager slow FSM is bypassed, with no support for low pow power entry / deep sleeps.
* A pinmux block is implemented, but all connections currently go via a CharDev and do not interact with pinmux.
* Non-Maskable Interrupts (NMIs) are not implemented.
* Many other unsupported features, see the QEMU documentation.

Furthermore, note that synchronous (e.g. I2C) or timing-based (UART) communication peripherals are often limited in supported due to the inherent inaccuracy of emulation with QEMU.
As such, there may be limitations on what you can do using these peripherals.

## Considerations & Constraints

### Timing and Cycle Accuracy

QEMU is _not_ a cycle-accurate emulator, as its main goal is emulation speed:
* The instruction count reported in `mcycle` will not accurately reflect the number of instructions that have been executed.
* When using a hardware timer (e.g. the `aon_timer` or `rv_timer`), the timer will expire after _approximately_ the correct amount of time, but will not be exactly accurate.

QEMU has mechanisms for pacing the virtual CPU to match hardware timers, but in general it should be expected that both hardware timers and instruction counts are not correct in QEMU.
This can be a particular challenge for security countermeasures and software mechanisms that opt to set tight timing thresholds.
One potential solution is modifying the `icount` shift parameter, which informs the TCG's instruction counting feature for system emulation.
When providing an icount shift of `N`, the virtual CPU will execute one instruction every `2^N` nanoseconds of virtual time, meaning that changing this parameter may allow emulation to "pass" tighter timing checks at the cost of less accurate timing overall.
By default, an `icount` of 6 is used to align execution time with wall-clock time.

### The TLB and PMP

Hardware will often use a Translation Lookaside Buffer (TLB) as a high-speed cache to accelerate translation from virtual addresses to physical addresses.
QEMU mimics this concept with its own address translation cache that it calls the [TLB](https://www.qemu.org/docs/master/devel/tcg.html#mmu-emulation), which it uses to speed up translation of guest virtual addresses to guest RAM or to the operation handlers for MMIO regions defined by emulated devices.

It is worth being aware that partially or entirely invalidating the TLB (via mechanisms such as self-modifying flash code, or writes to PMP CSRs) can therefore decrease performance, as QEMU will temporarily lose the speedup from cached address translations.

One particularly important note is that for RISC-V target emulation, 4 KiB pages are used for caching.
When a PMP configuration is used that is not aligned to this page size, any address translation that falls within the misaligned region will not be cached nor make use of the TLB, due to the possibility of more granular PMP regions splitting a page with different permissions.
As a result, any code that falls in a misaligned PMP region will be executed with a _significant_ slowdown compared to regular execution.

Earlgrey's current PMP configurations tend to make use of fine-grained ranges for permissions to increase security posture, which means more potential for QEMU emulation to be slowed.
In particular, Earlgrey's ROM & ROM_EXT text sections (containing the executable code) and owner firmware are all delineated using fine-grained PMP ranges, meaning code at the end (and start, if starting at a misaligned offset) will see performance decreases.
The 4 byte stack guard placed at the top of stack may also cause issues when using all available stack.
For any hot loops in the code, this can result in a substantial increase in emulation time.
For example, the `sec_mmio` checks often cause large slowdowns in the ROM.

### Host Performance and Parallelism

As QEMU emulates by translating guest code to host instructions, the performance of QEMU will depend on the performance characteristics and processing load of the host device.
Although QEMU has mechanisms for pacing, this can mean that different behaviors or outcomes are observed when executing QEMU on different host devices - particularly with regards to timing.
One major advantage of QEMU is that tests can be executed in parallel, but doing so will also increase host processing load and may exacerbate timing differences.
Hence, if the most reliable performance is required, instances of QEMU should be serially executed (e.g. passing `--test_output=streamed` or using `-j 1` for Bazel testing).

Currently, large amounts of OpenTitan code are designed to only execute in FPGA or silicon environments, or sometimes in cycle-accurate simulation.
This means that there may be segments of code which make implicit timing assumptions that no longer hold true when emulating in QEMU.
As such, it may be required to conditionally change these timing assumptions for QEMU environments, or to modify the [`icount` parameter](#timing-and-cycle-accuracy) for a test to be able to meet timing checks.
Where possible, the host and device should ideally synchronize without making any implicit timing assumptions.

### Host Communication

For communication between host and device (e.g. via UART, SPI, GPIO, etc.) QEMU allows for the creation of [CharDevs](https://www.qemu.org/docs/master/system/device-emulation.html).
CharDevs are generic and flexible interfaces for communication, introducing an abstraction layer that supports a variety of protocols.
Host-device communication in OpenTitanTool mainly uses PTYs (pseudo serial ports) and TCP sockets.

Importantly, QEMU's lack of accurate cycle & timing emulation can limit the features that it is possible to emulate for these interfaces.
For example, all UART communication goes via the CharDev and is not based on sampling at timing intervals, and so it is not possible to support the [UART oversampling](https://opentitan.org/book/hw/ip/uart/doc/theory_of_operation.html#reception) mechanism.

### Flash Images and Bootstrapping

There is sufficient Earlgrey emulation and support for QEMU in OpenTitanLib to run flows that require bootstrapping firmware.
In spite of this, [slow emulation of the ROM](#the-tlb-and-pmp) means that we generally prefer to splice firmware into the initial flash image and avoid bootstrapping entirely.
This avoids the delay of bootstrapping and additional boot times from resetting, which can compound to a large increase in execution time across multiple test runs.

For software flows where it is genuinely desired to bootstrap firmware, appropriate [test parameters](#test-parameters) can be configured to use the bootstrapping flow instead, or a custom host harness or test command can be used.

## Testing

From the perspective of OpenTitan testing, QEMU is treated as a separate set of execution environments (e.g. `sim_qemu_rom_ext`) which use the QEMU transport interface in OpenTitanLib, allowing communication between the the host Rust code and the emulated QEMU OpenTitan device.

### Test parameters

Tests with a `sim_qemu_*` execution environment can be further configured by adding `qemu_params` to the test target.
The currently supported parameters are:

* `icount` (`int`): scale for Ibex's reported execution speed (`1GHz >> icount`) (defaults to 6).
* `globals` (`dict[str, str]`): global properties for the QEMU machine.
* `traces` (`[str]`): globs of [QEMU traces](https://qemu-project.gitlab.io/qemu/devel/tracing.html) to enable for debugging purposes.
QEMU accepts different trace event patterns with support for wildcard matching with an `"*"`.
* `qemu_args` (`[str]`): additional command line flags to pass to QEMU.
* `bootstrap` (`bool`): by setting to `True`, bootstrap test firmware instead of splicing a flash image.
Mutually exclusive with specifying a custom test harness.

Example:

```python
opentitan_test(
    name = "my_test",
    exec_env = {
      "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys": None,
    },
    qemu = qemu_params(
      icount = 5,
      globals = {
        "ot-aes.fast-mode": "false",
      },
      qemu_args = {
        "-s", # spawn GDB server
      },
      traces = [
        "ot_spi_device*",
      ],
    ),
    # ...
)
```

### Command-line arguments

It can often be inconvenient to manually modify test targets to contain the desired list of QEMU arguments whilst debugging.
In particular, manually adding and removing traces can quickly become unwieldy.

Instead, you can pass in arguments to QEMU as command-line arguments using the form `--qemu-arg="X"` or `--qemu-args="X Y Z"`.
The former forwards a single argument `X` to QEMU, whereas the latter forwards `X`, `Y` and `Z` each as _different_ arguments to QEMU.

For example, to manually add some traces for the USB device and alert updates whilst debugging a test, you might run:
```
./bazelisk.sh test //path_to_qemu_test:my_test --test_arg=--qemu-args="--trace ot_usbdev* --trace ot*update_alert*"
```

### Logging

When executing a test in a QEMU execution environment, the default behavior is that the QEMU log output stream is combined with the regular UART console output stream.
When both interfaces are simultaneously written, it is possible that output may be disrupted by the characters interleaved from both streams.
This can be particularly noticeable when tracing, where the QEMU log is often written much faster than regular console output.
These outputs are not currently buffered by line breaks before combining the streams, meaning that it is possible for one line of console output to be split across multiple QEMU log lines.
