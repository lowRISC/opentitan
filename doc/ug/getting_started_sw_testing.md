---
title: Test Software
---

## Prerequisites

_Make sure you followed the install instructions to [prepare the system]({{< relref "install_instructions#system-preparation" >}}) and to install the [software development tools]({{< relref "doc/ug/install_instructions#software-development" >}}) and [Verilator]({{< relref "install_instructions#verilator" >}})._

## Overview

The OpenTitan software tests fall into two main categories:

* Unit tests
* Smoke tests

Unit tests are designed to run on the host so they are quick to build and run.
Writing unit tests is a good way to provide high levels of test coverage for a library without significantly impacting the runtime of the continuous integration tests.
Smoke tests on the other hand are designed to run on an emulated device and therefore require a more complicated setup procedure.
Typically smoke tests take significantly longer to run than unit tests.
Smoke tests are therefore best suited for testing that the core functionality of a library is correct.

## Unit tests

OpenTitan unit tests are written using the [GoogleTest](https://github.com/google/googletest/) C++ test framework and are designed to be run on a workstation.
Typically this means that they are executed in a Linux environment running on the x86_64 architecture although they should be designed to be as portable as possible.
Device-specific features that are not necessarily available on the host system, for example memory-mapped I/O (MMIO) and Ibex control registers (CSRs), may be provided by mock implementations.

Unit tests use the suffix `_unittest.cc` and are typically contained in the same directory as other tests for the same code.

The unit tests may be executed by invoking the ninja test target:

```console
# Configure the Meson environment.
$ cd "$REPO_TOP"
$ ./meson_init.sh

# Build and run the unit tests.
$ ninja -C build-out test
```

## Device smoke tests

OpenTitan tests that are designed to be executed on the target device itself are referred to as ‘smoke tests’.
Smoke tests are full applications written in a language suitable for the target device such as C.
The target device may be emulated using either software simulation or a programmable hardware device (FPGA).

The name ‘smoke test’ is used to describe device tests because they are not typically as comprehensive as unit tests that target the host.
This is because device emulation, especially when using a software simulation, is relatively slow.
Therefore the execution time of smoke tests needs to be kept as low as possible.

Smoke tests use the suffix `_smoketest.c` and are usually found in the same directory as other tests for the same code.

To build a software simulation of the target device run the following command:

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  The software simulation needs to be rebuilt every time the source code for the hardware changes.
  The `fusesoc` command should therefore be re-run every time a branch is checked out or a git pull/rebase operation is performed.

  Failure to rebuild the software simulator may result in the tests failing.
</div>

```console
# Build Verilator simulation.
$ cd "$REPO_TOP"
$ fusesoc --cores-root . run --flag=fileset_top --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator
```

Once built the simulator needs to be made available to the test infrastructure.
This is done by moving it to the `build-bin/hw` folder.
If your workflow is likely to consist solely of simulation tests (i.e. you do not expect to test on FPGAs frequently) then you may find it useful to simply link the `build-bin/hw` directory to the simulation output directory:

```console
# Make Verilator simulation available to test infrastructure.
$ mkdir build-bin/hw
$ ln -sf "$(pwd)/build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator" build-bin/hw/top_earlgrey
```

The smoke test binaries are not built as part of the simulator.
They are separate applications that need to be built independently.
To build all of the applications for all targets:

```console
# Configure the Meson environment.
$ ./meson_init.sh

# Build all of the targets.
$ ninja -C build-out all
```

The smoke tests may be executed using pytest.
Depending on the performance of your workstation these tests may take anywhere from a few minutes to several hours to complete:

```console
# Run the smoke tests on a device simulated using Verilator.
$ pytest test/systemtest/earlgrey/test_sim_verilator.py
```

For more detailed information about the options available to `pytest` and how to target an FPGA see [system tests](/test/systemtest/README/).
