# FPGA Reference Manual

This manual provides additional usage details about the FPGA.
Specifically, it provides instructions on SW development flows and testing procedures.
Refer to the [FPGA Setup](../../getting_started/setup_fpga.md) guide for more information on initial setup.

## FPGA SW Development Flow

The FPGA is meant for both boot ROM and general software development.
The flow for each is different, as the boot ROM is meant to be fairly static while general software can change very frequently.
However, for both flows, you must have OpenTitanTool set up with the ability to load memories via JTAG over OpenOCD.
See the instructions described [here](../../getting_started/setup_fpga.md).

### Boot ROM development

The FPGA bitstream is built after compiling whatever code is sitting in `sw/device/lib/testing/test_rom`.
This binary is used to initialize internal FPGA memory and is part of the bitstream directly.

To update this content without rebuilding the FPGA, you must use the dedicated `bkdr_loader` IP to program the ROM.
First, you must flash the existing base bitstream onto the FPGA with `opentitantool`.
Then, you can use the backdoor loader to overwrite the ROM image on the FPGA.
See the [FPGA Setup guide](../../getting_started/setup_fpga.md#programming-the-fpga-with-rom--otp-images) for a detailed guide on how this can be done.

### General Software Development

After building, the FPGA bitstream contains only the boot ROM.
Using this boot ROM, the FPGA is able to load additional software to the emulated flash, such as software in the `sw/device/tests` and `sw/device/examples` and `sw/device/crypto` directories.
To load additional software, `opentitantool` is required.

Note that whichever binary you wish to load needs to be built first.
For the purpose of this demonstration, we will use `sw/device/examples/hello_world`, but it applies to any software image that is able to fit in the emulated flash space.
The example below builds the `hello_world` image and loads it onto the FPGA.

```console
$ cd ${REPO_TOP}
$ bazel run //sw/host/opentitantool fpga set-pll # This needs to be done only once.
$ bazel build //sw/device/examples/hello_world:hello_world_fpga_cw340_bin
$ bazel run //sw/host/opentitantool bootstrap $(ci/scripts/target-location.sh //sw/device/examples/hello_world:hello_world_fpga_cw340_bin)
```

Uart output:
```
I00000 test_rom.c:81] Version: earlgrey_silver_release_v5-5886-gde4cb1bb9, Build Date: 2022-06-13 09:17:56
I00001 test_rom.c:87] TestROM:6b2ca9a1
I00000 test_rom.c:81] Version: earlgrey_silver_release_v5-5886-gde4cb1bb9, Build Date: 2022-06-13 09:17:56
I00001 test_rom.c:87] TestROM:6b2ca9a1
I00002 test_rom.c:118] Test ROM complete, jumping to flash!
I00000 hello_world.c:66] Hello World!
I00001 hello_world.c:67] Built at: Jun 13 2022, 14:16:59
I00002 demos.c:18] Watch the LEDs!
I00003 hello_world.c:74] Try out the switches on the board
I00004 hello_world.c:75] or type anything into the console window.
I00005 hello_world.c:76] The LEDs show the ASCII code of the last character.
```

For more details on the exact operation of the loading flow and how the boot ROM processes incoming data, please refer to the [boot ROM readme](https://github.com/lowRISC/opentitan/tree/master/sw/device/lib/testing/test_rom).

### Accelerating `git bisect` with the bitstream cache

To set the stage, let's say you've discovered a test regression.
The test used to pass on `GOOD_COMMIT`, but now it fails at `BAD_COMMIT`.
Your goal is to find the *first bad commit*.

In general, a linear search from `GOOD_COMMIT` to `BAD_COMMIT` is one of the slowest ways to find the first bad commit.
We can save time by testing fewer commits with `git bisect`, which effectively applies binary search to the range of commits.
We can save even more time by leveraging the bitstream cache with **[`//util/fpga:bitstream_bisect`](https://github.com/lowRISC/opentitan/tree/master/util/fpga/bitstream_bisect.py)**.

The `:bitstream_bisect` tool is faster than regular `git bisect` because it restricts itself to cached bitstreams until it can make no more progress.
Building a bitstream is many times slower than running a test (hours compared to minutes), and `git bisect` has no idea that some commits will be faster to classify than others due to the bitstream cache.
Note that by default, the FPGA test setup will always make use of a cached bitstream - so this advice only applies if bisecting with `--define bitstream=vivado`.

For example, suppose that `//sw/device/tests:uart_smoketest` has regressed sometime in the last 30 commits.
The following command could easily save hours compared to a naive `git bisect`:

```sh
# This will use the fast command to classify commits with cached bitstreams. If
# the results are ambiguous, it will narrow them down with the slow command.
./bazelisk.sh run //util/fpga:bitstream_bisect -- \
    --good HEAD~30 \
    --bad HEAD \
    --fast-command "./bazelisk.sh test //sw/device/tests:uart_smoketest_fpga_cw340_rom" \
    --slow-command "./bazelisk.sh test --define bitstream=vivado //sw/device/tests:uart_smoketest_fpga_cw340_rom"
```

One caveat is that neither `git bisect` nor `:bitstream_bisect` will help if the FPGA somehow retains state between tests.
That is, if the test command bricks the FPGA causing future tests to fail, bisection will return entirely bogus results.
For now, if you suspect this kind of FPGA flakiness, the best strategy may be a linear progression from `GOOD_COMMIT` to `BAD_COMMIT`.

Note that the slow command doesn't necessarily have to build a bitstream.
If you don't have a Vivado license and the test regression is reproducible in Verilator, it could make sense to fall back to the Verilated test.
Building on the example above, you could replace the slow command with `"./bazelisk.sh test //sw/device/tests:uart_smoketest_sim_verilator"` and the `:bitstream_bisect` tool would never build any bitstreams.

For more information, consult the `:bitstream_bisect` tool directly!

```sh
./bazelisk.sh run //util/fpga:bitstream_bisect -- --help
```

## Implementation of Bitstream Caching and Splicing

This section gives an overview of where bitstreams are generated, how they are uploaded to the GCP cache, and how Bazel reaches into the cache.

OpenTitan runs CI tasks on GitHub Actions that build FPGA bitstreams.
A full bitstream build can take hours, so we cache the output artifacts in a GCS bucket.
These cached bitstreams can be downloaded and used as-is, or with additional programmed components such as the ROM and OTP image.

### Building bitstreams on CI and uploading artifacts to GCS

The `chip_earlgrey_cw340` CI job builds the `//hw/bitstream/vivado:fpga_cw340` target which will build a bitstream with the test ROM and RMA OTP image.
The following files are produced as a result:

* `lowrisc_systems_chip_earlgrey_cw340_0.1.bit` (Base CW340 bitstream - Test ROM and RMA OTP images)
* `lowrisc_systems_chip_earlgrey_cw340_0.1.runs` (information about the Synthesis & Implementation runs)
* `memories.mmi` (a dummy MMI file used by the legacy bitstream splicing flow - to be removed in the future).

If CI is working on the `master` branch, it puts selected build artifacts into a tarball, which it then uploads to the GCS bucket. The latest tarball is available here: https://storage.googleapis.com/opentitan-bitstreams/master/bitstream-latest.tar.gz

### Exposing GCS-cached artifacts to Bazel

The `@bitstreams//` workspace contains autogenerated Bazel targets for the GCS-cached artifacts.
This magic happens in `rules/scripts/bitstreams_workspace.py`.
Under the hood, it fetches the latest tarball from the GCS bucket and constructs a BUILD file that defines one target per artifact.

One meta-level up, we have targets in `//hw/bitstream` that decide whether to use cached artifacts or to build them from scratch.
By default, these targets use cached artifacts by pulling in their corresponding `@bitstreams//` targets.
