# Verilator Setup

_Before following this guide, make sure you've followed the [dependency installation instructions](README.md)._

## About Verilator

Verilator is a cycle-accurate simulation tool.
It translates synthesizable Verilog code into a simulation program in C++, which is then compiled and executed.

### Install Verilator

Even though Verilator is packaged for most Linux distributions, these versions tend to be too old to be usable.
We recommend compiling Verilator from source, as outlined here.

Fetch, build and install Verilator itself (this should be done outside the `$REPO_TOP` directory).
Note that Verilator 4.210 will not build with GCC 12.0 or later, so it will need to be built with an older toolchain.
The example below assumes gcc-11 and g++-11 are installed on the system.

```console
export VERILATOR_VERSION={{#tool-version verilator }}

git clone https://github.com/verilator/verilator.git
cd verilator
git checkout v$VERILATOR_VERSION

autoconf
CC=gcc-11 CXX=g++-11 ./configure --prefix=/tools/verilator/$VERILATOR_VERSION
CC=gcc-11 CXX=g++-11 make
sudo CC=gcc-11 CXX=g++-11 make install
```
The `make` step can take several minutes.

After installation you need to add `/tools/verilator/$VERILATOR_VERSION/bin` to your `PATH` environment variable.
Also add it to your `~/.bashrc` or equivalent so that it's on the `PATH` in the future, like this:
```console
export PATH=/tools/verilator/$VERILATOR_VERSION/bin:$PATH
```

Check your installation by running:
```console
$ verilator --version
Verilator 4.210 2021-07-07 rev v4.210 (mod)
```

#### Troubleshooting

If you need to install to a different location than `/tools/verilator/...`, you can pass a different directory to `./configure --prefix` above and add `your/install/location/bin` to `PATH` instead.

## Use Bazel to run software on a verilator simulation

First the RTL must be built into a simulator binary.
This is done by running fusesoc, which collects up RTL code and passes it to Verilator to generate and then compile a C++ model.
Next software must be built to run on the simulated hardware.
There are 4 memory types on OpenTitan hardware: ROM, Flash, OTP, and SRAM.
Software images need to be provided for ROM, Flash, and OTP (SRAM is populated at runtime).
By default, the system will first execute out of ROM and then jump to Flash.
The OTP image does not contain executable code, rather it contains root secrets, runtime configuration data, and life cycle state.
(By default, the life cycle state is set to RMA, which enables debugging features such as the JTAG interface for the main processor.)
Lastly, the Verilator simulation binary must be run with the correct arguments.

Thankfully, Bazel (and `opentitantool`) simplify this process by providing a single interface for performing all of the above steps.
Moreover, Bazel automatically connects to the simulated UART (via `opentitantool`) to print the test output in real time.

For example, to run the UART smoke test on Verilator simulated hardware, and see the output in real time, use
```console
cd $REPO_TOP
bazel test --test_output=streamed //sw/device/tests:uart_smoketest_sim_verilator
```
or
```console
cd $REPO_TOP
bazel test --test_tag_filters=verilator --test_output=streamed //sw/device/tests:uart_smoketest
```

You should expect to see something like:
```console
Invoking: sw/host/opentitantool/opentitantool --rcfile= --logging=info --interface=verilator --verilator-bin=hw/build.verilator_real/sim-verilator/Vchip_sim_tb --verilator-rom=sw/device/lib/testing/test_rom/test_rom_sim_verilator.scr.39.vmem --verilator-flash=sw/device/tests/uart_smoketest_prog_sim_verilator.64.scr.vmem --verilator-otp=hw/ip/otp_ctrl/data/img_rma.vmem console --exit-failure=(FAIL|FAULT).*\n --exit-success=PASS.*\n --timeout=3600s
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::subprocess] Spawning verilator: "hw/build.verilator_real/sim-verilator/Vchip_sim_tb" ["--meminit=rom,sw/device/lib/testing/test_rom/test_rom_sim_verilator.scr.39.vmem", "--meminit=flash,sw/device/tests/uart_smoketest_prog_sim_verilator.64.scr.vmem", "--meminit=otp,hw/ip/otp_ctrl/data/img_rma.vmem"]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] Simulation of OpenTitan Earl Grey
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] =================================
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] Tracing can be toggled by sending SIGUSR1 to this process:
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] $ kill -USR1 3422749
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] GPIO: FIFO pipes created at $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/gpio0-read (read) and $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/gpio0-write (write) for 32-bit wide GPIO.
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] GPIO: To measure the values of the pins as driven by the device, run
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] $ cat $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/gpio0-read  # '0' low, '1' high, 'X' floating
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] GPIO: To drive the pins, run a command like
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] $ echo 'h09 l31' > $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/gpio0-write  # Pull the pin 9 high, and pin 31 low.
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] SPI: Created /dev/pts/9 for spi0. Connect to it with any terminal program, e.g.
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] $ screen /dev/pts/9
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] NOTE: a SPI transaction is run for every 4 characters entered.
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] SPI: Monitor output file created at $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/spi0.log. Works well with tail:
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] $ tail -f $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/spi0.log
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] UART: Created /dev/pts/10 for uart0. Connect to it with any terminal program, e.g.
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] $ screen /dev/pts/10
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] UART: Additionally writing all UART output to 'uart0.log'.
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] USB: Monitor output file created at $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/usb0.log. Works well with tail:
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] $ tail -f $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/usb0.log
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] JTAG: Virtual JTAG interface dmi0 is listening on port 44853. Use
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] OpenOCD and the following configuration to connect:
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]   interface remote_bitbang
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]   remote_bitbang_host localhost
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]   remote_bitbang_port 44853
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout] Simulation running, end by pressing CTRL-c.
[2022-06-09T08:08:16Z INFO  opentitanlib::transport::verilator::stdout]
[2022-06-09T08:08:17Z INFO  opentitanlib::transport::verilator::transport] Verilator started with the following interaces:
[2022-06-09T08:08:17Z INFO  opentitanlib::transport::verilator::transport] gpio_read = $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/gpio0-read
[2022-06-09T08:08:17Z INFO  opentitanlib::transport::verilator::transport] gpio_write = $HOME/.cache/bazel/_bazel_ttrippel/3d92022c091a734228e22679f3ac7c7f/execroot/lowrisc_opentitan/bazel-out/k8-fastbuild/bin/sw/device/tests/uart_smoketest_sim_verilator.runfiles/lowrisc_opentitan/gpio0-write
[2022-06-09T08:08:17Z INFO  opentitanlib::transport::verilator::transport] uart = /dev/pts/10
[2022-06-09T08:08:17Z INFO  opentitanlib::transport::verilator::transport] spi = /dev/pts/9
Starting interactive console
[CTRL+C] to exit.

I00000 test_rom.c:81] Version:    earlgrey_silver_release_v5-5775-gefa09d3b8
Build Date: 2022-06-09, 00:12:35

I00001 test_rom.c:118] Test ROM complete, jumping to flash!
I00000 status.c:28] PASS!


Exiting interactive console.
[2022-06-09T08:09:38Z INFO  opentitantool::command::console] ExitSuccess("PASS!\r\n")
```

**For most use cases, interacting with the UART is all you will need and you can stop here.**
However, if you want to interact with the simulation in additional ways, there are more options listed below.

## Execution Log

All executed instructions in the loaded software into Verilator simulations are logged to the file `trace_core_00000000.log`.
By default this file is stored in a subdirectory of `~/.cache/bazel`.
You can find it using the following command:

```console
find ~/.cache/bazel -name "trace_core_00000000.log"
```

The columns in this file are tab separated; change the tab width in your editor if the columns don't appear clearly, or open the file in a spreadsheet application.

## Interact with GPIO (optional)

The simulation includes a DPI module to map general-purpose I/O (GPIO) pins to two POSIX FIFO files: one for input, and one for output.
Observe the `gpio0-read` file for outputs (in the same directory as the trace):

```console
cat gpio0-read
```

To drive input pins write to the `gpio0-write` file.
A command consists of the desired state: `h` for high, and `l` for low, and the decimal pin number.
Multiple commands can be issued by separating them with a single space.

```console
echo 'h09 l31' > gpio0-write  # Pull the pin 9 high, and pin 31 low.
```

## Connect with OpenOCD to the JTAG port and use GDB (optional)

The simulation includes a "virtual JTAG" port to which OpenOCD can connect using its `remote_bitbang` driver.
All necessary configuration files are included in this repository.

For more guidance on using OpenOCD, see [Using OpenOCD](./using_openocd.md).

Run the simulation with Bazel, making sure to build the device software with debug symbols using
```console
cd $REPO_TOP
bazel test --copt=-g --test_output=streamed //sw/device/tests:uart_smoketest_sim_verilator
```

Then, connect with OpenOCD using the following command.

```console
cd $REPO_TOP
/tools/openocd/bin/openocd -s util/openocd -f board/lowrisc-earlgrey-verilator.cfg
```

Lastly, connect GDB using the following command (noting it needs to be altered to point to the sw binary in use).

```console
cd $REPO_TOP
riscv32-unknown-elf-gdb -ex "target extended-remote :3333" -ex "info reg" \
  "$(./bazelisk.sh outquery --config=riscv32 //sw/device/tests:uart_smoketest_prog_sim_verilator.elf)"
```

## SPI device test interface (optional)

The simulation contains code to monitor the SPI bus and provide a host interface to allow interaction with the `spi_device`.
When starting the simulation you should see a message like

```console
SPI: Created /dev/pts/4 for spi0. Connect to it with any terminal program, e.g.
$ screen /dev/pts/4
NOTE: a SPI transaction is run for every 4 characters entered.
SPI: Monitor output file created at /auto/homes/mdh10/github/opentitan/spi0.log. Works well with tail:
$ tail -f /auto/homes/mdh10/github/opentitan/spi0.log
```

Use any terminal program, e.g. `screen` or `microcom` to connect to the simulation.

```console
screen /dev/pts/4
```

Microcom seems less likely to send unexpected control codes when starting:
```console
microcom -p /dev/pts/4
```

The terminal will accept (but not echo) characters.
After 4 characters are received a 4-byte SPI packet is sent containing the characters.
The four characters received from the SPI transaction are echoed to the terminal.
The `hello_world` code will print out the bytes received from the SPI port (substituting _ for non-printable characters).
The `hello_world` code initially sets the SPI transmitter to return `SPI!` (so that should echo after the four characters are typed) and when bytes are received it will invert their bottom bit and set them for transmission in the next transfer (thus the Nth set of four characters typed should have an echo of the N-1th set with bottom bit inverted).

The SPI monitor output is written to a file.
It may be monitored with `tail -f` which conveniently notices when the file is truncated on a new run, so does not need restarting between simulations.
The output consists of a textual "waveform" representing the SPI signals.

## Generating waveforms (optional)

With the `--trace` argument the simulation generates a FST signal trace which can be viewed with Gtkwave (only).
An argument may be provided to `--trace` to specify where the trace file will be saved.
Note that for automated tests, `opentitantool` interfaces with the simulator, and verilator arguments must be passed via `--verilator-args=<arg>`.

In addition, it may be necessary to adjust the test timeout values when using `bazel test` with waveforms.
Tracing slows down the simulation by roughly factor of 1000.
The timeout adjustment may be done via bazel's `--test_timeout` option.
Putting these all together for the UART smoke test yields the following command line:

```console
cd $REPO_TOP
bazel test //sw/device/tests:uart_smoketest_sim_verilator \
  --test_output=streamed \
  --test_timeout=1000 \
  --test_arg=--verilator-args=--trace=/tmp/sim.fst
gtkwave /tmp/sim.fst
```

Without an argument to `--trace`, the waveform file would be named `sim.fst` and be placed in the test's [runfiles](https://bazel.build/reference/test-encyclopedia#runfiles) tree.
It would appear alongside the simulator's other outputs in the test's working directory.
