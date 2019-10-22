---
title: "Quickstart"
---

# Quickstart

The environment variable `$REPO_TOP` is the top-level of the git source tree.

## Simulation with Verilator

_Make sure you followed the install instructions to [prepare the system]({{< relref "install_instructions#system-preparation" >}}) and to install the [software development tools]({{< relref "install_instructions#software-development" >}}) and [Verilator]({{< relref "install_instructions#verilator" >}})._

Build the simulator and the software and then run the simulation

```console
$ cd $REPO_TOP
$ fusesoc --cores-root . run --target=sim --setup --build lowrisc:systems:top_earlgrey_verilator
$ make SIM=1 -C sw/device/boot_rom clean all
$ make SIM=1 -C sw/device/examples/hello_world clean all
$ build/lowrisc_systems_top_earlgrey_verilator_0.1/sim-verilator/Vtop_earlgrey_verilator --rominit=sw/device/boot_rom/rom.vmem \
$ --flashinit=sw/device/examples/hello_world/sw.vmem
```

See the [Getting Started with Verilator Guide]({{< relref "getting_started_verilator.md" >}}) for more information.

## Running on an FPGA

_Make sure you followed the install instructions to [prepare the system]({{< relref "install_instructions#system-preparation" >}}) and to install the [software development tools]({{< relref "install_instructions#software-development" >}})._

Do you want to try out the design without installing EDA tools and waiting for a long build?
Then you have come to the right place!

You need the following things:

* A [Nexys Video FPGA board](https://store.digilentinc.com/nexys-video-artix-7-fpga-trainer-board-for-multimedia-applications/)
  (Unfortunately we do not provide presynthesized bitstreams for other FPGA boards right now.)
* A USB pen drive or a microSD card (TODO: specify minimum size)

Once you have obtained these things, follow these steps to get started.

1. Download a release bitstream from the [OpenTitan Github Releases page](https://github.com/lowRISC/opentitan/releases).
2. Connect the Nexys Video board to your PC over USB.
   TODO: Give good instructions on permission problems/udev rules.
3. Follow the instructions in Section 2.3 of [NexysVideo reference manual](https://reference.digilentinc.com/_media/reference/programmable-logic/nexys-video/nexysvideo_rm.pdf) to prepare the MicroSD card or the USB pen drive, and to configure the FPGA with this bitstream.
4. TODO: include steps on how to build software, spiflash it, and expectations on what should be seen on the board when the software works.


See the [Getting Started on FPGAs Guide]({{< relref "getting_started_fpga.md" >}}) for full instructions how to build your own bitstream.
