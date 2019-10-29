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
* An empty USB pen drive or microSD card (at least 16 MB)
* `fdisk` utility installed on your machine.
  ```
  sudo apt-get install fdisk
  ```

Once you have obtained these things, follow these steps to get started.

For more info refer to Section 2.3 of [Nexys Video reference manual](https://reference.digilentinc.com/_media/reference/programmable-logic/nexys-video/nexysvideo_rm.pdf).

### Prepare a storage device with the FPGA bitstream

**Note**: you may need to be an admin on your machine in order to mount and format external storage devices.
If you are, and some of the commands run into permission errors, run them in `sudo` mode.

1.  Download a release bitstream from the [OpenTitan Github Releases page](https://github.com/lowRISC/opentitan/releases).
2.  Insert microSD/USB pen to your machine.
3.  Run `fdisk -l` to find where the device was mapped.
    See an example mapping below, where an SD device was mapped as */dev/mmcblk0p1*.

        ```
        $ fdisk -l
        ...
        Disk /dev/mmcblk0: 14.9 GiB, 15931539456 bytes, 31116288 sectors
        Units: sectors of 1 * 512 = 512 bytes
        Sector size (logical/physical): 512 bytes / 512 bytes
        I/O size (minimum/optimal): 512 bytes / 512 bytes
        Disklabel type: dos
        Disk identifier: 0x00000000

        Device         Boot Start      End  Sectors  Size Id Type
        /dev/mmcblk0p1       8192 31116287 31108096 14.9G  c W95 FAT32 (LBA)
        ```

4.  Format the device to  *FAT32* format.
    ```bash
    mkfs.fat -F 32 /dev/mmcblk0p1
    ```

5.  Mount the device by running the following commands:

    ```bash
    mkdir -p ~/ot-img-mount  # Can be a different name
    mount -t vfat /dev/mmcblk0p1 ~/ot-img-mount  # Change according to mount/dev
    ```

6.  Make sure the device is empty. `ls ~/ot-img-mount` should not print anything.
7.  Copy the bit file image to the storage device.
    ```bash
    cp hw/top_earlgrey/lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit ~/ot-img-mount/
    ```

### Program the FPGA with a bitstream from the storage device

1.  Connect the USB pen drive or the microSD card to the Nexys Video board.
    The microSD slot sits on the bottom of the board and marked "SD MICRO", USB header is in the top and marked "USB HOST".
1.  Place JP4 on the pins marked USB/SD.
1.  Place JP3 according to the selected device (marked either USB or SD).
1.  Push the PROG button. Done LED (LD014) should be steadily on.
1.  Wait for the Done LED to be turned off.

### Run software on the FPGA

**Note**: Your user account needs to have access to connected USB devices.
See [the section udev rules of the installation guide](install_instructions.md#device-permissions-udev-rules) for more details.

The reference FPGA bitstream contains a valid boot ROM that will print a message to UART upon boot.

In order to see the printout, follow these instructions:
1.  Connect a micro USB cable from your machine to the UART connector (J13) on Nexys Video board.
1.  Use `dmesg` to determine which serial port was assigned. It should be named `/dev/ttyUSB*`, e.g. `/dev/ttyUSB0`.
1.  Open a serial console (use the device file determined before) and connect.
    Settings: 230400 baud, 8N1, no hardware or software flow control.

    ```bash
    screen /dev/ttyUSB0 230400
    ```

1.  On the Nexys Video board, press the red button labeled CPU_RESET.
2.  Observe the terminal output, it should show a ROM boot message like this:

    ```
    Commit ID:  1961a5f3e87f1d2c078c58c7cfb009a125af481e
    Build Date: 2019-10-23, 15:25:44
    Jump!
    ```

3.  To exit `screen` press <kbd>CTRL</kbd>+<kbd>A</kbd> keys together, then press <kbd>K</kbd>, and then confirm exit by pressing <kbd>y</kbd>.

Instructions for flashing your own RISC-V program, and creating your own design bitstream, can be found in the [Getting Started on FPGAs Guide]({{< relref "getting_started_fpga.md" >}}).

