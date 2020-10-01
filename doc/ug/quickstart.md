---
title: "Quickstart"
---

## Install required packages

To follow the guide below the following things must be installed:

* xz-utils
* screen
* fdisk
* libusb 1.x
* libftdi1 1.x
* usbutils
* libelf1

Under Ubuntu these can be installed with:
```console
$ sudo apt-get install xz-utils screen fdisk libftdi1-2 libusb-1.0-0 usbutils libelf1
```

## Extract the release

Download a release bitstream from the [OpenTitan GitHub Releases page](https://github.com/lowRISC/opentitan/releases) and extract it.
`$OT_TOP` refers to the location where it is extracted.

```console
$ mkdir -p $OT_TOP
$ tar -C $OT_TOP -xvf opentitan-snapshot-20191101-1.tar.xz --strip-components=1
```

(Replace opentitan-snapshot-20191101-1.tar.xz with the release you downloaded if you have downloaded a different version)

## Simulation with Verilator

Run the provided simulator binary with 
```console
$ cd $OT_TOP
$ ./hw/top_earlgrey/Vtop_earlgrey_verilator --rominit=./sw/device/sim/boot_rom/rom.vmem --flashinit=./sw/device/sim/examples/hello_world/sw.vmem

Simulation of OpenTitan Earl Grey
=================================

Tracing can be toggled by sending SIGUSR1 to this process:
$ kill -USR1 19351

Rom initialized with program at ./sw/device/sim/boot_rom/rom.vmem

Flash initialized with program at ./sw/device/sim/examples/hello_world/sw.vmem

GPIO: FIFO pipe created at /home/greg/work/opentitan_builds/ot/gpio0 for 32 bit wide GPIO. Run
$ cat /home/greg/work/opentitan_builds/ot/gpio0
to observe the output.

JTAG: Virtual JTAG interface jtag0 is listening on port 44853. Use
OpenOCD and the following configuration to connect:
  interface remote_bitbang
  remote_bitbang_host localhost
  remote_bitbang_port 44853

SPI: Created /dev/pts/4 for spi0. Connect to it with any terminal program, e.g.
$ screen /dev/pts/4
NOTE: a SPI transaction is run for every 4 characters entered.
SPI: Monitor output file created at /home/greg/work/opentitan_builds/ot/spi0.log. Works well with tail:
$ tail -f /home/greg/work/opentitan_builds/ot/spi0.log

UART: Created /dev/pts/6 for uart0. Connect to it with any terminal program, e.g.
$ screen /dev/pts/6

Simulation running, end by pressing CTRL-c.
TOP.top_earlgrey_verilator.top_earlgrey.core.ibex_tracer_i: Writing execution trace to trace_core_00000000.log
```

Note the UART output will be available on `/dev/pts/N`, `/dev/pts/6` in this example.
Use `cat` to view the UART output to see everything that has been output since simulation start.

```console
$ cat /dev/pts/6
Commit ID:  1d0d927693c2ef60d7880ab306beb25115a53dcb
Build Date: 2019-11-01, 15:57:42
Jump!
Hello World! Nov  1 2019 15:57:49
Watch the LEDs!
Try out the switches on the board
or type anything into the console window.
The LEDs show the ASCII code of the last character.
```

See the [Getting Started with Verilator Guide]({{< relref "getting_started_verilator.md" >}}) for more information.

## Running on an FPGA

Do you want to try out the design without installing EDA tools and waiting for a long build?
Then you have come to the right place!

You need the following things:

* A [Nexys Video FPGA board](https://store.digilentinc.com/nexys-video-artix-7-fpga-trainer-board-for-multimedia-applications/)
  (Unfortunately we do not provide presynthesized bitstreams for other FPGA boards right now.)
* An empty USB pen drive or microSD card (at least 16 MB)
* `fdisk` utility installed on your machine.

Once you have obtained these things, follow these steps to get started.

### Prepare a storage device with the FPGA bitstream

**Note**: you may need to be an admin on your machine in order to mount and format external storage devices.
If you are, and some of the commands run into permission errors, run them in `sudo` mode.

1.  Insert microSD/USB pen to your machine.
2.  Run `fdisk -l` to find where the device was mapped.
    See an example mapping below, where an SD device was mapped as */dev/mmcblk0p1*.

    ```console
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

3.  Format the device to  *FAT32* format.
    ```console
    $ mkfs.fat -F 32 /dev/mmcblk0p1
    ```

4.  Mount the device by running the following commands:

    ```console
    $ mkdir -p ~/ot-img-mount  # Can be a different name
    $ mount -t vfat /dev/mmcblk0p1 ~/ot-img-mount  # Change according to mount/dev
    ```

5.  Make sure the device is empty. `ls ~/ot-img-mount` should not print anything.
6.  Copy the bit file image to the storage device.
    ```console
    $ cd $OT_TOP
    $ cp hw/top_earlgrey/lowrisc_systems_top_earlgrey_nexysvideo_0.1.bit ~/ot-img-mount/
    ```

For more information on programming the Nexsys Video FPGA board refer to Section 2.3 of [Nexys Video reference manual](https://reference.digilentinc.com/_media/reference/programmable-logic/nexys-video/nexysvideo_rm.pdf).

### Program the FPGA with a bitstream from the storage device

1.  Connect the USB pen drive or the microSD card to the Nexys Video board.
    The microSD slot sits on the bottom of the board and marked "SD MICRO", USB header is in the top and marked "USB HOST".
2.  Place JP4 on the pins marked USB/SD.
3.  Place JP3 according to the selected device (marked either USB or SD).
4.  Push the PROG button. The BUSY LED (LD14) should be steadily on.
5.  Wait for the BUSY LED to turn off, DONE (LD15) should turn on.

### Run software on the FPGA

**Note**: Your user account needs to have access to connected USB devices.
See [the section udev rules of the installation guide]({{< relref "install_instructions#device-permissions-udev-rules" >}}) for more details.

1.  Connect a micro USB cable from your machine to the UART connector (J13) on Nexys Video board.
2.  Use `dmesg` to determine which serial port was assigned:

    ```console
    $ dmesg
    [23426.869858] usb 1-3: new full-speed USB device number 27 using xhci_hcd
    [23427.023299] usb 1-3: New USB device found, idVendor=0403, idProduct=6001, bcdDevice= 6.00
    [23427.023301] usb 1-3: New USB device strings: Mfr=1, Product=2, SerialNumber=3
    [23427.023301] usb 1-3: Product: FT232R USB UART
    [23427.023302] usb 1-3: Manufacturer: FTDI
    [23427.023303] usb 1-3: SerialNumber: A503XQQS
    [23427.026674] ftdi_sio 1-3:1.0: FTDI USB Serial Device converter detected
    [23427.026691] usb 1-3: Detected FT232RL
    [23427.027019] usb 1-3: FTDI USB Serial Device converter now attached to ttyUSB0
    ```

    It should be named `/dev/ttyUSB*` in this example it is `/dev/ttyUSB0`.
3.  Open a serial console (use the device file determined before) and connect.
    Settings: 115200 baud, 8N1, no hardware or software flow control.
    `screen` needs to be installed first.

    ```console
    $ screen /dev/ttyUSB0 115200
    ```

4.  On the Nexys Video board, press the red button labeled CPU_RESET.
5.  Observe the terminal output, it should show a ROM boot message like this:

    ```
    Commit ID:  1d0d927693c2ef60d7880ab306beb25115a53dcb
    Build Date: 2019-11-01, 15:57:43
    Jump!
    ```
    (To exit `screen` press <kbd>CTRL</kbd>+<kbd>A</kbd> keys together, then press <kbd>K</kbd>, and then confirm exit by pressing <kbd>y</kbd>.)
6. Connect a micro USB cable from your machine to the PROG connector (J12) on the Nexsys Video board (noting you need to also have a connection to the UART connector to see serial output).
7. Use the `spiflash` tool to write the hello_world binary:
    ```console
    $ cd $OT_TOP
    $ ./sw/host/spiflash/spiflash --input=sw/device/fpga/examples/hello_world/sw.bin
    ```
    You should see output from the `spiflash` tool showing the progress:
    ```console
    Running SPI flash update.
    Image divided into 6 frames.
    frame: 0x00000000 to offset: 0x00000000
    frame: 0x00000001 to offset: 0x000003d8
    frame: 0x00000002 to offset: 0x000007b0
    frame: 0x00000003 to offset: 0x00000b88
    frame: 0x00000004 to offset: 0x00000f60
    frame: 0x80000005 to offset: 0x00001338
    ```

    and matching output from the serial console from the boot rom loading the program:
    ```console
    Processing frame no: 00000000 exp no: 00000000
    Processing frame no: 00000001 exp no: 00000001
    Processing frame no: 00000002 exp no: 00000002
    Processing frame no: 00000003 exp no: 00000003
    Processing frame no: 00000004 exp no: 00000004
    Processing frame no: 80000005 exp no: 00000005
    bootstrap: DONE!
    Jump!
    ```
8. The hello_world binary will output the following:
    ```console
    Hello World! Oct 31 2019 16:28:03
    Watch the LEDs!
    Try out the switches on the board
    or type anything into the console window.
    The LEDs show the ASCII code of the last character.
    FTDI control changed. Enable JTAG
    ```

    Press some keys in the serial console and you should see the ASCII values of the characters sent shown in binary on the LEDs of the Nexsys Video FPGA board.

To build the software yourself follow the instructions in [Testing the demo design]({{< relref "getting_started_fpga.md#testing-the-demo-design" >}}) (note the software tools must be installed and a clone of the OpenTitan repository made, this is explained in the [Install Instructions]({{< relref "install_instructions" >}})).
See the [Getting Started on FPGAs Guide]({{< relref "getting_started_fpga.md" >}}) for full instructions how to build your own bitstream.
