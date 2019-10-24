# FPGA Quick Start

Do you want to try out the design without installing EDA tools and waiting for a long build??
Then you have come to the right place!

In addition to actually building the [FPGA from scratch](getting_started_fpga.md), this flow also supports booting the FPGA directly from a storage device.

## Golden Bitfile Release

To support the quick start flow, the OpenTitan repository will release known good bitstreams.
The cadence of such releases will vary and largely depend on amount of change from the previous release.
To find a release, please navigate to the OpenTitan [github page `releases` tab](https://github.com/lowRISC/opentitan/releases).
The OpenTitan releases are tagged with the [CalVer convention](https://calver.org), similar to [lowRISC-toolchains](https://github.com/lowRISC/lowrisc-toolchains/releases).


## NexysVideo Quick Start

NexysVideo FPGA boards support the ability to program the FPGA from a USB pen drive or a microSD card (see section 2.3 of [NexysVideo reference manual](https://reference.digilentinc.com/_media/reference/programmable-logic/nexys-video/nexysvideo_rm.pdf).

To do so, please follow the steps below:
### Preparing the microSD

1.  Insert microSD Card to your machine.
1.  Run `fdisk -l` to find where the device was mapped (see an example mapping
    below, where the device was mapped as */dev/mmcblk0*):
    ```
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
1.  Make sure the device is formatted as FAT32. If not, format it to FAT32.
1.  Mount the device by running the following commands:
    ```bash
    mkdir -p /mnt/OT-SD  # Can be a different name
    mount -t vfat /dev/mmcblk0p1 /mnt/OT-SD  # Change according to mount/dev name
    ```
1.  Remove all files from the microSD. By the end of the process, it must contain a single bit file.
1.  Copy the required bit file to the micorSD.

### Loading FPGA Image From microSD

1.  On the NexysVideo board, mount the microSD (the microSD slot sits on the
    bottom of the board).
1.  Place JP4 on the pins marked USB/SD.
1.  Place JP2 on the pin marked SD.
1.  Push the PROG button and wait for the device to be flashed.
1.  Monitor Done LED (LD14) and wait for it to be turned off.
