# The TinyFPGA USB Bootloader
The TinyFPGA USB Bootloader is an open source IP for programming FPGAs without extra USB interface chips.  It implements a USB virtual serial port to SPI flash bridge on the FPGA fabric itself.  For FPGAs that support loading multiple configurations it is possible for the bootloader to be completely unloaded from the FPGA before the user configuration is loaded in.  

From the host computer's perspective, the bootloader looks like a serial port.  This method was chosen because programming with serial ports is generally easier to understand than other USB-specific protocols.  Commands to boot into the user configuration or access the SPI flash are all transfered over this interface.  Using this serial interface, a programmer application on the host computer can issue commands to the SPI flash directly through the bootloader.  All of the details about programming the SPI flash are handled by the programmer application.

## Hardware Requirements
In order to implement the TinyFPGA USB Bootloader, an FPGA system...
1. **MUST** have USB_P and USB_N lines with 3.3v signalling for the USB interface.
2. **MUST** have an oscillator and PLL capable of generating an accurate and stable 48MHz in the FPGA fabric.
3. **MUST** have FPGA configuration stored on external SPI flash, loaded by FPGA on boot.
4. **MUST** have a 1.5k pull-up resistor on the USB_P line and **SHOULD** connect the 1.5K pull-up resistor to the `usb_pu` signal from the bootloader.
5. **SHOULD** support booting from multiple images stored in SPI flash.  The bootloader in the primary image, and the user configuration in a secondary image.  
6. **SHOULD** use SPI flash that is large enough for a multi-boot image with at least two FPGA configurations as well as any user data that may be stored there.  Use the appropriate tools for your FPGA to determine the size of the mult-boot image before selecting the SPI flash size.
7. **SHOULD** use SPI flash that supports programmable security register pages accessed with opcodes 0x44, 0x42, 0x48.  These register places are a useful location to store metadata for the board that the programmer application needs to properly program user configurations and data.

## FPGA Board Metadata
Each FPGA board implementing the TinyFPGA USB Bootloader may have different locations for the bootloader image, user image, user data, and other information.  These differences are driven by the FPGA's multi-boot capabilities/requirements and the size of the FPGA configuration image.

In order for a common bootloader and programmer application to program user images and user data to the correct locations, the programmer must know where these locations are in the SPI flash.  It is also useful to identify the board with a name and unique serial number.  This information along with other required and optional metadata is stored in the non-volatile security register pages of the SPI flash and optionally in the main SPI flash memory.

The programmer application will search security register pages 0-3 for valid metadata.  The metadata is stored in JSON format.  JSON was choosen because it is compact enough, is well understood, and easier to read and understand than a binary format. 

Below is an example of how the metadata may be structured and formatted for the TinyFPGA BX board:

#### SPI Flash Security Register Page 1 (write-protected)
One of the SPI flash security register pages contains fixed data about the board that does not change.  This is the name of the board, the hardware revision of the board, and serial number unique to the board name.  This security register page should be write protected as it should never be changed.  If the rest of the SPI flash is erased, this minimal amount of information will help the user to find recovery instructions.

```javascript
{"boardmeta":{
  "name": "TinyFPGA BX",
  "fpga": "ice40lp8k-cm81",
  "hver": "1.0.0",
  "serial": 10034
}}
```

#### SPI Flash Security Register Page 2 (not write-protected)
A seperate SPI flash security register page should contain or point to information that can change.  This includes the bootloader version number, update URL for new bootloader releases for this board, and an address map for the SPI flash that describes where the bootloader, user image, and user data belong.  Using this information the programmer application is able to discover where to put new user images and data without any input from the user or built-in knowledge about the board.  It makes the board plug-and-play.

Optionally, an additional `desc.tgz` file may be included in the SPI flash itself, or on the update page.  This `desc.gz` file contains the information necessary to develop with the board.  At a minimum it describes the FPGA name, package, and a mapping from FPGA pins to board IOs and peripherals.

```javascript
{"bootmeta": "@0xFF000+445"}
```

#### SPI Flash Memory Address 0xFF000
```javascript
{
  "bootloader": "TinyFPGA USB Bootloader",
  "bver": "2.0.0",
  "update": "https://tinyfpga.com/update/tinyfpga-bx",
  "addrmap": {
    "bootloader": "0x00000+131542",
    "userimage":  "0x30000+131542",
    "userdata":   "0x50000+710000",
    "desc.tgz":   "0xFC000+16000"
  }
}
```

A detailed explanation of the metadata structure will be added here.

## Protocol
The protocol on top of the USB virtual serial port takes the form of requests and responses.  Only the host computer is able to initiate requests.  The bootloader on the FPGA can only respond to requests.

### Boot Command
```
Length: 1 byte

+=====================+
|    Request Data     |
+=====+========+======+
| Byte| Field  |Value |
+=====+========+======+
|  0  | Opcode | 0x00 |
+-----+--------+------+
```

The `Boot` command forces the TinyFPGA B-series board to exit the bootloader and configure the FPGA with the user design from SPI flash.  Once the user design is loaded onto the FPGA, the bootloader is no longer present and the user design has full control over the FPGA, including the USB interface.   

### Access SPI Command
```
Length: Variable

+================================+
|          Request Data          |
+=====+===================+======+
| Byte|       Field       | Value|
+=====+===================+======+
|  0  |       Opcode      | 0x01 |
+-----+-------------------+------+
|  1  |  Write Length Lo  | 0xWW |
+-----+-------------------+------+
|  2  |  Write Length Hi  | 0xWW |
+-----+-------------------+------+
|  3  |   Read Length Lo  | 0xRR |
+-----+-------------------+------+
|  4  |   Read Length Hi  | 0xRR |
+-----+-------------------+------+
|  5  | Write Data Byte 0 | 0xDD |
+-----+-------------------+------+
+-----+-------------------+------+
| n+5 | Write Data Byte n | 0xDD |
+-----+-------------------+------+

+================================+
|         Response Data          |
+=====+===================+======+
| Byte|       Field       | Value|
+=====+===================+======+
|  0  |  Read Data Byte 0 | 0xDD |
+-----+-------------------+------+
+-----+-------------------+------+
|  n  |  Read Data Byte n | 0xDD |
+-----+-------------------+------+
```

The `Access SPI` command executes a transfer with the SPI flash.  SPI flash commands can have two phases:
1. Write phase.  Command opcode, address, and potentially data are shifted out the SPI master to the SPI flash.
2. Read phase.  Data is shifted from the SPI flash to the SPI master.

The `Write Length` and `Read Length` in the `Access SPI` command refer to these two phases.  In order to fully understand how to interact with the SPI flash you need to read the [datasheet for the SPI flash chip](http://datasheet.octopart.com/AT25SF041-SSHD-B-Adesto-Technologies-datasheet-62342976.pdf).  The datasheet contains a table that lists the commands the SPI flash chip supports.  

Here's a summary of the commands used to properly erase, program, and verify bitstreams on the SPI flash:

| Command               | Opcode      | Address Bytes | Dummy Bytes | Data Bytes | Datasheet Section |
|-----------------------|:-----------:|:-------------:|:-----------:|:----------:|:-----------------:|
| Resume                |     0xAB    |       0       |      0      |      0     |        11.4       |
| Read Man. and Dev. ID |     0x9F    |       0       |      0      |      0     |        11.1       |
| Read Status Reg 1     |     0x05    |       0       |      0      |      1     |        10.1       |
| Block Erase 4 KBytes  |     0x20    |       3       |      0      |      0     |         7.2       |
| Block Erase 32 KBytes |     0x52    |       3       |      0      |      0     |         7.2       |
| Block Erase 64 KBytes |     0xD8    |       3       |      0      |      0     |         7.2       |
| Write Enable          |     0x06    |       0       |      0      |      0     |         8.1       |
| Byte/Page Program     |     0x02    |       3       |      0      |     1+     |         7.1       |
| Read Array            |     0x0B    |       3       |      1      |     1+     |         6.1       |     

## SPI Flash Programming Flow

The SPI flash needs to be accessed in a specific order to successfully program the bitstream.  The following pseudocode illustrates how the `tinyprog` programmer programs user FPGA bitstreams into the SPI flash:

```
// SPI flash will be in deep sleep, we need to wake it up
issue resume command     

// read FPGA board metadata
for each SPI flash security register page 0-3:
    read the security register page and metadata JSON
    recursively read any other locations in SPI flash referenced by the metadata
 
 userimage_addr = metadata["bootmeta"]["addrmap"]["userimage"]

// erase user flash area
for each 4k block from (userimage_addr) to (userimage_addr + length(bitstream)):
    issue write enable command
    issue block erase 4 KBytes at current block address
    poll status reg 1 until bit 0 is cleared

// program new user bitstream into user flash area
for each 256 bytes from (userimage_addr) to (userimage_addr + length(bitstream)):
    issue write enable command
    write 256 bytes of of the bitstream and increment write offset by 256 bytes
    poll status reg 1 until bit 0 is cleared
    
// verify bitstream data is correct
read length(bitstream) bytes of of the bitstream, compare to bitstream file

if verify is successful then issue boot command to the bootloader
```

For exact details, see the [`tinyprog/__init__.py`](https://github.com/tinyfpga/TinyFPGA-Bootloader/blob/master/programmer/tinyprog/__init__.py) Python module in this repo.

