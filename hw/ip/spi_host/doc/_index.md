---
title: "SPI_HOST HWIP Technical Specification"
---

# Overview

This document specifies SPI_HOST hardware IP (HWIP) functionality.
This module conforms to the [Comportable guideline for peripheral functionality.]({{< relref "doc/rm/comportability_specification/index.md" >}})
See that document for integration overview within the broader top-level system.

## Features

- Hardware control for remote devices using the Serial Peripheral Interface (SPI)
- Primarily designed for serial NOR flash devices such as the [Winbond W25Q01JV](https://www.winbond.com/resource-files/W25Q01JV%20SPI%20RevB%2011132019.pdf)
- Number of chip select lines controlled by `MaxCS` parameter
- Support for Standard SPI, Dual SPI or Quad SPI commands
  - Pins `sd[0]` through `sd[3]` are intended to connect to lines IO<sub>0</sub> through IO<sub>3</sub> respectively, on the target device.
  - Pin `sd[0]` may also be identified as "MOSI" by other SPI Hosts, while `sd[1]` is commonly referred to as "MISO"
- RX and TX data held in separate FIFOs
   - 288 bytes for TX data, 256 bytes for RX data
   - FIFOs loaded/unloaded via 32-bit TL-UL registers
   - Support for arbitrary byte-count in each transaction
   - Parametrizable support for Big- or Little-Endian systems in ordering I/O bytes within 32-bit words.
- SPI clock rate controlled by separate input clock to core
   - SPI `sck` line typically toggles at 1/2 the core clock frequency
   - An additional clock rate divider exists to reduce the frequency if needed
- Support for all SPI polarity and phases (CPOL, CPHA)
   - Additional support for "Full-cycle" SPI transactions, wherein data can be read a full SPI Clock cycle after the active edge (as opposed to one half cycle as is typical for SPI interfaces)
- Single Transfer Rate (STR) only (i.e. data received on multiple lines, but only on one clock edge)
   - *No support* for Dual Transfer Rate (DTR)
- Pass-through mode for coordination with [SPI_DEVICE IP]({{< relref "hw/ip/spi_device/doc/_index.md" >}})
- Automatic or manual control of chip select lines
- Condensed interrupt footprint: Two lines for two distinct interrupt classes: "error" and "spi_event"
   - Fine-grain interrupt masking supplied by secondary enable registers

## Description

The Serial Peripheral Interface (SPI) is a synchronous serial interface quite commonly used for NOR flash devices as well as a number of other off-chip peripherals such as ADC's, DAC's, or temperature sensors.
The interface is a *de facto* standard (not a formal one), and so there is no definitive reference describing the interface, or establishing compliance criteria.

It is therefore important to consult the data sheets for the desired peripheral devices in order to ensure compatibility.
For instance, this OpenTitan SPI Host IP is primarily designed for controlling Quad SPI NOR flash devices, such as the [W25Q01JV Serial NOR flash from Winbond](https://www.winbond.com/resource-files/W25Q01JV%20SPI%20RevB%2011132019.pdf) or this [1 Gb M25QL NOR flash from Micron](https://media-www.micron.com/-/media/client/global/documents/products/data-sheet/nor-flash/serial-nor/mt25q/die-rev-b/mt25q_qlkt_l_01g_bbb_0.pdf?rev=43d124f03bbf4ef0962435e9ec63a185).
Though this IP implementation aims to be general enough to support a variety of devices, the Winbond serial flash device is used as the primary reference for understanding our host requirements.

There are also a number of good references describing legacy host implementations for this protocol, which are useful for understanding some of the general needs for a wider range of target devices.
For instance, the legacy [SPI Block Guide](https://web.archive.org/web/20150413003534/http://www.ee.nmt.edu/~teare/ee308l/datasheets/S12SPIV3.pdf) from Motorola contains a definitive overview of some of the the general requirements for a standard SPI host, notably the definitions of SPI clock phase and polarity (CPOL and CPHA).
In order to potentially support a broad range of devices, this SPI Host IP also supports all four of the standard SPI clock phases.

### SPI Protocol Basics

Broadly speaking, the SPI host accepts commands from the TL-UL interface and, based on these commands, serially transmits and receives data on the external SPI interface pins.
The timing and data-line formatting of the command sequence depend on the external peripheral device and the nature of the specific command issued.

In each standard SPI command a number of instruction-, address- or data-bytes are transmitted on `sd[0]`, and response bytes are received on `sd[1]`.
So in standard-mode commands, `sd[0]` is always configured as an output, and `sd[1]` is always an input.
In standard SPI commands the `sd[0]` and `sd[1]` lines can be used as a full-duplex communication channel.
Not all devices exploit this capability, opting instead to have clear input and output phases for each command.
This half-duplex signaling behavior is especially common in devices with also support Dual- and Quad-mode commands, which are always half-duplex.
The SPI_HOST IP optionally supports both full-duplex and half-duplex commands in standard mode.

Along with the data lines, the SPI protocol also includes a chip select line, commonly called CS\#, or in this IP we refer to it as `cs_n`.
The SPI bus can be connected to many target peripherals, but each device on the bus gets its own chip select line, and so this active-low signal designates a particular device for each command.

The chip-select line also marks the beginning and end of each command.
No device will accept any command input until `cs_n` has been asserted for that device, and most devices (if not all) do not accept a second command unless `cs_n` has been deasserted to mark the end of the previous command.
Some simple devices, particularly those that support SPI daisy-chaining, do not process command input at all until *after* the `cs_n` line has been deasserted.
In the case of NOR flash devices, read and write commands are indeterminate in length, and the data transfer ends only when the `cs_n` line is deasserted.
So, though the exact details of operation may vary from device to device, the edges of the `cs_n` signal serve as an important markers for delineating the boundaries of each transaction.

The `sd` and `cs_n` lines are accompanied by a serial clock, `sck`.
The host is responsible for generating the serial clock, and typically each side asserts outgoing data on one edge of the clock (e.g. on the rising edge) and samples data in the next edge (e.g. on the falling edge).
When it comes to devices there is no universal convention on clock polarity (CPOL) or clock phase (CPHA).
Some devices expect the clock line to be low when the host is idle, thus the clock should come as a sequence of positive pulses (CPOL = 0).
On the other hand, other devices expect CPOL = 1, meaning that the clock line is inverted: *high* when idle with sequences of *negative* pulses.

Devices also differ in their expectations of clock *phase* (CPHA) relative to the data.
Devices with CPHA = 0, expect that both the host and device will be sampling data on the *leading* edge, and asserting data on the *trailing* edge.
(Because of the option for either polarity, the terms "leading" and "trailing" are preferred to "rising" or "falling").
When CPHA = 0, the first output bit is asserted with the falling edge of `cs_n`.
Meanwhile if CPHA = 1, data is always is asserted on the leading edge of `sck`, and data is always sampled on the trailing edge of sck.

When operating at the fastest-rated clock speeds, some flash devices (i.e. both the Winbond and Micron devices noted above), require setup times which exceed half a clock-cycle.
In order to support these fastest data rates, the SPI_HOST IP offers a modified "Full-cycle" (FULLCYC = 1) timing mode where data can be sampled a *full* cycle after the target device asserts data on the `sd` bus.
This full cycle mode has no effect on any of the signals transmitted, only on the timing of the sampling of the incoming signals.

{{< wavejson >}}
{signal: [
  {name: "clk_core_i", wave: "p.................."},
  {name: "sck (CPOL=0)", wave: "0.1010101010101010."},
  {name: "sck (CPOL=1)", wave: "1.0101010101010101."},
  {name: "cs_n", wave: "10................1"},
  ["CPHA = 0",
    {name: "sd[0] (output)", wave: "22.2.2.2.2.2.2.2...", data: ["","out7", "out6", "out5", "out4", "out3", "out2", "out1", "out0" ]},
    {name: "sd[1] (input)", wave: "22.2.2.2.2.2.2.2.2.", data: ["","in7", "in6", "in5", "in4", "in3", "in2", "in1", "in0",""]},
    {name: "Sampling Event (FULLCYC=0)", wave: "1.H.H.H.H.H.H.H.H.."},
    {name: "Sampling Event (FULLCYC=1)", wave: "1..H.H.H.H.H.H.H.H."},
  ],
  ["CPHA = 1",
    {name: "sd[0] (output)", wave: "2.2.2.2.2.2.2.2.2..", data: ["","out7", "out6", "out5", "out4", "out3", "out2", "out1", "out0" ]},
    {name: "sd[1] (input)", wave: "2.2.2.2.2.2.2.2.2.2", data: ["","in7", "in6", "in5", "in4", "in3", "in2", "in1", "in0",""]},
    {name: "Sampling Event (FULLCYC=0)", wave: "1..H.H.H.H.H.H.H.H."},
    {name: "Sampling Event (FULLCYC=1)", wave: "1...H.H.H.H.H.H.H.H"},
  ],
],
  head: {
    text: "Standard SPI transaction (1 byte) illustrating of the impact of the CPOL, CPHA, and FULLCYC settings"
  },
  foot: {
  }
}
{{< /wavejson >}}

As mentioned earlier, the `sd[0]` and `sd[1]` lines are unidirectional in Standard SPI mode.
On the other hand in the faster Dual- or Quad-modes, all data lines are bidirectional, and in Quad mode the number of data lines increases to four.
For the purposes of this IP, Dual or Quad-mode commands can be thought of as consisting of up to four command phases in which the host:
1. Transmits instructions or data at single-line rate,
2. Transmits instructions address or data on 2 or 4 data lines,
3. Holds the bus in a high-impedance state for some number of "dummy" clock cycles (neither side transmits), or
4. Receives information from the target device.

This four phase command scheme is also applied to half-duplex interactions when in standard mode.

{{< wavejson >}}
{signal: [
  {name: "clk_core_i", wave: "p.............................."},
  {name: "sck (CPOL=0)", wave: "0.1010101010101010101010101010."},
  {name: "cs_n", wave: "10............................1"},
  {name: "sd[0]", wave: "22.2.2.2.2.2.2.2.2.2.z...2.2.x.", data: ["","cmd7", "cmd6", "cmd5", "cmd4", "cmd3", "cmd2", "cmd1", "cmd0",
                                                             "out4", "out0", "in4", "in0" ]},
  {name: "sd[1]", wave: "z................2.2.z...2.2.x.", data: ["out5", "out1", "in5", "in1"]},
  {name: "sd[2]", wave: "z................2.2.z...2.2.x.", data: ["out6", "out2", "in6", "in2"]},
  {name: "sd[3]", wave: "z................2.2.z...2.2.x.", data: ["out7", "out3", "in7", "in3"]},
  {name: "Transaction phase:", wave: "x2...............3...4...5...x.", data: ['TX1', 'TXn', 'Dummy','RX'] },
  {name: "Sampling Event (FULLCYC=0)", wave: "1.........................H.H.."},
  {name: "Sampling Event (FULLCYC=1)", wave: "1..........................H.H."},
],
  head: {
  text: "Example Quad SPI transaction: 1 byte TX (Single), 1 byte (Quad), 2 dummy cycles and 1 RX byte with CPHA=0"
  },
}
{{< /wavejson >}}

For even faster transfer rates, some flash chips support double transfer rate (DTR) variations to the SPI protocol wherein the device receives and transmits fresh data on *both* the leading and trailing edge.
This IP only supports single transfer rate (STR), *not* DTR.
A preliminary investigation of DTR transfer mode suggests that proper support for setup and hold times in this mode may require a level of sub-cycle timing control which is not currently planned for this IP.

# Theory of Operations

**TODO**: Review text for accuracy after review updates.

## SPI_HOST IP Command Interface

Issuing a command generally consists of the following steps:
1. Configure the IP to be compatible with the target peripheral.
The {{< regref "CONFIGOPTS_0" >}} multi-register has one set of configuration settings for each `cs_n` line.
2. Load the instructions and data to be transmitted into the TXFIFO via the {{< regref "TXDATA" >}} register,
3. Issue a 32-bit command to the appropriate Command multi-register (e.g. for controlling the device on `cs_n[0]` use {{< regref "COMMAND_0" >}}).
Each command register has the following information,
    - The speed to use, {{< regref "COMMAND_0.SPEED_0" >}}, for this particular command (Standard, Dual, or Quad)
    - The number of bytes to transmit at *reduced* data rate, {{<regref "COMMAND_0.TX1_CNT_0" >}}, using `sd[0]` only
        - This field is specifically intended for Dual or Quad commands where the first instruction must be sent serially on `sd[0]`
    - The number of bytes to transmit at full data rate, {{< regref "COMMAND_0.TXN_CNT_0" >}}
    - The number of dummy `sck` cycles to wait before reading data, {{< regref "COMMAND_0.DUMMY_CYCLES_0" >}}
    - The number of bytes to receive at the full Dual or Quad rate, {{< regref "COMMAND_0.RX_CNT_0" >}}
4. Read the peripheral response from the {{< regref "RXDATA" >}} register.

### Configuration options

The {{< regref "CONFIGOPTS_0" >}} multi-register has one entry per `cs_n` line and holds clock configuration and timing settings which are specific to each peripheral.
Once the {{< regref "CONFIGOPTS_0" >}} multi-register has been programed for each SPI peripheral device, the values can be left unchanged.

The following sections give details on how the SPI_HOST can be used to control a specific peripheral.
For simplicity, this section decribes how to interact one device, attached to `cs_n[0]`, and as such references are made to the multi-registers {{< regref "CONFIGOPTS_0" >}} and {{< regref "COMMAND_0" >}}.
To configure timing and send commands to devices on other `cs_n` lines, instead use the `COMMAND` and `CONFIGOPTS` multi-registers corresponding to desired `cs_n` line.

The most common differences between target devices are the requirements for a specific SPI clock phase or polarity, CPOL and CPHA, which were described in the previous section [SPI Protocol Basics](#spi-protocol-basics).
These clock parameters can be set via the {{< regref "CONFIGOPTS_0.CPOL_0">}} or {{< regref "CONFIGOPTS_0.CPHA_0" >}} register fields.
Likewise, as also described in the previous section, if device setup times require a full clock cycle before sampling the output, Full-Cycle Mode can be enabled by asserting the {{< regref "CONFIGOPTS_0.FULLCYC_0" >}} bit.

#### Clock rate selection

The SPI clock rate for each peripheral is set by two factors:
- The SPI_HOST core clock (which may be generated independently from the TL-UL interface clock)
- An additional 16-bit clock divider

The SPI protocol usually requires activity (either sampling or asserting data) on either edge of the `sck` clock.
For this reason the maximum `sck` frequency is at most one half the SPI_HOST core frequency.
In order to support a broader range of SPI clock frequencies, the SPI_HOST core operates on a separate clock domain, which may be independent from the TL-UL bus clock.
This arrangement allows gives more flexibility in setting the serial clock frequency by means of an external PLL, and in principle the sck frequency could even be configured to *exceed* the bus clock.
For example, if the TL-UL bus is operating at 100MHz, a 200MHz SPI core clock can be fed to the SPI_HOST IP, in order to acheive data rates of 100 MTransfers/s (near the maximum clock rate of the Winbond flash device).

Since some peripheral devices attached to the same SPI_HOST may require different clock frequencies, there is also the option to divide the core clock by an additional factor when dealing with slower peripherals.

$$T_\textrm{sck,0}=\frac{1}{2}\frac{T_\textrm{core}}{\textrm{CONFIGOPTS_0.CLKDIV}+1}$$

Alternatively, this clock-divide feature can also be used to entirely bypass the need for an independent core clock.
Instead the core can be driven by the TL-UL bus clock, and the `sck` period can be adjusted using the {{< regref CONFIGOPTS_0.CLKDIV_0 >}} setting.

#### Chip-select timing control

Typically the `cs_n` line is automatically deasserted after the last edge of `sck`.
However,  by asserting {{< regref "CONFIGOPTS_0.CSAAT_0" >}} before issuing a particular command, one can instruct the core to hold `cs_n` low indefinitely after the last clock edge.
This is useful for merging two adjacent commands together, to create very long commands such as continuous read operations.
The `cs_n` line can then be deasserted by either issuing another command after clearing the {{< regref "CONFIGOPTS_0.CSAAT_0" >}} field, issuing a command to a different device (using a different `COMMAND` register), or simply resetting the core FSM via the {{< regref "CONTROL.RST_FSM">}} register.

Most devices require at least one-half `sck` clock-cycle between either edge of `cs_n` and the nearest `sck` edge.
However, some devices may require more timing margin and so the SPI_HOST core offers some configuration registers for controlling the timing of the `cs_n` edges when operating under automatic control.
The relevant parameters are as follows:
- T<sub>IDLE</sub>: The minimum time between each rising edge of `cs_n` and the following falling edge.
This time delay is a half `sck` cycle by default but can be extended to as long as eight `sck` cycles by setting the {{< regref "CONFIGOPTS_0.CSNIDLE_0">}} register.
- T<sub>LEAD</sub>: The minimum time between each falling edge of `cs_n` and the first leading edge of `sck`.
This time delay is a half `sck` cycle by default but can be extended to as long as eight `sck` cycles by setting the {{< regref "CONFIGOPTS_0.CSNLEAD_0">}} register.
- T<sub>TRAIL</sub>: The minimum time between the last trailing edge of `sck` and the following rising edge of `cs_n`.
This time delay is a half `sck` cycle by default but can be extended to as long as eight `sck` cycles by setting the {{< regref "CONFIGOPTS_0.CSNTRAIL_0">}} register.

{{< wavejson >}}
{signal: [
  {name: "sck",  wave: "l....1010|10........"},
  {name: "cs_n", wave: "10.......|.....1...0", node: ".A...B.....C...D...E"}
],
 edge: ["A<->B minimum (CSNLEAD+1)", "C<->D minimum (CSNTRAIL+1)", "D<->E minimum (CSNIDLE+1)"],
  head: {
    text: "Impact of CSNLEAD, CSNTRAIL and CSNIDLE CONFIGOPTS register settings",
    tick: 1
  },
  foot: {
    text: ["tspan", "All ticks are in units of &#xbd;T",
           ["tspan", {'baseline-shift':'sub'}, "sck"],
          "=&#xbd;T",
           ["tspan", {'baseline-shift':'sub'}, "core"],
          "&#xd7;(CLKDIV+1)"]
  }
}
{{< /wavejson >}}

These settings are all minimum bounds, and delays in the FSM implementation may create more margin in each of these timing constraints.

### Special Command Fields

The {{< regref "COMMAND_0" >}} register must be written every time a command is issued.
Whenever a `1` is written to {{< regref "COMMAND_0.GO_0" >}}, the contents of the {{< regref "CONFIGOPTS_0" >}} and {{< regref "COMMAND_0" >}} registers are passed through the Config/Command CDC to the SPI_HOST core FSM, along with a Chip Select mask signal, indicating which device should receive the command (for example `cs_n[0]`)
Once the command is issued, the core will immediately deassert {{< regref "STATUS.READY" >}}, and once the command has started {{< regref "STATUS.ACTIVE" >}} will go high.
The {{< regref "STATUS.ACTIVE" >}} line takes a few cycles to assert, due to CDC delays.
The command is complete when {{< regref "STATUS.ACTIVE" >}} goes low.
A `spi_event` interrupt can also be triggered to go off on completion by setting {{< regref "EVENT_ENABLE.IDLE" >}}.

### Chip Select Masks

Each instance of the SPI_HOST IP supports a parametrizable number of chip select lines (`cs_n[MaxCS-1:0]`).
Each `cs_n` line can be routed either to a single peripheral or to a daisy-chain of peripherals.
Whenever a 1 is written to one of the the `GO` bits in the `COMMAND` multiregister, a `cs_n` mask is sent (along with the `COMMAND` and `CONFIGOPTS` multi-register data for that line) to indicate which device is meant to receive the command.
The SPI_HOST core typically then manages the details of asserting and deasserting the proper `cs_n` line, subject to the timing parameters expressed in {{< regref "CONFIGOPTS_0.CSAAT_0" >}}, {{< regref "CONFIGOPTS_0.CSNLEAD_0" >}}, {{< regref "CONFIGOPTS_0.CSNTRAIL_0" >}}, and {{< regref "CONFIGOPTS_0.CSNIDLE_0" >}}.

Alternatively the `cs_n` lines can be controlled entirely by firmware.
If the register {{< regref "CONTROL.MANCS_EN" >}} is set high then the `cs_n` lines are directly controlled by the {{< regref "CONTROL.MANUAL_CS" >}} register.

If [Pass-through mode](#pass-through-mode) is enabled then the `cs_n` lines are controlled by *neither* the SPI_HOST hardware nor the firmware register.
In Pass-though mode, control of the `cs_n` lines passes directly to the inter-module port, `pt_cs_ni`.

### Arbitrary Length Commands

Typically the length of each command is limited by the maximum number of bits in the {{< regref "COMMAND_0.TXN_CNT_0" >}}, {{< regref "COMMAND_0.RX_CNT_0" >}}, and {{< regref "COMMAND_0.TX1_CNT_0" >}} fields.
However, a series  of SPI_HOST IP commands can be merged into one long command sequence using the {{< regref "CONFIGOPTS_0.CSAAT_0" >}} field, which leaves the `cs_n` line low after the first SPI_HOST command.
By raising the `cs_n` line only after the last command has completed, the peripheral will interpret the resulting transmit/receive sequences as one long command.

### Back-to-back Commands

There is no command queue in the SPI_HOST IP.
However a second command can be placed into the Config/Command CDC whenever {{< regref "STATUS.READY" >}} is high, even if the previous command is still running.
The internal state within the Config/Command CDC provides the option of scheduling a second command to execute immediately after completion of the current command.

On the other hand, writing a one to {{< regref "COMMAND_0.GO_0" >}} (or any `GO` bit in this multi-register) when {{< regref "STATUS.READY" >}} is low will trigger an error condition, which must be acknowledged by software.

## Data Formatting

### Input and Output Byte Ordering

The SPI transactions must be issued with correct bit ordering to properly communicate with a remote device.
Based on the requirements for our chosen flash devices, this IP follows these conventions:
- The relative significance of lines on the `sd` bus: `sd[0]` is always the most significant, followed by `sd[1]` though `sd[3]` with decreasing significance.
- The relative significance of a sequence of bits on the same `sd` bus: higher significance bits are always transmitted earlier than (or at the same time as) any lower significance bits.
    - For instance, when transferring a single byte in Quad mode, all four bits of the upper nibble (bits 7 through 3) are transferred in the first clock cycle and the entire lower nibble (bits 3 through 0) is transferred in the second cycle.

The programming model for the IP should meanwhile make it easy to quickly program the peripheral device, with a minimum amount of byte shuffling.
It should be intuitive to program the specific flash devices we are targeting, while following the conventions above:
- When reading the data in and out of the {{< regref "TXDATA" >}} and {{< regref "RXDATA" >}} registers, the IP should make the most of the TL-UL bus, using 32-bit I/O instructions.
- The SPI_HOST should make it easy to arrange transaction-data in processor memory, meaning that bytes should be sequentially transmitted in order of ascending memory address.
  - When using 32-bit I/O instructions, this requires some knowledge of the processor byte-order.

Based on these requirements, data placed in {{< regref "TXDATA" >}} or read from {{< regref "RXDATA" >}} is handled as follows:
- 32-bit words placed in the {{< regref "TXDATA" >}} register are transmitted in first-in-first-out order.
Likewise, words received from the SPI data lines are made available in the {{< regref "RXDATA" >}} register in first-in-first-out order.
- Within a 32-byte word, the `ByteOrder` parameter controls the order in which bytes are transmitted, and also the manner in which received bytes are eventually arranged in the 32-bit {{< regref "RXDATA" >}} register.
By default (`ByteOrder` = 0, for Big-Endian processors), the MSB of {{< regref "TXDATA" >}} (i.e bits 31 though 24) is transmitted first, and the other bytes follow in order of decreasing significance.
Similarly, by default, the first byte received is packed into the MSB of {{< regref "RXDATA" >}}, and the subsequent bytes of {{< regref "RXDATA" >}} are filled in order of decreasing significance.
On the other hand, if `ByteOrder` is set to 1 (for Little-Endian processors), the LSB is transmitted first from {{< regref "TXDATA" >}}, and received data is loaded first into the LSB of {{< regref "RXDATA" >}}.
   - The default choice of Big-Endian comes from the observation that our target flash peripherals expect to receive MSBs first for addresses and data.
- Finally within a given byte, the most significant bits are transmitted and received first.
For Dual and Quad transactions the *most* significant bit in any instantaneous pair or nibble is transmitted or received on `sd[0]`, and the remaining `sd` bits (1 though 3) are populated in order of *decreasing* significance.

The following figure shows how data appears on the serial data bus when it is written to {{< regref "TXDATA" >}}, or read from {{< regref "RXDATA" >}}.

{{< wavejson >}}
{signal: [
  ["ByteOrder=0",
  {name: "sd[0] (host output)", wave: "x22222222222|2222|222|22x", data: ["t[31]", "t[30]", "t[29]", "t[28]", "t[27]", "t[26]", "t[25]", "t[24]", "t[23]","t[22]",
                                                                          "t[21]","t[17]","t[16]","t[15]","t[14]","t[8]", "t[7]", "t[6]", "t[1]", "t[0]"]},
  {name: "sd[1] (host input)", wave: "x22222222222|2222|222|22x", data: ["r[31]", "r[30]", "r[29]", "r[28]", "r[27]", "r[26]", "r[25]", "r[24]", "r[23]","r[22]",
                                                                         "r[21]","r[17]","r[16]","r[15]","r[14]","r[8]", "r[7]", "r[6]", "r[1]", "r[0]"]},
  {name: "Which Byte?", wave: "x4.......4..|..4.|.4.|..x", data: ["MSB from TXDATA/RXDATA", "","", "          LSB"]}
],
  ["ByteOrder=1",
  {name: "sd[0] (host output)", wave: "x22222222222|2222|222|22x", data: ["t[7]", "t[6]", "t[5]", "t[4]", "t[3]", "t[2]", "t[1]", "t[0]", "t[15]","t[14]",
                                                                          "t[13]","t[9]","t[8]","t[23]","t[22]","t[16]", "t[31]", "t[30]", "t[25]", "t[24]"]},
  {name: "sd[1] (host input)", wave: "x22222222222|2222|222|22x", data: ["r[7]", "r[6]", "r[5]", "r[4]", "r[3]", "r[2]", "r[1]", "r[0]", "r[15]","r[14]",
                                                                         "r[13]","r[9]","r[8]","r[23]","r[22]","r[16]", "r[31]", "r[30]", "r[25]", "r[24]"]},
  {name: "Which Byte?", wave: "x5.......5..|..5.|.5.|..x", data: ["LSB from TXDATA/RXDATA", "","", "          MSB"]}
],
  ],
  head: {
    text: "Serial bit ordering for 32-bit TXDATA & RXDATA data words (t[31:0] and r[31:0]), Standard SPI as a Function of the Parameter 'ByteOrder'",
  },
  foot: {
  text: "(Bits are numbered as they appear when loaded into TXDATA or RXDATA registers.)"
  }
}
{{< /wavejson >}}


As shown in the following figure, a similar time-ordering scheme applies for Dual- and Quad-mode transfers.
However many bits of similar significance are packed into multiple parallel `sd` data lines, with the most significant going to `sd[0]`.

{{< wavejson >}}
{signal: [
  ["ByteOrder=0",
  {name: "sd[0]", wave: "x...22334455x...", data: ["d[31]", "d[27]", "d[23]", "d[19]", "d[15]", "d[11]", "d[7]", "d[3]"]},
  {name: "sd[1]", wave: "x...22334455x...", data: ["d[30]", "d[26]", "d[22]", "d[18]", "d[14]", "d[10]", "d[6]", "d[2]"]},
  {name: "sd[2]", wave: "x...22334455x...", data: ["d[29]", "d[25]", "d[21]", "d[17]", "d[13]", "d[9]", "d[5]", "d[1]"]},
  {name: "sd[3]", wave: "x...22334455x...", data: ["d[28]", "d[24]", "d[20]", "d[16]", "d[12]", "d[8]", "d[4]", "d[0]"]},
],
   ["ByteOrder=1",
  {name: "sd[0]", wave: "x...55443322x...", data: ["d[7]", "d[3]", "d[15]", "d[11]", "d[23]", "d[19]", "d[31]", "d[27]"]},
  {name: "sd[1]", wave: "x...55443322x...", data: ["d[6]", "d[2]", "d[14]", "d[10]", "d[22]", "d[18]", "d[30]", "d[26]"]},
  {name: "sd[2]", wave: "x...55443322x...", data: ["d[5]", "d[1]", "d[13]", "d[9]", "d[21]", "d[17]", "d[29]", "d[25]"]},
  {name: "sd[3]", wave: "x...55443322x...", data: ["d[4]", "d[0]", "d[12]", "d[8]", "d[20]", "d[16]", "d[28]", "d[24]"]},
  ],
  ],
  head: {
   text: "Serial bit ordering for 32-bit data word (d[31:0]), Quad SPI as a Function of the Parameter 'ByteOrder'",
  },
  foot: {
  text: "(Bits are numbered as they appear when loaded into TXDATA or RXDATA registers.)"
  }
}
{{< /wavejson >}}

### Command Length and Alignment in TXDATA,RXDATA

There is no restriction on the length of a command.
Even though the TXDATA and RXDATA registers require 4-byte accesses, any unused bytes in the TXDATA fifo (or unused slots in the RXDATA fifo), are simply ignored at the end of a command.
There is no need to explicitly pad commands to use up extra TXDATA bytes.
If the last few received bytes do not fill an entire RXDATA word, they will be posted to RXDATA at the end of the command and any unneeded bytes the end of the RXDATA word will be left as zeros.

The following waveform illustrates an example SPI transaction, where neither the data transmitted nor the data received fit into an even number of 32-bit words.
In this example, `A[31:0]` and `B[31:0]`, have been previously loaded into {{< regref "TXDATA" >}}, and afterwards one word, `X[31:0]`, is available in {{< regref "RXDATA" >}}.
All data in the waveform is transferred using 32-bit instructions.

{{< wavejson >}}
{signal: [
  ["ByteOrder=0",
  {name: "sd[0]", wave: "x222222223344552233z.22x", data: ["A[31]", "A[30]", "A[29]", "A[28]", "A[27]","A[26]", "A[25]", "A[24]", "A[23]", "A[19]", "A[15]", "A[11]",
                                                         "A[7]", "A[3]", "B[31]", "B[27]", "B[23]", "B[19]", "X[31]", "X[27]"]},
  {name: "sd[1]", wave: "xz.......3344552233z.22x", data: ["A[22]", "A[18]", "A[14]", "A[10]", "A[6]", "A[2]", "B[30]", "B[26]", "B[22]", "B[18]", "X[30]", "X[26]"]},
  {name: "sd[2]", wave: "xz.......3344552233z.22x", data: ["A[21]", "A[17]", "A[13]", "A[9]", "A[5]", "A[1]", "B[29]", "B[25]", "B[21]", "B[17]", "X[29]", "X[25]"]},
  {name: "sd[3]", wave: "xz.......3344552233z.22x", data: ["A[20]", "A[16]", "A[12]", "A[8]", "A[4]", "A[0]", "B[28]", "B[24]", "B[20]", "B[16]", "X[28]", "X[24]"]},
],
   {name:""},
   ["ByteOrder=1",
  {name: "sd[0]", wave: "x555555554433225544z.55x", data: ["A[7]", "A[6]", "A[5]", "A[4]", "A[3]", "A[2]", "A[1]", "A[0]",
                                                           "A[15]", "A[11]", "A[23]", "A[19]", "A[31]", "A[27]", "B[7]", "B[3]", "B[15]", "B[11]", "X[7]", "X[3]"]},
  {name: "sd[1]", wave: "xz.......4433225544z.55x", data: ["A[14]", "A[10]", "A[22]", "A[18]", "A[30]", "A[26]", "B[6]", "B[2]", "B[14]", "B[10]", "X[6]","X[2]"]},
  {name: "sd[2]", wave: "xz.......4433225544z.55x", data: ["A[13]", "A[9]", "A[21]", "A[17]", "A[29]", "A[25]", "B[5]", "B[1]", "B[13]", "B[9]", "X[5]", "X[1]"]},
  {name: "sd[3]", wave: "xz.......4433225544z.55x", data: ["A[12]", "A[8]", "A[20]", "A[16]", "A[28]", "A[24]", "B[4]", "B[0]", "B[12]", "B[8]", "X[4]", "X[0]"]},
  ],
  ],
  head: {
    text: "Serial bit ordering for 6 bytes transmitted from FIFO words 'A[31:0]' and 'B[31:0]', and 1 byte received into word 'X[31:0]'",
  },
  foot: {
    text: "Note: SPI_HOST command sent with COMMAND_0.TX1_CNT_0 = 1, .TXN_CNT_0 = 5, .DUMMY_CYCLES_0 = 2, and  .RX_CNT_0=1"
  }
}
{{< /wavejson >}}

There is also no restriction on the alignment of transmitted data. 
The {{< regref "TXDATA" >}} register is actually implemented as a memory window, so that it can support byte-enable signals.
This means that when copying bytes into {{< regref "TXDATA" >}} from unaligned firmware memory addresses, it is possible to use byte or half-word instructions.
Full-word instructions should however be used whenever possible, because each write consumes a full word of data in the TX FIFO regardless of the instruction size.
Smaller writes thus make inefficient use of the TX FIFO.

The RX FIFO has no special provisions for packing received data in any unaligned fashion.
Depending on the ByteOrder parameter, the first byte received is always packed into either the most- or least-significant byte of {{< regref "RXDATA" >}}.

## Pass-through Mode

The SPI_HOST also supports a special "Pass-through" mode, which allows for the direct control of the serial interface by another block (namely SPI_DEVICE).

To enable this mode, one sets {{< regref "CONTROL.PASSTHRU" >}} to one.

A multiplexor then configures the output signals `cio_sck_o` and `cio_cs_no` to directly match the inter-module signals `pt_sck_i` and `pt_cs_ni[MaxCS-1:0]`.
Likewise the bidirectional port-control `cio_sd_o[3:0]` and `cio_sdt_t[3:0]` are then respectively driven by inter-module signals `cio_sdo_i[3:0]` and `cio_sdi_o[3:0]`.
Meanwhile the peripheral data input signal `cio_sdo_o[3:0]` is always connected to the inter-module `pt_sdi_o[3:0]`.

## Interrupt aggregation

In order to reduce the total number of interrupts in the system, the SPI_HOST has only two interrupt lines: `error` and `spi_event`.
Within these two interrupt classes, there are a number of conditions which can trigger them.

Each interrupt class has a secondary status and mask register, to control which sub-classes of SPI events will cause an interrupt.

### SPI Events and Event Interrupts

The SPI_HOST supports interrupts for the following SPI events:

- `IDLE`: The SPI_HOST is idle.
- `READY`: The SPI_HOST is ready to accept a new command.
- `RXFULL`: The SPI_HOST has run out of room in the RXFIFO.
- `RXWM`: The number of 32-bit words in the RXFIFO currently exceeds the value set in {{< regref "CONTROL.RX_WATERMARK" >}}.
- `TXEMPTY`: The SPI_HOST has transmitted all the data in the TX FIFO.
- `TXWM`: The number of 32-bit words in the TX FIFO currently is currently less than the value set in {{< regref "CONTROL.TX_WATERMARK" >}}

Most SPI events signal a particular condition that persists until it is fixed, and these conditions can be detected by polling the corresponding field in the {{< regref "STATUS" >}} register.

In addition to these events, there are also two additional diagnostic fields in the {{< regref "STATUS" >}} register:  
- `RXSTALL`: The RXFIFO is full, and the SPI HOST is stalled and waiting for firmware to remove some data.
- `TXSTALL`: The TX FIFO is not only empty, but the SPI HOST is stalled and waiting for firmware to add more data.

These bits can provide diagnostic data for tuning the throughput of the device, but do not themselves generate event interrupts.

By default none of these SPI events trigger an interrupt.
They need to be enabled by writing to the corresponding field in {{< regref "EVENT_ENABLE" >}}.

The SPI event interrupt is signaled only when the IP enters the corresponding state.
For example if an interrupt is requested when the TX FIFO is empty, the IP will only generate one interrupt when the last data word is transmitted from the TX FIFO.
In this case, no new interrupts will be created until more data has been added to the FIFO, and all of it has been transmitted.

### Error Interrupt Conditions

An error interrupt is usually caused by a violation of the SPI_HOST programming model:
- If {{< regref "COMMAND_0.GO_0" >}} is asserted when {{< regref "STATUS.READY">}} is zero, the IP will assert {{< regref "ERROR_STATUS.CMDERR" >}}.
- The IP asserts {{< regref "ERROR_STATUS.OVERFLOW" >}} if it receives a write to {{< regref "TXDATA" >}} when the TX FIFO is full.
- Ihe IP asserts {{< regref "ERROR_STATUS.UNDERFLOW" >}} if it software attempts to read {{< regref "RXDATA" >}} when the RXFIFO is empty.

By default all of these programming violations will cause an `error` interrupt when they occur.
They will also halt the IP until the corresponding bit is cleared in the {{< regref "ERROR_STATUS" >}} register.


Each of these errors can be optionally ignored by clearing the corresponding bit in {{< regref "ERROR_ENABLE" >}}.
Clearing an error-enable bit will suppress interrupts for that class of violation and will allow the IP to proceed even if one of these errors has occurred.
The {{< regref "ERROR_STATUS" >}} register will continue to report all of these violations even if one of the corresponding bits in {{< regref "ERROR_ENABLE" >}} is zero.

The {{< regref "ERROR_STATUS" >}} bit should be cleared *before* clearing the error interrupt in the {{< regref "INTR_STATE" >}} register.
Failure do to so may result in a repeated interrupt.

## Status Indicators

*TODO:* TXDQ and RXDQ

## Other Registers

### SPI_HOST Enable

The SPI_HOST state machine is disabled on reset.
Before any commands are processed, the block must be enabled by writing one to the {{< regref "CONTROL.SPIEN" >}} register.
Writing a zero to this register temporarily suspends any previously submitted transactions.
If the block is re-enabled by writing a one to {{< regref "CONTROL.SPIEN" >}}, any previously executing commands will continue from wherever they left off.

An unacknowledged error interrupt will also suspend the core state machine.

### Component reset

In addition to the global hardware reset, there are three software reset options.
- The main control FSM can be held in reset by writing a one to {{< regref "CONTROL.RST_FSM" >}}.
This can be used to cancel a previous command.
- The TX FIFO can be cleared by writing a one to {{< regref "CONTROL.RST_TXFIFO">}}
- The RXFIFO can be cleared by writing a one to {{< regref "CONTROL.RST_RXFIFO">}}

## Block Diagram

![](spi_host_block_diagram.svg)

## Hardware Interfaces

{{< hwcfg "hw/ip/spi_host/data/spi_host.hjson" >}}

## Design Details

### Component Overview.

**TODO** High level introductory description of
- Control FSM
- SDQ Shift register
- Byte Select
- Byte Merge
- TX FIFO and RXFIFO interfaces

### Command and Config CDC


Highlights for this unit:
- New commands can always be written to {{< regref "COMMAND_0" >}} or {{< regref "CONFIGOPTS_0" >}}
- It is an error however to write a one to {{< regref "COMMAND_0.GO" >}} unless {{< regref "STATUS.READY" >}} is one.
- The {{< regref "COMMAND_0.GO" >}} bit triggers a four-phase synchronizer, which copies the relevant multi-registers and `cs_n` masks to `coreCmdConf`.
- {{<regref "STATUS.READY" >}} is low while this synchronizer is in operation
- The core FSM is responsible for issuing the `cc_ack` signal.
- `coreCmdCnf` is only updated and acknowledged (using `cc_ack`) when the FSM is not busy.

{{< wavejson >}}
{ signal: [
  {name: "clk", wave: "p..............................."},
  {name: "READY",         wave: "1.0..........1|.0..|...........1"},
  {name: "COMMAND, CONFIGOPTS", wave: "x3............|4...|............"},
  {name: "GO.q && GO.qe", wave: "010...........|10..|............"},
  {name: "cc_req",        wave: "01.....0......|1...|.....0......"},
  {name: "cc_req_syncd",  wave: "0..1.....0....|..1.|.......0...."},
  {name: "cc_ack",        wave: "0...1.....0...|....|..1.....0..."},
  {name: "cc_ack_ayncd",  wave: "0.....1.....0.|....|....1.....0."},
  {name: "core_cmd_cnf", wave: "x...3.........|....|..4........."},
  {name: "core_active",   wave: "0...1.........|....|.01........."},
],
  head: {text: 'Command and Config Synchronizer Operation'},
  foot: {text: "Synchronizer delay uncertainties are not illustrated."}
}
{{< /wavejson >}}

### Shift Register

{{< wavejson >}}
{signal: [
  {name: "clk_core_i", wave: "p.........................."},
  {name: "txfifo.out[31:0]", wave: "2..........................", data:"0x123456XX"},
  {name: "bytesel.out[7:0]", wave: "2..2...............2.......", data:["0x12", "0x34", "0x56"]},
  {name: "cio_sck_o",        wave: "0...1010101010101010101010."},
  {name: "cio_cs_no[0]",     wave: "1..0......................."},
  {name: "cio_sd_i[1]",      wave: "x..1.1.0.0.1.1.1.1.0.1.0.1."},
  {name: "sd_i_q[1]",        wave: "x...1.1.0.0.1.1.1.1.0.1.0.1"},
  {name: "shiftreg.sample",  wave: "0..101010101010101010101010"},
  {name: "shiftreg.shift",   wave: "0...10101010101010..1010101"},
  {name: "shiftreg.wr_en",   wave: "0.10..............10......."},
  {name: "shiftref.rd_en",   wave: "0.................10......."},
  {name: "shiftreg.mode",    wave: "2..........................", data: ["0"]},
  {name: "shiftreg.q[0]",    wave: "x..0.1.1.0.0.1.1.1.0.1.0.1."},
  {name: "shiftreg.q[1]",    wave: "x..1.0.1.1.0.0.1.1.0.0.1.0."},
  {name: "shiftreg.q[2]",    wave: "x..0.1.0.1.1.0.0.1.1.0.0.1."},
  {name: "shiftreg.q[3]",    wave: "x..0.0.1.0.1.1.0.0.0.1.0.0."},
  {name: "shiftreg.q[4]",    wave: "x..1.0.0.1.0.1.1.0.1.0.1.0."},
  {name: "shiftreg.q[5]",    wave: "x..0.1.0.0.1.0.1.1.1.1.0.1."},
  {name: "shiftreg.q[6]",    wave: "x..0.0.1.0.0.1.0.1.0.1.1.0."},
  {name: "shiftreg.q[7]",    wave: "x..0.0.0.1.0.0.1.0.0.0.1.1."},
  {name: "shiftreg.q (hex)", wave: "x..4.2.2.2.2.2.2.2.4.2.2.2.",
   data: ["0x12", "0x25", "0x4B", "0x96", "0x2c", "0x59", "0xB3", "0x67", "0x34", "0x69", "0xD2", "0xA5"]},
  {name: "bytemerge.in[7:0]", wave: "x..................2.......", data: ["0xcf"]},
  {name: "cio_sd_o[0] (shiftreg.q[7])",   wave: "x..0.0.0.1.0.0.1.0.0.0.1.1."},
],
edge: [],
  head: {
  text: "Standard SPI transaction, showing simultaneous receipt and transmission of data."
  },
   foot: {
   }
}
{{< /wavejson >}}

#### Standard mode

#### Dual mode

#### Quad mode

### Byte Select

The Byte Select, or `bytesel`, unit is responsible for unpacking data from the FIFO to it can be loaded into the shift register

**TODO:** For simplicity move `ByteOrder` control to be between TXFIFO/TXDATA and between RXFIFO/RXDATA.

{{< wavejson >}}
{signal: [
  {name: "clk_core_i", wave: "p......................"},
  {name: "txfifo.out[31:0]", wave: "x2.............x.......", data: ['0xDAD5F00D']},
  {name: "txfifo.empty", wave: "10.............1......."},
  {name: "txfifo.rd_en",wave: "0.............10......."},
  {name: "bytesel.q[31:0]", wave:"2..............2.......", data: ['0xBEADCAFE', '0xDAD5F00D']},
  {name: "bytesel.almost_empty", wave: "0..........1...0......."},
  {name: "bytesel.empty", wave: "0......................"},
  ['Big-Endian mode',
    {name: "bytesel.idx[1:0]", wave: "2..2...2...2...2...2...", data: [3, 2, 1, 0, 3, 2]},
  {name: "bytesel.out[7:0]", wave: "2..2...2...2...2...2...", data: ['0xBE', '0xAD', '0xCA', '0xFE', '0xDA', '0xD5']},
  {name: "shiftreg.wr_en", wave: "0.10..10..10..10..10..1"},
  {name: "shiftreg.shift", wave: "0...10..10..10..10..10."},
  {name: "shiftreg.q[7:0]", wave: "4..2.2.2.2.2.2.2.2.2.2.", data: ['','0xBE', '0xEX', '0xAD', '0xDX', '0xCA', '0xAX', '0xFE', '0xEX','0xDA', '0xAX']},
  {name: "sd[0:3] (*)", wave: "4..2.2.2.2.2.2.2.2.2.2.", data: ['','B','E','A','D','C','A','F','E', 'D','A']},

],
  ['Little-Endian mode',
    {name: "bytesel.idx[1:0]", wave: "2..2...2...2...2...2...", data: [0, 1, 2, 3, 0, 1]},
  {name: "bytesel.out[7:0]", wave: "2..2...2...2...2...2...", data: ['0xFE', '0xCA', '0xAD', '0xBE', '0x0D', '0xF0']},
     {name: "shiftreg.wr_en", wave: "0.10..10..10..10..10..1"},
  {name: "shiftreg.shift", wave: "0...10..10..10..10..10."},
  {name: "shiftreg.q[7:0]", wave: "4..2.2.2.2.2.2.2.2.2.2.", data: ['','0xFE', '0xEX', '0xCA', '0xAX', '0xAD', '0xDX', '0xBE', '0xEX','0x0D', '0xDX']},
  {name: "sd[0:3] (*)", wave: "4..2.2.2.2.2.2.2.2.2.2.", data: ['','F','E','C','A','A','D','B','E','0','D']},
],
],
  head: {
  text: "Processing of TX FIFO data as a function of the ByteOrder parameter (0: BE, 1: LE)"
  },
   foot: {
   text: "*Note bit-ordering for the sd bus. For Dual and Quad mode commands, sd[0] is always the MSB."
   }
}
{{< /wavejson >}}

### Byte Merge

{{< wavejson >}}
{signal: [
  {name: "clk_core_i", wave: "p......................"},

  {name: "sd[0:3] (*)", wave: "2.2.2.2.2.2.2.2.2.2.2.2", data: ['B','E','A','D','C','A','F','E','D','A', 'D', '5']},
  {name: "shiftreg.sample", wave: "10101010101010101010101"},
  {name: "shiftreg.q[7:0]", wave: "42.2.2.2.2.2.2.2.2.2.2.", data:["X","0xXB", "0xBE", "0xEA", "0xAD","0xDC","0xCA","0xAF","0xFE","0xED", "0xDA", "0xAD"]},
  {name: "bytemerge.rd_en", wave: "0..10..10..10..10..10.."},
  {name: "bytemerge.almost_full", wave: "0...........1...0......"},
  ['BE',
  {name: "bytemerge.idx", wave:"2...2...2...2...2...2..", data: [3,2,1,0, 3, 2]},
  {name: "rxfifo.data_in[31:0]", wave:"2...2...2...2...2...2..", data: ["0xXXXXXXXX","0xBEXXXXXX","0xBEADXXXX", "0xBEADCAXX", "0xBEADCAFE", "0xDAADCAFE"]},
  ],
  ['LE',
  {name: "bytemerge.idx", wave:"2...2...2...2...2...2..", data: [0,1,2,3,0,1]},
  {name: "rxfifo.data_in[31:0]", wave:"2...2...2...2...2...2..", data: ["0xXXXXXXXX","0xXXXXXXBE","0xXXXXADBE", "0xXXCAADBE", "0xFECAADBE", "0xFECAADAD"]},
  ],

  {name: "rxfifo.wr_en", wave: "0...............10....."},
  {name: "rxfifo.full", wave: "0......................"}
  ],
  head: {
  text: "Collection of RXFIFO data as a function of ByteOrder parameter"
  },
   foot: {
   text: "*Note bit-ordering for the sd bus. For Dual and Quad mode commands, sd[0] is always contains the MSB."
   }
}
{{< /wavejson >}}

#### End of Command

#### RXFIFO Full or TX FIFO Empty

### Config/Command CDC

### Passthrough Mode Multiplexors

# Programmer's Guide

**TODO**. (Outline Below)

## Basic Configuration

## Issuing a Standard SPI command

## Issuing a Dual or Quad SPI command

### Instruction code sent at Standard SPI bit width

### All Bytes Sent at Dual or Quad Rate

## Register Table

{{< registers "hw/ip/spi_host/data/spi_host.hjson" >}}