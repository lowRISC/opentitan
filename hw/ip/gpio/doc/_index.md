---
title: "GPIO HWIP Technical Specification"
---

# Overview

This document specifies GPIO hardware IP functionality. This
module conforms to the [Comportable guideline for peripheral device
functionality]({{< relref "doc/rm/comportability_specification" >}})
See that document for integration overview within the broader top
level system.

## Features

- 32 GPIO ports
- Configurable interrupt per GPIO for detecting rising edge, falling edge,
  or active low/high input
- Two ways to update GPIO output: direct-write and masked (thread-safe) update

## Description

The GPIO block allows software to communicate through general purpose I/O
pins in a flexible manner. Each of 32 independent bits can be written
as peripheral outputs in two modes. Each of the 32 bits can be read
by software as peripheral inputs.  How these peripheral inputs and
outputs are connected to the chip IO is not within the scope of this
document. See the Comportability Specification for peripheral IO options
at the top chip level.

In the output direction, this module provides direct 32b access to each
GPIO value using direct write. This mode allows software to control all
GPIO bits simultaneously. Alternately, this module provides masked writes
to half of the bits at a time, allowing software to affect the output
value of a subset of the bits without requiring a read-modify-write.
In this mode the user provides a mask of which of the 16 bits are to be
modified, along with their new value. The details of this mode are given
in the [Programmers Guide](#programmers-guide) below.

In the input direction, software can read the contents of any of the GPIO
peripheral inputs.  In addition, software can request the detection of an
interrupt event for any of the 32 bits in a configurable manner.  The choices
are positive edge, negative edge or level detection events. A noise
filter is available through configuration for any of the 32 GPIO inputs.
This requires the input to be stable for 16 cycles of the
module clock before the input register reflects the change and interrupt
generation is evaluated. Note that if the filter is enabled and the pin
is set to output then there will be a corresponding delay in a change
in output value being reflected in the input register.

See the Design Details section for more details on output, input, and
interrupt control.

# Theory of Operations

## Block Diagram

![GPIO Block Diagram](gpio_blockdiagram.svg)

The block diagram above shows the `DATA_OUT` and `DATA_OE` registers
managed by hardware outside of the auto-generated register file.
For reference, it also shows the assumed connections to pads in
the top level netlist.

## Hardware Interfaces

{{< hwcfg "hw/ip/gpio/data/gpio.hjson" >}}

## Design Details

### GPIO Output logic

![GPIO Output Diagram](gpio_output.svg)

The GPIO module maintains one 32-bit output register `DATA_OUT` with two
ways to write to it. Direct write access uses {{< regref "DIRECT_OUT" >}}, and
masked access uses {{< regref "MASKED_OUT_UPPER" >}} and
{{< regref "MASKED_OUT_LOWER" >}}. Direct access provides full write and read
access for all 32 bits in one register.

For masked access the bits to modify are given as a mask in the upper
16 bits of the {{< regref "MASKED_OUT_UPPER" >}} and
{{< regref "MASKED_OUT_LOWER" >}} register write, while the data to write is
provided in the lower 16 bits of the register write.  The hardware updates
`DATA_OUT` with the mask so that the modification is done without software
requiring a Read-Modify-Write.

Reads of masked registers return the lower/upper 16 bits of the `DATA_OUT`
contents. Zeros are returned in the upper 16 bits (mask field). To read
what is on the pins, software should read the {{< regref "DATA_IN" >}} register.
(See [GPIO Input](#gpio-input) section below).

The same concept is duplicated for the output enable register `DATA_OE`.
Direct access uses {{< regref "DIRECT_OE" >}}, and masked access is available
using {{< regref "MASKED_OE_UPPER" >}} and {{< regref "MASKED_OE_LOWER" >}}.

The output enable is sent to the pad control block to determine if the
pad should drive the `DATA_OUT` value to the associated pin or not.

A typical use pattern is for initialization and suspend/resume code to
use the full access registers to set the output enables and current output
values, then switch to masked access for both `DATA_OUT` and `DATA_OE`.

For GPIO outputs that are not used (either not wired to a pin output or
not selected for pin multiplexing), the output values are disconnected
and have no effect on the GPIO input, regardless of output enable values.

### GPIO Input

The {{< regref "DATA_IN" >}} register returns the contents as seen on the
peripheral input, typically from the pads connected to those inputs.  In the
presence of a pin-multiplexing unit, GPIO peripheral inputs that are
not connected to a chip input will be tied to a constant zero input.

The GPIO module provides optional independent noise filter control for
each of the 32 input signals. Each input can be independently enabled with
the {{< regref "CTRL_EN_INPUT_FILTER" >}} (one bit per input).  This 16-cycle
filter is applied to both the {{< regref "DATA_IN" >}} register and
the interrupt detection logic. The timing for {{< regref "DATA_IN" >}} is still
not instantaneous if {{< regref "CTRL_EN_INPUT_FILTER" >}} is false as there is
top-level routing involved, but no flops are between the chip input and the
{{< regref "DATA_IN" >}} register.

The contents of {{< regref "DATA_IN" >}} are always readable and reflect the
value seen at the chip input pad regardless of the output enable setting from
DATA_OE. If the output enable is true (and the GPIO is connected to a
chip-level pad), the value read from {{< regref "DATA_IN" >}} includes the
effect of the peripheral's driven output (so will only differ from DATA_OUT if
the output driver is unable to switch the pin or during the delay imposed
if the noise filter is enabled).

### Interrupts

The GPIO module provides 32 interrupt signals to the main processor.
Each interrupt can be independently enabled, tested, and configured.
Following the standard interrupt guidelines in the [Comportability
Specification]({{< relref "doc/rm/comportability_specification" >}}),
the 32 bits of the {{< regref "INTR_ENABLE" >}} register determines whether the
associated inputs are configured to detect interrupt events. If enabled
via the various `INTR_CTRL_EN` registers, their current state can be
read in the {{< regref "INTR_STATE" >}} register. Clearing is done by writing a
`1` into the associated {{< regref "INTR_STATE" >}} bit field.

For configuration, there are 4 types of interrupts available per bit,
controlled with four control registers. {{< regref "INTR_CTRL_EN_RISING" >}}
configures the associated input for rising-edge detection.
Similarly, {{< regref "INTR_CTRL_EN_FALLING" >}} detects falling edge inputs.
{{< regref "INTR_CTRL_EN_LVLHIGH" >}} and {{< regref "INTR_CTRL_EN_LVLLOW" >}}
allow the input to be level sensitive interrupts. In theory an input can be
configured to detect both a rising and falling edge, but there is no hardware
assistance to indicate which edge caused the output interrupt.

**Note #1:** all inputs are sent through optional noise filtering before
being sent into interrupt detection. **Note #2:** all output interrupts to
the processor are level interrupts as per the Comportability Specification
guidelines. The GPIO module, if configured, converts an edge detection
into a level interrupt to the processor core.

# Programmers Guide

## Initialization

Initialization of the GPIO module includes the setting up of the interrupt
configuration for each GPIO input, as well as the configuration of
the required noise filtering. These do not provide masked access since
they are not expected to be done frequently.

```cpp
// enable inputs 0 and 1 for rising edge detection with filtering,
// inputs 2 and 3 for falling edge detection with filtering,
// input 4 for both rising edge detection (no filtering)
// and inputs 6 and 7 for active low interrupt detection
*GPIO_INTR_ENABLE =          0b11011111;
*GPIO_INTR_CTRL_EN_RISING =  0b00010011;
*GPIO_INTR_CTRL_EN_FALLING = 0b00011100;
*GPIO_INTR_CTRL_EN_LVLLOW  = 0b11000000;
*GPIO_INTR_CTRL_EN_LVLHIGH = 0b00000000;
*GPIO_CTRL_EN_INPUT_FILTER = 0b00001111;
```

## Common Examples

This section below shows the interaction between the direct access
and mask access for data output and data enable.

```cpp
// assume all GPIO are connected to chip pads.
// assume a weak pullup on all pads, returning 1 if undriven.
printf("0x%x", *GPIO_DATA_IN);          // 0xffffffff

*DIRECT_OUT = 0x11223344;
printf("0x%x", *GPIO_DIRECT_OUT);       // 0x11223344

*DIRECT_OE  = 0x00ff00ff;
printf("0x%x", *GPIO_DIRECT_OE);        // 0x00ff00ff

// weak pullup still applies to undriven signals
printf("0x%x", *GPIO_DATA_IN);          // 0xff22ff44

// read of direct_out still returns DATA_OUT contents
printf("0x%x", *GPIO_DIRECT_OUT);       // 0x11223344

// try masked accesses to DATA_OUT
*GPIO_MASKED_OUT_LOWER = 0x0f0f5566
printf("0x%x", *GPIO_MASKED_OUT_LOWER); // 0x00003546
printf("0x%x", *GPIO_DIRECT_OUT);       // 0x11223546

*GPIO_MASKED_OUT_UPPER = 0x0f0f7788
printf("0x%x", *GPIO_MASKED_OUT_UPPER); // 0x00001728
printf("0x%x", *GPIO_DIRECT_OUT);       // 0x17283546

// OE still applies
printf("0x%x", *GPIO_DATA_IN);          // 0xff28ff46

// manipulate OE
*GPIO_DIRECT_OE = 0xff00ff00;
printf("0x%x", *GPIO_DIRECT_OE);        // 0xff00ff00
printf("0x%x", *GPIO_DATA_IN);          // 0x17ff35ff

*GPIO_MASKED_OE_LOWER = 0x0f0f0f0f;
printf("0x%x", *GPIO_MASKED_OE_LOWER);  // 0x00000f0f
printf("0x%x", *GPIO_DIRECT_OE);        // 0xff000f0f
printf("0x%x", *GPIO_DATA_IN);          // 0x17fff5f6

*GPIO_MASKED_OE_UPPER = 0x0f0f0f0f;
printf("0x%x", *GPIO_MASKED_OE_UPPER);  // 0x00000f0f
printf("0x%x", *GPIO_DIRECT_OE);        // 0x0f0f0f0f
printf("0x%x", *GPIO_DATA_IN);          // 0xf7f8f5f6
```

## Interrupt Handling

This section below gives an example of how interrupt clearing works,
assuming some events have occurred as shown in comments.

```cpp
*INTR_ENABLE = 0x000000ff;              // interrupts enabled GPIO[7:0] inputs
printf("0b%x", *GPIO_DATA_IN);          // assume 0b00000000
printf("0b%x", *GPIO_INTR_STATE);       // 0b00000000

*INTR_CTRL_EN_RISING  = 0b00010001;     // rising detect on GPIO[0], GPIO[4]
*INTR_CTRL_EN_FALLING = 0b00010010;     // falling detect on GPIO[1], GPIO[4]
*INTR_CTRL_EN_LVLLOW  = 0b00001100;     // falling detect on GPIO[2], GPIO[3]
*INTR_CTRL_EN_LVLHIGH = 0b11000000;     // falling detect on GPIO[6], GPIO[7]

// already detected intr[3,2] (level low)
printf("0b%b", *GPIO_INTR_STATE);       // 0b00001100

// try and clear [3:2], fails since still active low
*GPIO_INTR_STATE = 0b00001100;
printf("0b%b", *GPIO_INTR_STATE);       // 0b00001100

// EVENT: all bits [7:0] rising, triggers [7,6,4,0], [3,2] still latched
printf("0b%b", *GPIO_DATA_IN);          // 0b11111111
printf("0b%b", *GPIO_INTR_STATE);       // 0b11011101

// try and clear all bits, [7,6] still detecting level high
*GPIO_INTR_STATE = 0b11111111;
printf("0b%b", *GPIO_INTR_STATE);       // 0b11000000

// EVENT: all bits [7:0] falling, triggers [4,3,2,1], [7,6] still latched
printf("0b%b", *GPIO_DATA_IN);          // 0b00000000
printf("0b%b", *GPIO_INTR_STATE);       // 0b11011110

// try and clear all bits, [3,2] still detecting level low
*GPIO_INTR_STATE = 0b11111111;
printf("0b%b", *GPIO_INTR_STATE);       // 0b00001100

// write test register for all 8 events, trigger regardless of external events
*GPIO_INTR_TEST = 0b11111111;
printf("0b%b", *GPIO_INTR_STATE);       // 0b11111111

// try and clear all bits, [3,2] still detecting level low
*GPIO_INTR_STATE = 0b11111111;
printf("0b%b", *GPIO_INTR_STATE);       // 0b00001100

```

## Device Interface Functions (DIFs)

{{< dif_listing "sw/device/lib/dif/dif_gpio.h" >}}

## Register Table

{{< registers "hw/ip/gpio/data/gpio.hjson" >}}
