# Programmer's Guide

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

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_gpio.h)
