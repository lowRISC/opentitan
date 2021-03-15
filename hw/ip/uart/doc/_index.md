---
title: "UART HWIP Technical Specification"
---

# Overview

This document specifies UART hardware IP functionality. This module
conforms to the
[Comportable guideline for peripheral functionality.](/doc/rm/comportability_specification)
See that document for integration overview within the broader
top level system.


## Features

- 2-pin full duplex external interface
- 8-bit data word, optional even or odd parity bit per byte
- 1 stop bit
- 32 x 8b RX buffer
- 32 x 8b TX buffer
- Programmable baud rate
- Interrupt for transmit empty, receive overflow, frame error, parity error, break error, receive
  timeout

## Description

The UART module is a serial-to-parallel receive (RX) and parallel-to-serial
(TX) full duplex design intended to communicate to an outside device, typically
for basic terminal-style communication. It is programmed to run at a particular
baud rate and contains only a transmit and receive signal to the outside world,
i.e. no synchronizing clock. The programmable baud rate guarantees to be met up
to 1Mbps.

## Compatibility

The OpenTitan UART is feature compatible to a specific implementation in [Chromium EC](https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/master/chip/g/uart.c).
Additional features such as parity have been added.

# Theory of Operations

## Block Diagram

![UART Block Diagram](block_diagram.svg)

## Hardware Interfaces

{{< incGenFromIpDesc "../data/uart.hjson" "hwcfg" >}}

## Design Details

### Serial interface (both directions)

The TX/RX serial lines are high when idle. Data starts with a START bit (high
idle state deasserts, **1**-->**0**) followed by 8 data bits. The least
significant bit is sent first. If the parity feature is turned on then an odd or
even parity bit follows after the data bits. Finally a STOP (**1**) bit
completes one byte of data transfer.

{{< wavejson >}}
{
  signal: [
    { name: 'Baud Clock',     wave: 'p............'                                                        },
    { name: 'tx',             wave: '10333333331..', data: [ "lsb", "", "", "", "", "", "", "msb" ]        },
    { name: 'Baud Clock',     wave: 'p............'                                                        },
    { name: 'tx (w/ parity)', wave: '103333333341.', data: [ "lsb", "", "", "", "", "", "", "msb", "par" ] },
  ],
  head: {
    text: 'Serial Transmission Frame',
  },
  foot: {
    text: 'start bit ("0") at cycle -1, stop bit ("1") at cycle 8, or after parity bit',
    tock: -2
  },
  foot: {
    text: [
      'tspan',
        ['tspan', 'start bit '],
        ['tspan', {class:'info h4'}, '0'],
        ['tspan', ' at cycle -1, stop bit '],
        ['tspan', {class:'info h4'}, '1'],
        ['tspan', ' at cycle 8, or at cycle 9 after parity bit'],
      ],
    tock: -2,
  }
}
{{< /wavejson >}}

### Transmission

A write to {{< regref "WDATA" >}} enqueues a data byte into the 32 byte deep write FIFO, which
triggers the transmit module to start UART TX serial data transfer. The TX
module dequeues the byte from the FIFO and shifts it bit by bit out to the UART
TX pin on positive edges of the baud clock.

If TX is not enabled, written DATA into FIFO will be stacked up and sent out
when TX is enabled.

When the FIFO becomes empty as part of transmittion, a TX FIFO empty interrupt will be raised.
This is separate from the TX FIFO water mark interrupt.


### Reception

The RX module oversamples the RX input pin at 16x the requested
baud clock. When the input is detected low the receiver will check
half a bit-time later (i.e. 8 cycles of the oversample clock) that the
line is still low before detecting the START bit. If the line has
returned high the glitch is ignored. After it detects the START bit,
the RX module samples at the center of each bit-time and gathers
incoming serial bits into a charcter buffer. If the STOP bit is
detected as high and the optional partity bit is correct the data byte
is pushed into a 32 byte deep RX FIFO. The data can be read out by
reading {{< regref "RDATA" >}} register.

This behaviour of the receiver can be used to compute the approximate
baud clock frequency error that can be tolerated between the
transmitter at the other end of the cable and the receiver. The
initial sample point is aligned with the center of the START bit. The
receiver will then sample every 16 cycles of the 16 x baud clock, the
diagram below shows the number of ticks after the centering that each
bit is captured. Because of the frequency difference between the
transmiter and receiver the actual sample point will drift compared to
the ideal center of the bit. In order to correctly receive the STOP
bit it must be sampled between the "early" and "late" points shown
on the diagram, which are half a bit-time or 8 ticks of the 16x baud
clock before or after the center. If the transmitter is considered
"ideal" then the local clock must thus differ by no more than plus or
minus 8 ticks in 144 or aproximately +/- 5.5%. If parity is enabled
the stop bit will be a bit time later, so this becomes 8/160 or about
+/- 5%.

{{< wavejson >}}
{
  signal: [
    { name: 'Sample', wave: '', node: '..P............', period: "2" },
    {},
    { name: 'rx',
      wave: '1.0.3.3.3.3.3.3.3.3.1.0.3',
      node: '...A................C.D..',
      cdata: [ "idle", "start", "+16", "+32", "+48", "+64", "+80",
                "+96", "+112", "+128", "+144", "next start" ] },
  ],
    "edge"   : ["P-|>A center", "P-|>C early", "P-|>D late"],
  head: {
    text: 'Receiver sampling window',
  },
}
{{< /wavejson >}}

In practice, the transmitter and receiver will both differ from the
ideal baud rate. Since the worst case difference for reception is 5%,
the uart can be expected to work if both sides are within +/- 2.5% of
the ideal baud rate.

### Setting the baud rate

The baud rate is set by writing to the {{< regref "CTRL.NCO" >}} register field. This should be
set using the equation below, where `f_pclk` is the system clock frequency
provided to the UART, and `f_baud` is the desired baud rate (in bits per second).

$$ NCO = 16 \times {{2^{$bits(NCO)} \times f\_{baud}} \over {f\_{pclk}}} $$

The formula above depends on the NCO CSR width.
The logic creates a x16 tick when the NCO counter overflows.
So, the computed baud rate from NCO value is below.

$$ f\_{baud} = {{1 \over 16} \times {NCO \over {2^{$bits(NCO)}}} \times {f\_{pclk}}} $$

Note that the NCO result from the above formula can be a fraction but
the NCO register only accepts an integer value. This will create an
error if the baud rate is not divisible by the fixed clock frequency. As
discussed in the previous section the error rate between the receiver
and remote transmitter should be lower than `8 / 144` to latch a
correct character value when parity is not used and lower than `8 /
160` when parity is used. In the expectation that the device the other
side of the line behaves similarly, this requires each side have a
baud rate that is matched to within +/- 2.5% of the ideal baud
rate. The contribution to this error if NCO is rounded down to an
integer (which will make the actual baud rate always lower or equal to
the requested rate) can be computed from:

$$ Error = {{(NCO - INT(NCO))} \over {NCO}} percent $$

In this case if the resulting value of NCO is greater than $$ {1 \over
0.025} = 40 $$ then this will always be less than the 2.5% error
target.

For NCO less than 40 the error in baud rate may or may not be
acceptable and should be carefully checked and rounding to the nearest
integer may achieve better results. If the computed value is close to
an integer so that the error in the target range then the baud rate
can be supported, however if it is too far off an integer then the
baud rate cannot be supported. This check is needed when

$$ {{baud} < {{40 * f\_{pclk}} \over {2^{$bits(NCO)+4}}}} \qquad OR \qquad
{{f\_{pclk}} > {{{2^{$bits(NCO)+4}} * {baud}} \over {40}}} $$

Using rounded frequencies and common baud rates, this implies that
care is needed for 9600 baud and below if the system clock is under
250MHz, with 4800 baud and below if the system clock is under 125MHz,
2400 baud and below if the system clock us under 63MHz, and 1200 baud
and below if the system clock is under 32MHz.


### Interrupts

UART module has a few interrupts including general data flow interrupts
and unexpected event interrupts.

#### tx_watermark / rx_watermark
If the TX FIFO level becomes smaller than the TX water mark level (configurable via {{< regref "FIFO_CTRL.RXILVL" >}} and {{< regref "FIFO_CTRL.TXILVL" >}}), the `tx_watermark` interrupt is raised to inform SW.
If the RX FIFO level becomes greater than or equal to RX water mark level (configurable via {{< regref "FIFO_CTRL.RXILVL" >}} and {{< regref "FIFO_CTRL.TXILVL" >}}), the `rx_watermark` interrupt is raised to inform SW.

Note that the watermark interrupts are edge triggered events.
This means the interrupt only triggers when the condition transitions from untrue->true.
This is especially important in the tx_watermark case.
When the TX FIFO is empty, it by default satisifies all the watermark conditions.
In order for the interrupt to trigger then, it is required that software initiates a write burst that is greater than the programmed watermark value.

For example, assume TX watermark is programmed to be less than 4 bytes, and software programs one byte at a time, waits for it to finish transmitting, before supplying the next byte.
Under these conditions, the TX watermark interrupt will never trigger because the size of the FIFO never exceeds the watermark level.


#### tx_empty
If TX FIFO becomes empty as part of transmit, the interrupt `tx_empty` is asserted.
The transmitted contents may be garbage at this point as old FIFO contents will likely be transmitted.

#### rx_overflow
If RX FIFO receives an additional write request when its FIFO is full,
the interrupt `rx_overflow` is asserted and the character is dropped.

#### rx_break_err
The `rx_break_err` interrupt is triggered if a break condition has
been detected. A break condition is defined as the RX pin being
continuously low for more than a programmable number of
character-times (via {{< regref "CTRL.RXBLVL" >}}, either 2, 4, 8, or 16). A
character time is 10 bit-times if parity is disabled (START + 8 data +
STOP) or 11 bit-times if parity is enabled (START + 8 data + parity +
STOP). If the UART is connected to an external connector this would
typically indicate the cable has been disconnected (or there is a
break in the wire). If the UART is connected to another part on the
same board it would typically indicate the other part has reset or
rebooted. (If the open connector or resetting peer part causes the RX
input to not be actively driven, then a pulldown resistor is needed to
ensure a break and a pullup resistor will ensure the line looks idle
and no break is generated.)  Note that only one interrupt is generated
per break -- the line must return high for at least half a bit-time
before an additional break interrupt is generated. The current break
status can be read from the {{< regref "STATUS.BREAK" >}} bit. If STATUS.BREAK is set
but {{< regref "INTR_STATE.BREAK" >}} is clear then the line break has already caused
an interrupt that has been cleared but the line break is still going
on. If {{< regref "STATUS.BREAK" >}} is clear but {{< regref "INTR_STATE.BREAK" >}} is set then
there has been a line break for which software has not cleared the
interrupt but the line is now back to normal.

#### rx_frame_err
The `rx_frame_err` interrupt is triggered if the RX module receives the `START`
bit (**0**) and a series of data bits but did not detect the `STOP` bit
(**1**). This can happen because of noise affecting the line or if the
transmitter clock is fast or slow compared to the receiver. In a real frame
error the stop bit will be present just at an incorrect time so the line will
continue to signal both high and low. The start of a line break (described
above) matches a frame error with all data bits zero and one frame error
interrupt will be raised. If the line stays zero until the break error occurs,
the frame error will be set at every char-time. Frame errors will continue to
be reported after a break error.

{{< wavejson >}}
{
  signal: [
    { name: 'Baud Clock',        wave: 'p............'                                                 },
    { name: 'rx',                wave: '10333333330..', data: [ "lsb", "", "", "", "", "", "", "msb" ] },
    {},
    { name: 'intr_rx_frame_err', wave: '0..........1.'},
  ],
  head: {
    text: 'Serial Receive with Framing Error',
  },
  foot: {
    text: [
      'tspan',
        ['tspan', 'start bit '],
        ['tspan', {class:'info h4'}, '0'],
        ['tspan', ' at cycle -1, stop bit '],
        ['tspan', {class:'error h4'}, '1'],
        ['tspan', ' missing at cycle 8'],
      ],
    tock: -2,
  }
}
{{< /wavejson >}}

The effects of the line being low for certain periods are summarized
in the table:

|Line low (bit-times) | Frame Err? | Break? | Comment |
|---------------------|------------|--------|---------|
|<10                  | If STOP=0  | No     | Normal operation |
|10 (with parity)     | No         | No     | Normal zero data with STOP=1 |
|10 (no parity)       | Yes        | No     | Frame error since STOP=0 |
|11 - RXBLVL*char     | Yes        | No     | Break less than detect level |
|\>RXBLVL*char        | Yes        | Once   | Frame error signalled at every char-time, break at RXBLVL char-times|

#### rx_timeout
The `rx_timeout` interrupt is triggered when the RX FIFO has data sitting in it
without software reading it for a programmable number of bit times (using the
baud rate clock as reference, programmable via {{< regref "TIMEOUT_CTRL" >}}). This is used to
alert software that it has data still waiting in the FIFO that has not been
handled yet. The timeout counter is reset whenever the FIFO depth is changed or
an `rx_timeout` event occurs. If the RX FIFO is full and new character is
received, it won't reset the timeout value. The software is responsible for
keeping the RX FIFO in the level below the watermark. The actual timeout time
can vary based on the reset of the timeout timer and the start of the
transaction. For instance, if the software resets the timeout timer by reading a
character from the RX FIFO and right after it there is a baud clock tick and the
start of a new RX transaction from the host, the timeout time is reduced by 1
and half baud clock periods.

#### rx_partity_err
The `rx_parity_err` interrupt is triggered if parity is enabled and
the RX parity bit does not match the expected polarity as programmed
in {{< regref "CTRL.PARITY_ODD" >}}.

# Programmers Guide

## Initialization

The following code snippet demonstrates initializing the UART to a programmable
baud rate, clearing the RX and TX FIFO, setting up the FIFOs for interrupt
levels, and enabling some interrupts. The NCO register controls the baud rate,
and should be set using the equation below, where `f_pclk` is the fixed clock
frequency and `f_baud` is the baud rate in bits per second. The UART uses the
primary clock `clk_i` as a clock source.

$$ NCO = {{2^{20} * f\_{baud}} \over {f\_{pclk}}} $$

Note that the NCO result from the above formula can be a fraction but
the NCO register only accepts an integer value. See the the
[Reception](#reception) and [Setting the baud
rate](#setting-the-baud-rate) sections for more discussion of the
baud rate error target and when care is needed.

Also note that because the baud rate is multiplied by 2^20 care is
needed not to overflow 32-bit registers. Baud rates can easily be more
than 12 bits. The code below is careful to force 64-bit
arithmetic. (Even if the complier is pre-computing constants there can
be unexpected overflow).

```cpp
#define CLK_FIXED_FREQ_HZ (50ULL * 1000 * 1000)

void uart_init(unsigned int baud) {
  // nco = 2^20 * baud / fclk. Assume NCO width is 16bit.
  uint64_t uart_ctrl_nco = ((uint64_t)baud << 20) / CLK_FIXED_FREQ_HZ;
  REG32(UART_CTRL(0)) =
      ((uart_ctrl_nco & UART_CTRL_NCO_MASK) << UART_CTRL_NCO_OFFSET) |
      (1 << UART_CTRL_TX) |
      (1 << UART_CTRL_RX);

  // clear FIFOs and set up to interrupt on any RX, half-full TX
  *UART_FIFO_CTRL_REG =
      UART_FIFO_CTRL_RXRST                 | // clear both FIFOs
      UART_FIFO_CTRL_TXRST                 |
      (UART_FIFO_CTRL_RXILVL_RXFULL_1 <<3) | // intr on RX 1 character
      (UART_FIFO_CTRL_TXILVL_TXFULL_16<<5) ; // intr on TX 16 character

  // enable only RX, overflow, and error interrupts
  *UART_INTR_ENABLE_REG =
      UART_INTR_ENABLE_RX_WATERMARK_MASK  |
      UART_INTR_ENABLE_TX_OVERFLOW_MASK   |
      UART_INTR_ENABLE_RX_OVERFLOW_MASK   |
      UART_INTR_ENABLE_RX_FRAME_ERR_MASK  |
      UART_INTR_ENABLE_RX_PARITY_ERR_MASK;

  // at the processor level, the UART interrupts should also be enabled
}
```

## Common Examples

The following code shows the steps to transmit a string of characters.

```cpp
int uart_tx_rdy() {
  return ((*UART_FIFO_STATUS_REG & UART_FIFO_STATUS_TXLVL_MASK) == 32) ? 0 : 1;
}

void uart_send_char(char val) {
  while(!uart_tx_rdy()) {}
  *UART_WDATA_REG = val;
}

void uart_send_str(char *str) {
  while(*str != '\0') {
    uart_send_char(*str++);
}
```

Do the following to receive a character, with -1 returned if RX is empty.

```cpp
int uart_rx_empty() {
  return ((*UART_FIFO_STATUS_REG & UART_FIFO_STATUS_RXLVL_MASK) ==
          (0 << UART_FIFO_STATUS_RXLVL_LSB)) ? 1 : 0;
}

int uart_rcv_char() {
  if(uart_rx_empty())
    return -1;
  return *UART_RDATA_REG;
}
```

## Interrupt Handling

The code below shows one example of how to handle all UART interrupts
in one service routine.

```cpp
void uart_interrupt_routine() {
  volatile uint32 intr_state = *UART_INTR_STATE_REG;
  uint32 intr_state_mask = 0;
  char uart_ch;
  uint32 intr_enable_reg;

  // Turn off Interrupt Enable
  intr_enable_reg = *UART_INTR_ENABLE_REG;
  *UART_INTR_ENABLE_REG = intr_enable_reg & 0xFFFFFF00; // Clr bits 7:0

  if (intr_state & UART_INTR_STATE_RX_PARITY_ERR_MASK) {
    // Do something ...

    // Store Int mask
    intr_state_mask |= UART_INTR_STATE_RX_PARITY_ERR_MASK;
  }

  if (intr_state & UART_INTR_STATE_RX_BREAK_ERR_MASK) {
    // Do something ...

    // Store Int mask
    intr_state_mask |= UART_INTR_STATE_RX_BREAK_ERR_MASK;
  }

  // .. Frame Error

  // TX/RX Overflow Error

  // RX Int
  if (intr_state & UART_INTR_STATE_RX_WATERMARK_MASK) {
    while(1) {
      uart_ch = uart_rcv_char();
      if (uart_ch == 0xff) break;
      uart_buf.append(uart_ch);
    }
    // Store Int mask
    intr_state_mask |= UART_INTR_STATE_RX_WATERMARK_MASK;
  }

  // Clear Interrupt State
  *UART_INTR_STATE_REG = intr_state_mask;

  // Restore Interrupt Enable
  *UART_INTR_ENABLE_REG = intr_enable_reg;
}
```

One use of the `rx_timeout` interrupt is when the {{< regref "FIFO_CTRL.RXILVL" >}}
is set greater than one, so an interrupt is only fired when the fifo
is full to a certain level. If the remote device sends fewer than the
watermark number of characters before stopping sending (for example it
is waiting an acknowledgement) then the usual `rx_watermark` interrupt
would not be raised. In this case an `rx_timeout` would generate an
interrupt that allows the host to read these additional characters. The
`rx_timeout` can be selected based on the worst latency experienced by a
character. The worst case latency experienced by a character will happen
if characters happen to arrive just slower than the timeout: the second
character arrives just before the timeout for the first (resetting the
timer), the third just before the timeout from the second etc. In this
case the host will eventually get a watermark interrupt, this will happen
`((RXILVL - 1)*timeout)` after the first character was received.

## Device Interface Functions (DIFs)

{{< dif_listing "sw/device/lib/dif/dif_uart.h" >}}

## Register Table

{{< incGenFromIpDesc "../data/uart.hjson" "registers" >}}
