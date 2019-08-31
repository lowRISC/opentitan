{{% lowrisc-doc-hdr UART HWIP Technical Specification }}
{{% regfile uartcfg.hjson}}

{{% section1 Overview }}

This document specifies UART hardware IP functionality. This module
conforms to the
[Comportable guideline for peripheral device functionality.](../../../doc/rm/comportability_specification.md)
See that document for integration overview within the broader
top level system.

{{% toc 3 }}

{{% section2 Features }}

- 2-pin full duplex external interface
- 8-bit data word, optional even or odd parity bit per byte
- 1 stop bit
- 32 x 8b RX buffer
- 32 x 8b TX buffer
- Programmable baud rate
- Interrupt for overflow, frame error, parity error, break error, receive
  timeout

{{% section2 Description }}

The UART module is a serial-to-parallel receive (RX) and parallel-to-serial
(TX) full duplex design intended to communicate to an outside device, typically
for basic terminal-style communication. It is programmed to run at a particular
BAUD rate and contains only a transmit and receive signal to the outside world,
i.e. no synchronizing clock. The programmable BAUD rate guarantees to be met up
to 1Mbps.

{{% section2 Compatibility }}

The UART is compatible with the feature set of H1 Secure Microcontroller UART as
used in the [Chrome OS cr50][chrome-os-cr50] codebase. Additional features such
as parity have been added.

[chrome-os-cr50]: https://chromium.googlesource.com/chromiumos/platform/ec/+/master/chip/g/

{{% section1 Theory of Operations }}

{{% section2 Block Diagram }}

![UART Block Diagram](block_diagram.svg)

{{% section2 Hardware Interfaces }}

{{% hwcfg uart}}

{{% section2 Design Details }}

### Serial interface (both directions)

TX/RX serial lines are high when idle. Data starts with START bit (1-->0)
followed by 8 data bits. Least significant bit is sent first. If parity feature
is turned on, at the end of the data bit, odd or even parity bit follows then
STOP bit completes one byte data transfer.

```wavejson
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
```

### Transmission

A write to !!WDATA enqueues a data byte into the 32 depth write
FIFO, which triggers the transmit module to start UART TX serial data
transfer. The TX module dequeues the byte from the FIFO and shifts it
bit by bit out to the UART TX pin when BAUD tick is asserted.

### Reception

The RX module samples the RX input pin with 16x oversampled BAUD
clock. After it detects START bit, RX module gathers incoming serial
bits into one byte data and pushes to 32 depth RX FIFO if it receives
optional parity bit and correct STOP bit.  These pushed data can be read
out by reading !!RDATA register.

### Interrupts

UART module has a few interrupts including general data flow interrupts
and unexpected event interrupts.

If the TX or RX FIFO hits the designated depth of entries, interrupts
`tx_watermark` or `rx_watermark` are raised to inform FW.  FW can
configure the watermark value via registers !!FIFO_CTRL.RXILVL or
!!FIFO_CTRL.TXILVL .

If either FIFO receives an additional write request when its FIFO is full,
the interrupt `tx_overflow` or `rx_overflow` is asserted and the character
is dropped.

The `rx_frame_err` interrupt is triggered if RX module receives the
`START` bit and series of data bits but did not detect `STOP` bit (`1`).

```wavejson
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
```

The `rx_break_err` interrupt is triggered if a break condition has
been detected. A break condition is defined as a programmable number
of characters (via !!CTRL.RXBLVL, either 2, 4, 8, or 16) all equal to
`0` during a frame error. This typically indicates that the UART is not
being driven at this time.

The `rx_timeout` interrupt is triggered when the RX FIFO has data sitting
in it without software reading it for a programmable number of bit times
(with baud rate clock as reference, programmable via !!TIMEOUT_CTRL). This
is used to alert software that it has data still waiting in the FIFO that
has not been handled yet. The timeout counter is reset whenever software
reads a character from the FIFO, or if a new character is received from
the line.

The `rx_parity_err` interrupt is triggered if parity is enabled and
the RX parity bit does not match the expected polarity as programmed
in !!CTRL.PARITY_ODD.

{{% section1 Programmers Guide }}

{{% section2 Initialization }}

The following code snippet shows initializing the UART to a programmable
baud rate, clearing the RX and TX FIFO, setting up the FIFOs for interrupt
levels, and enabling some interrupts. The NCO register controls the baud
rate, and should be set to `(2^20*baud)/freq`, where `freq` is the fixed
clock frequency. The UART uses `clock_primary` as a clock source.

$$ NCO = {{2^{20} * f_{baud}} \over {f_{pclk}}} $$

```cpp
#define CLK_FIXED_FREQ_MHZ 48

void uart_init(int baud) {
  // set baud rate. NCO = baud * 2^20 / clock_freq =~ baud / freq_mhz
  int setting = baud / CLK_FIXED_FREQ_MHZ;
  *UART_CTRL_NCO_REG = setting;

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

{{% section2 Common Examples }}

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
  while(*str != \0) {
    uart_send_char(*str++);
}
```

Do the following to receive a character, with -1 returned if RX is empty.

```cpp
int uart_rx_empty() {
  return ((*UART_FIFO_STATUS_REG & UART_FIFO_STATUS_RXLVL_MASK) ==
          (0 << UART_FIFO_STATUS_RXLVL_LSB)) ? 1 : 0;
}

char uart_rcv_char() {
  if(uart_rx_empty())
    return 0xff;
  return *UART_RDATA_REG;
}
```

{{% section2 Interrupt Handling }}

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

One use of the `rx_timeout` interrupt is when the !!FIFO_CTRL.RXILVL
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

{{% section2 Register Table }}

{{% registers x }}
