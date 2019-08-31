{{% lowrisc-doc-hdr Simple UART }}
{{% regfile uart.hjson }}

The simple UART provides an asynchronous serial interface that can
operate at programmable BAUD rates. The main features are:

- 32 byte transmit FIFO
- 32 byte receive FIFO
- Programmable fractional baud rate generator
- Hardware flow control (when enabled)
- 8 data bits
- optional parity bit (even or odd)
- 1 stop bit

{{% toc 3 }}

## Compatibility

The simple UART is compatible with the H1 Secure Microcontroller UART
used in the Chrome OS cr50 codebase
(https://chromium.googlesource.com/chromiumos/platform/ec/+/master/chip/g/).
The parity option has been added.

## Theory of operation

*TODO block diagram of UART*

The UART can connect to four external pins:
* TX: transmit data output.
* RX: receive data input.
* RTS: request to send flow control output. This pin is active low.
* CTS: clear to send flow control input. This pin is active low.

### Serial data format

The serial line is high when idle. Characters are sent using a start
bit (low) followed by 8 data bits sent least significant
first. Optionally there may be a parity bit which is computed to give
either even or odd parity. Finally there is a stop bit (high). The
start bit for the next character may immediately follow the stop bit,
or the line may be in the idle (high) state for some time.

#### Serial waveform

```wavejson
{signal: [
  {name:'Baud Clock',  wave: 'p...........' },
  {name:'Data',        wave: '10========1.',
   data: [ "lsb", "", "", "", "", "", "", "msb" ] },
  {name:'With Parity', wave: '10=========1',
   data: [ "lsb", "", "", "", "", "", "", "msb", "par" ] },
 ],
 head:{
   text:'Serial Line format',
   tick:0,
 }
}
```

### Transmission

The UART will normally format characters (add start, parity and stop
bits) and transmit them whenever the line is idle and there is a
character available in the transmit FIFO.

If !!CTRL.CTS is set then the CTS input is checked before
starting a transmission. If CTS is active (low) then the character is
transmitted as usual. If CTS is inactive (high) then tranmission is
delayed until CTS is asserted again. Note that once transmission of a
character has started the state of the CTS line will have no effect
until the stop bit has been transmitted.

### Reception

The internal clock runs at 16x the baud rate. This is used to sample
the receive data. While the line is idle the data is sampled
high. After the line goes low the data and parity bits are sampled in
the middle of their bit time and the character received. The stop bit
is checked in the middle of its bit time and must be high or a framing
error will be reported.

If there is space in the receive FIFO then the received character is
written to the FIFO otherwise it is discarded and the RX overrun
interrupt set. *TODO what happens if it has a parity or framing
error, is the character added to the FIFO or not?*.

For a character to be correctly recieved the local clock and the
peer's transmit clock must drift by no more than half a bit time
between the start of the start bit and the mid-point of the stop
bit. Thus without parity the clocks can differ by no more than 5.2%
(0.5 bit-times / 9.5 bit-times), and with parity they can differ by no
more than 4.7% (0.5 bit-times / 10.5 bit-times).

The stop bit in the serial line format ensures that the line will
never be low for more than 9 (10 with parity) bit-times. If the line
is detected low for multiple character times (configured in the
!!ICTRL.RXBLVL field) then the receiver will detect a break
condition and signal an interrupt. *TODO will any zero characters be
received? Depends on answer to framing error question?*

If !!CTRL.CTS is set, the receiver provides flow control by
driving the RTS output. When the number of characters in the receive
FIFO is below the level set in !!FIFO.RXILVL the UART will drive
this pin low (active) to indicate it is ready to accept data. Once the
FIFO has reached the programmed level the UART will drive the pin high
(inactive) to stop the remote device sending more data.

If !!CTRL.CTS is clear, active flow control is disabled. The UART
will drive the RTS pin low (active) whenever its receiver is enabled
(!!CTRL.RX set) and high (inactive) whenever the receiver is
disabled.

*TODO say something about the RX noise filter enable bit*

## Programmer Guide


### Initialization

The internal clock must be configured to run at 16x the required BAUD
rate. This is done by programming the Numerically Controlled
Oscillator (!!NCO register). The register should be set to
(2<sup>20</sup>*f<sub>baud</sub>)/f<sub>pclk</sub>, where
f<sub>baud</sub> is the required baud rate and f<sub>pclk</sub> is the
peripheral clock provided to the UART.

Care should be taken not to overflow the registers during the baud
rate setting, 64-bit arithmetic may need to be forced. For example:

```c
	long long setting = (16 * (1 << UART_NCO_WIDTH) *
			     (long long)CONFIG_UART_BAUD_RATE / PCLK_FREQ);
	/* set frequency */
	GR_UART_NCO(uart) = setting;
```

During initialization the !!FIFO register should be written to
clear the FIFOs and set the trigger levels for interrupt and flow
control. This should be done before enabling the UART and flow control
by setting the !!CTRL register.

### Character FIFOs

The transmit and recieve FIFOs are always used and each are always 32
characters deep.

Prior to adding a character to the transmit FIFO the !!STATE.TX
bit can be checked to ensure there is space in the FIFO. If a
character is written to a full FIFO then the character is discarded,
the !!STATE.TXO bit is set and a TX overrun interrupt raised.

If the receive FIFO is full when a new character is received thenthe
!!STATE.RXO bit is set and a RX overrun interrupt raised.

The overrun status is latched, so will persist to indicate characters
have been lost, even if characters are removed from the corresponding
FIFO. The state must be cleared by writing 1 to !!STATECLR.TXO or
!!STATECLR.RXO.

The number of characters in the FIFO selects the interrupt
behaviour. The TX interrupt will be raised when there are fewer
characters in the FIFO than configured in the !!FIFO.TXILVL
field. The RX interrupt will be raised when there are the same or more
characters in the FIFO than configured in the !!FIFO.RXILVL
field. *TODO check I understand these levels*

The number of characters currently in each FIFO can always be read
from the !!RFIFO register.

### Receive timeout

The receiver timeout mechanism can raise an interrupt if the receiver
detects the line to be idle for a long period. This is enabled and the
timeout configured in the !!RXTO register.

### Interrupts

The UART has eight interrupts:
- TX: raised if the transmit FIFO is past the trigger level
- RX: raised if the receive FIFO is past the trigger level
- TXOV: raised if the transmit FIFO has overflowed
- RXOV: raised if the receive FIFO has overflowed
- RXF: raised if a framing error has been detected on receive
- RXB: raised if a break condition is detected on receive
- RXTO: raised if the receiver has not received any characters in a time
- RXPE: raised if the receiver has detected a parity error

The current state of the interrupts can be read from the !!ISTATE
register. Each interrupt has a corresponding bit in the
!!ISTATECLR register that must be written with a 1 to clear the
interrupt.

Interrupts are enabled in the !!ICTRL register (note the bit
assignment does not match the other registers bacuse this register
also configurs the break condition). This registe just configures if
the interrupt will be signalled to the system interrupt controller, it
will not change or mask the value in the !!ISTATE register.

### Debug Features

There are two loopback modes that may be useful during debugging.

System loopback is enabled by setting !!CTRL.SLPBK. Any
characters written to the transmit buffer will be copied to the
receive buffer. The state of the RX and CTS pins are ignored. Hardware
flow control should be disabled when this mode is used.

Line loopback is enabled by setting !!CTRL.LLPBK. Any data
received on the RX pin is transmitted on the TX pin. Data is retimed
by the peripheral clock, so this is only reliable if f<sub>pclk</sub>
is more than twice the baud rate being received. Hardware flow
control, the TX and RX fifos and interrupts should be disabled when
this mode is used.

Direct control of the TX pin can be done by setting the value to drive
in the !!OVRD.TXVAL bit with the !!OVRD.TXEN bit set.  Direct control
of the RTS pin can be done by setting the value to drive in the
!!OVRD.RTSVAL bit with the !!OVRD.RTSEN bit set.

The most recent samples from the receive and CTS pins gathered at 16x
the baud clock can be read from the !!VAL register if
!!CTRL.RCOS is set.

Interrupts can be tested by configuring the interrupts to be raised in
the !!ITOP register and setting the !!ITCR bit. This will
raise the corresponding interrupts to the system. It is recommended
the regular sources are disabled in the !!ICTRL register when
this feature is used. *TODO is this implementation?*



## Implementation Guide

The toplevel of the UART has the following signals that connect to
external pins:
- TX data output connects to external pin
- RX: receive data input connects to external pin
- RTS: request to send flow control output. This pin is active
  low. Connects to external pin.
- CTS: clear to send flow control input. This pin is active
  low. Connects to external pin.

The following signals connect to the interrupt controller:
- txint
- rxint
- txoint
- rxoint
- rxfint
- rxbint
- rxtoint
- rxpeint

A clock with some spec must be provided:
- pckl

The main register interface is an APB slave using:
- APB signals

An additional 32-bit scratch register !!DVREG is provided.

The UART code has no build-time options. (Unless it does.)

## Registers
{{% registers x }}
