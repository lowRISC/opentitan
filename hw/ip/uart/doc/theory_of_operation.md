# Theory of Operation

## Block Diagram

![UART Block Diagram](../doc/block_diagram.svg)

## Design Details

### Serial interface (both directions)

The TX/RX serial lines are high when idle. Data starts with a START bit (high
idle state deasserts, **1**-->**0**) followed by 8 data bits. The least
significant bit is sent first. If the parity feature is turned on then an odd or
even parity bit follows after the data bits. Finally a STOP (**1**) bit
completes one byte of data transfer.

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

A write to [`WDATA`](registers.md#wdata) enqueues a data byte into the 32 byte deep write FIFO, which
triggers the transmit module to start UART TX serial data transfer. The TX
module dequeues the byte from the FIFO and shifts it bit by bit out to the UART
TX pin on positive edges of the baud clock.

If TX is not enabled, written DATA into FIFO will be stacked up and sent out
when TX is enabled.

When the FIFO becomes empty as part of transmission, a TX FIFO empty interrupt will be raised.
This is separate from the TX FIFO water mark interrupt.


### Reception

The RX module oversamples the RX input pin at 16x the requested
baud clock. When the input is detected low the receiver will check
half a bit-time later (i.e. 8 cycles of the oversample clock) that the
line is still low before detecting the START bit. If the line has
returned high the glitch is ignored. After it detects the START bit,
the RX module samples at the center of each bit-time and gathers
incoming serial bits into a character buffer. If the STOP bit is
detected as high and the optional parity bit is correct the data byte
is pushed into a 32 byte deep RX FIFO. The data can be read out by
reading [`RDATA`](registers.md#rdata) register.

This behaviour of the receiver can be used to compute the approximate
baud clock frequency error that can be tolerated between the
transmitter at the other end of the cable and the receiver. The
initial sample point is aligned with the center of the START bit. The
receiver will then sample every 16 cycles of the 16 x baud clock, the
diagram below shows the number of ticks after the centering that each
bit is captured. Because of the frequency difference between the
transmitter and receiver the actual sample point will drift compared to
the ideal center of the bit. In order to correctly receive the STOP
bit it must be sampled between the "early" and "late" points shown
on the diagram, which are half a bit-time or 8 ticks of the 16x baud
clock before or after the center. If the transmitter is considered
"ideal" then the local clock must thus differ by no more than plus or
minus 8 ticks in 144 or approximately +/- 5.5%. If parity is enabled
the stop bit will be a bit time later, so this becomes 8/160 or about
+/- 5%.

```wavejson
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
```

In practice, the transmitter and receiver will both differ from the
ideal baud rate. Since the worst case difference for reception is 5%,
the uart can be expected to work if both sides are within +/- 2.5% of
the ideal baud rate.

### Setting the baud rate

The baud rate is set by writing to the [`CTRL.NCO`](registers.md#ctrl) register field. This should be
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
If the TX FIFO level becomes smaller than the TX water mark level (configurable via [`FIFO_CTRL.RXILVL`](registers.md#fifo_ctrl) and [`FIFO_CTRL.TXILVL`](registers.md#fifo_ctrl)), the `tx_watermark` interrupt is raised to inform SW.
If the RX FIFO level becomes greater than or equal to RX water mark level (configurable via [`FIFO_CTRL.RXILVL`](registers.md#fifo_ctrl) and [`FIFO_CTRL.TXILVL`](registers.md#fifo_ctrl)), the `rx_watermark` interrupt is raised to inform SW.

Note that the watermark interrupts are edge triggered events.
This means the interrupt only triggers when the condition transitions from untrue->true.
This is especially important in the tx_watermark case.
When the TX FIFO is empty, it by default satisfies all the watermark conditions.
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
character-times (via [`CTRL.RXBLVL`](registers.md#ctrl), either 2, 4, 8, or 16). A
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
status can be read from the [`STATUS.BREAK`](registers.md#status) bit. If STATUS.BREAK is set
but [`INTR_STATE.BREAK`](registers.md#intr_state) is clear then the line break has already caused
an interrupt that has been cleared but the line break is still going
on. If [`STATUS.BREAK`](registers.md#status) is clear but [`INTR_STATE.BREAK`](registers.md#intr_state) is set then
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
baud rate clock as reference, programmable via [`TIMEOUT_CTRL`](registers.md#timeout_ctrl)). This is used to
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

#### rx_parity_err
The `rx_parity_err` interrupt is triggered if parity is enabled and
the RX parity bit does not match the expected polarity as programmed
in [`CTRL.PARITY_ODD`](registers.md#ctrl--parity_odd).
