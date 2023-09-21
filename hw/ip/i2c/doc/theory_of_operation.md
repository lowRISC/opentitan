# Theory of Operation

## Block Diagram

![](../doc/I2C_block_diagram.svg)

## Design Details

### Functional Modes

I2C IP is a host-target combo that can function as either an I2C host or an I2C target.
Although it is conceivable that an I2C combo can optionally function as both a host and a target at the same time, we do not support this feature at this time.
These functional modes are enabled at runtime by setting the register fields [`CTRL.ENABLEHOST`](registers.md#ctrl) and [`CTRL.ENABLETARGET`](registers.md#ctrl).

### Virtual Open Drain

In devices which lack a true open drain buffer functionality, this IP implements a "virtual Open Drain" functionality.
The SDA and SCL outputs are assumed to be connected to a tri-state buffer, with independent enable outputs for both signals.

Rather than toggling the buffer inputs, the buffer inputs are *continuously asserted low*, and instead the buffer *enable* signals are toggled.
The SDA or SCL buffers are enabled for a logical "Low" output on the respective signal, and are disabled for logical "High" outputs.
This arrangement allows the output pins to float high if there is no conflict from external devices, or to be pulled low if there is a conflict (as is required for clock-stretching or--in future revisions-- multi-host functionality).

This arrangement is necessary for FPGA builds.


### Override Mode for Direct Pin Access

The I2C hardware interface consists of two external pins, SCL and SDA, whose behavior is described in the [I2C specification (rev. 6)](https://web.archive.org/web/20210813122132/https://www.nxp.com/docs/en/user-guide/UM10204.pdf).
These pins are typically controlled by an internal state machine.
However, there is a simpler "override" mode, by which these pins can be directly manipulated by software.
This override mode is useful for both troubleshooting and error recovery.

To enter override mode, the register field [`OVRD.TXOVRDEN`](registers.md#ovrd) is asserted by software.
In this state the output drivers `scl_tx_o` and `sda_tx_o` are controlled directly by the register fields [`OVRD.SCLVAL`](registers.md#ovrd) and [`OVRD.SDAVAL`](registers.md#ovrd).
When [`OVRD.SCLVAL`](registers.md#ovrd) and [`OVRD.SDAVAL`](registers.md#ovrd) are set high, the virtual open drain configuration will leave the output resistively pulled high, and controllable by remote targets.
In this state, with SCL or SDA asserted high, the register fields [`VAL.SCL_RX`](registers.md#val) and [`VAL.SDA_RX`](registers.md#val) can be used to receive inputs (including remote acknowledgments) from target devices.

#### FSM control of SCL and SDA

While in host mode, SCL and SDA are generated through the internal state machine.
Since SCL is directly decoded from the states, it can have short glitches during transition which the external target may be sensitive to if it is not using an over-sampling scheme.
To counter this, the SCL and SDA outputs from the internal state machine are flopped before they are emitted.

This adds a one cycle module clock delay to both signals.
If the module clock is sufficiently faster than I2C line speeds (for example 20MHz), this is not an issue.
However if the line speeds and the module clock speeds become very close (2x), the 1 cycle delay may have an impact, as the internal state machine may mistakenly think it has sampled an SDA that has not yet been updated.

Therefore, it is recommended that the internal module clock frequency is much higher than the line speeds.
Another reason to have this higher internal clock frequency is that the timing parameters can be more accurately defined, which helps attain the desired I2C clock rate.
Since there are currently also a few cycles discrepancy between the specified timings and the actual ones (as described in the [Programmer's Guide](./programmers_guide.md#timing-parameter-tuning-algorithm)), it is recommended that the internal module clock frequency is at leat 50x higher than the I2C line speeds.

### Byte-Formatted Programming Mode

This section applies to I2C in the host mode.
The state-machine-controlled mode allows for higher-speed operation with less frequent software interaction.
In this mode, the I2C pins are controlled by the state machine, which in turn is controlled by a sequence of formatting indicators.
These indicators determine:
- The sequence of bytes which should be transmitted on the SDA and SCL pins.
- The periods between transmitted bytes when the state-machine should stop transmission and instead read back a fixed number of bytes.
- Which bytes should be preceded by a START symbol.
- Which bytes should be followed by a STOP symbol.

The format indicator consists of 13-bits.
That is of one single format byte (entered into the format FIFO through [`FDATA.FBYTE`](registers.md#fdata)), and five 1-bit flags (entered into the format FIFO through registers [`FDATA.READB`](registers.md#fdata), [`FDATA.RCONT`](registers.md#fdata), [`FDATA.START`](registers.md#fdata), [`FDATA.STOP`](registers.md#fdata) and [`FDATA.NAKOK`](registers.md#fdata))

The I2C reads each format indicator from the head of FMT_FIFO, and processes them in turn.
If none of the flags are set for the format indicator, the I2C FSM simply transmits the format byte onto the SCL and SDA pins according to the specification, waits for acknowledgement, and then proceeds to the next format indicator.
The format flags modulate the behavior as follows.
- READB (corresponds to [`FDATA.READB`](registers.md#fdata)):
Signifies the format byte ([`FDATA.FBYTE`](registers.md#fdata)) should be treated as an unsigned number, R, and prompts the state machine to read R bytes from the target device.
Bytes read from the bus are inserted into the RX FIFO where they can be accessed by software.
A value of 0 is treated as a read of 256 bytes.
To read a larger byte stream, multiple 256-byte reads can be chained together using the RCONT flag.
- RCONT (corresponds to FIFO inputs [`FDATA.RCONT`](registers.md#fdata), only used with READB):
    - If RCONT is set, the format byte represents part of a longer sequence of reads, allowing for reads to be chained indefinitely.
    - The RCONT flag indicates the final byte returned with the current read should be responded to with an ACK, allowing the target to continue sending data.
    (Note that the first R-1 bytes read will still be acknowledged regardless of whether RCONT is asserted or not.)
- START (corresponds to [`FDATA.START`](registers.md#fdata), Ignored when used with READB):
Issue a START condition before transmitting the format byte on the bus.
This flag may also be used to issue a repeated start condition.
- STOP (corresponds to [`FDATA.STOP`](registers.md#fdata)):
Issue a STOP signal after processing this current entry in the FMT FIFO.
Note that this flag is not compatible with (READB & RCONT), and will cause bus conflicts.
- NAKOK (corresponds to [`FDATA.NAKOK`](registers.md#fdata), Not compatible with READB):
Typically every byte transmitted must also receive an ACK signal, and the IP will raise an exception if no ACK is received.
However, there are some I2C commands which do not require an ACK.
In those cases this flag should be asserted with FBYTE indicating no ACK is expected and no interrupt should be raised if the ACK is not received.

### Target Address Registers

I2C target device is assigned two 7-bit address and 7-bit mask pairs.
The target device accepts a transaction if the result of the bitwise AND operation performed on the transaction address sent by the host and a mask matches the assigned address corresponding to the mask.
In other words, address matching is performed only for bits where the mask is "1".
Thus, with the masks set to all ones (0x7F), the target device will respond to either of the two assigned unique addresses and no other.
If the mask and the assigned address both have zeros in a particular bit position, that bit will be a match regardless of the value of that bit received from the host.
Note that if, in any bit position, the mask has zero and the assigned address has one, no transaction can match and such mask/address pair is effectively disabled.
The assigned address and mask pairs are set in registers [`TARGET_ID.ADDRESS0`](registers.md#target_id), [`TARGET_ID.MASK0`](registers.md#target_id), [`TARGET_ID.ADDRESS1`](registers.md#target_id), and [`TARGET_ID.MASK1`](registers.md#target_id).

### Acquired Formatted Data

This section applies to I2C in the target mode.
When the target accepts a transaction, it inserts the transaction address, read/write bit, and START signal sent by the host into ACQ FIFO where they can be accessed by software.
ACQ FIFO output corresponds to [`ACQDATA`](registers.md#acqdata).
If the transaction is a write operation (R/W bit = 0), the target proceeds to read bytes from the bus and insert them into ACQ FIFO until the host terminates the transaction by sending a STOP or a repeated START signal.
A STOP or repeated START indicator is inserted into ACQ FIFO as the next entry following the last byte received, in which case other bits may be junk.
The following diagram shows consecutive entries inserted into ACQ FIFO during a write operation:

![](../doc/I2C_acq_fifo_write.svg)

If the transaction is a read operation (R/W bit = 1), the target pulls bytes out of TX FIFO and transmits them to the bus until the host signals the end of the transfer by sending a NACK signal.
If TX FIFO holds no data, or if the ACQ FIFO contains more than 1 entry, the target will hold SCL low to stretch the clock and give software time to write data bytes into TX FIFO or handle the available command.
See [stretching during read](#stretching-during-read) for more details.
TX FIFO input corresponds to [`TXDATA`](registers.md#txdata).
Typically, a NACK signal is followed by a STOP or repeated START signal and the IP will raise an exception if the host sends a STOP signal after an ACK.
An ACK/NACK signal is inserted into the ACQ FIFO as the first bit (bit 0), in the same entry with a STOP or repeated START signal.
For ACK and NACK signals, the value of the first bit is 0 and 1, respectively.
The following diagram shows consecutive entries inserted into ACQ FIFO during a read operation:

![](../doc/I2C_acq_fifo_read.svg)

The ACQ FIFO entry consists of 10 bits:
- Address (bits 7:1) and R/W bit (bit 0) or data byte
- Format flags (bits 9:8)
The format flags indicate the following signals received from the host:
- START: 01
- STOP: 10
- repeated START: 11
- No START, or STOP: 00

### Timing Control Registers

For Standard-mode, Fast-mode and Fast-mode Plus, the timing requirements for each transaction are detailed in Table 10 of the [I2C specification (rev. 6)](https://web.archive.org/web/20210813122132/https://www.nxp.com/docs/en/user-guide/UM10204.pdf).
To claim complete compatibility at each mode, the state machine timings need to be adapted to whether there are Standard-mode, Fast-mode and Fast-mode Plus targets on the bus.
Furthermore, depending on the actual capacitance of the bus, even a bus with all Fast-mode Plus capable targets may have to operate at slower speeds than 1 Mbaud.
For example, the host may need to run at lower frequencies, as discussed in Section 5.2 of the specification, but the computation of the nominal frequency will depend on timing specifications in Table 10, in this case particularly, the limits on t<sub>LOW</sub>, t<sub>HIGH</sub>, t<sub>r</sub>, and t<sub>f</sub>.
Assuming no clock stretching, for a given set of these four parameters the baud rate is then given to be:
$$ 1/f\_{SCL}=t\_{LOW}+t\_{HIGH}+t\_{r}+t\_{f}. $$

Thus in order to ensure compliance with the spec in any particular configuration, software will program the I2C host IP with explicit values for each of the following timing parameters, as defined in Figure 38 of the specification.
- t<sub>LOW</sub>: set in register [`TIMING0.TLOW`](registers.md#timing0).
- t<sub>HIGH</sub>: set in register [`TIMING0.THIGH`](registers.md#timing0).
- t<sub>r</sub>: set in register [`TIMING1.T_R`](registers.md#timing1).
(Note: The rise time cannot be explicitly controlled by internal hardware, and will be a function of the capacitance of the bus.
Thus this parameter is largely budgetary, meaning that it tells the state machine how much time to wait for an RC rise.)
- t<sub>f</sub>: set in register [`TIMING1.T_F`](registers.md#timing1).
(Note: The fall time cannot be explicitly controlled by internal hardware, and is a function of the pin driver.
Thus this parameter is also budgetary.
Given that the actual fall time cannot be controlled to stay above the minimum values set in Table 10 of the specification, and so this in this regard this module currently is not strictly compliant to the I2C spec.)
- t<sub>SU,STA</sub>: set in register [`TIMING2.TSU_STA`](registers.md#timing2)
- t<sub>HD,STA</sub>: set in register [`TIMING2.THD_STA`](registers.md#timing2)
- t<sub>SU,DAT</sub>: set in register [`TIMING3.TSU_DAT`](registers.md#timing3).
Taken to be synonymous with T<sub>SU,ACK</sub>
- t<sub>HD,DAT</sub>: set in register [`TIMING3.THD_DAT`](registers.md#timing3).
Taken to be synonymous with T<sub>HD,ACK</sub>.
Moreover, since the pin driver fall time is likely to be less then one clock cycle, this parameter is also taken to be synonymous with the parameters T<sub>VD,DAT</sub> and T<sub>VD,ACK</sub>
- t<sub>SU,STO</sub>: set in register [`TIMING4.TSU_STO`](registers.md#timing4).
- t<sub>BUF</sub>: set in register [`TIMING4.T_BUF`](registers.md#timing4)

The values programmed into the registers [`TIMING0`](registers.md#timing0) through [`TIMING4`](registers.md#timing4) are to be expressed in units of the input clock period.
It is important that the internal clock is at least 50x the bus clock so that the proportions of the timings can be accurately captured.
Note in order to ensure compliance with the I2C spec, firmware must program these registers with values within the ranges laid out in Table 10 of the specification.
These values can be directly computed using DIFs given the desired speed standard, the desired operating frequency, and the actual line capacitance.
These timing parameters are then fed directly to the I2C state machine to control the bus timing.

A detailed description of the algorithm for determining these parameters--as well as a couple of concrete examples--are given in the [Programmer's Guide](./programmers_guide.md#timing-parameter-tuning-algorithm).

### Timeout Control
A malfunctioning (or otherwise very slow) target device can hold SCL low indefinitely, stalling the bus.
For this reason [`TIMEOUT_CTRL`](registers.md#timeout_ctrl) provides a clock-stretching timeout mechanism to notify firmware of this sort of condition.
If [`TIMEOUT_CTRL.EN`](registers.md#timeout_ctrl) is asserted, an interrupt will be asserted when the IP detects that another device (a target or, in possible future revisions, an alternate host) has been holding SCL low for more than [`TIMEOUT_CTRL.VAL`](registers.md#timeout_ctrl) clock ticks.


This feature is added as a utility, though it is not required by the I2C specification.
However, in some applications it could be used in protocols which build upon I2C.
For instance, SMBus applications using this IP could in principle use this to support SMBus timeouts.
(Note: This is just an example application of this feature.
Other features may also be required for complete SMBus functionality.)

### Clock Stretching
As described in the I2C specification, a target device can pause a transaction by holding SCL low.
There are 3 cases in which this design stretches the clock.
In all cases described below, a target begins to stretch the clock after the ACK bit.
In the first two scenarios, it is after the ACK bit sent by the target, in the last scenario, it is after the host's ACK bit.

#### Stretching after address read
- When a target device receives a start, the address and R/W bit are written into the ACQ FIFO.
- If there is no space in the ACQ FIFO to receive such a write, the target stretches the clock after the ACK bit and waits for software to make space.
- The `acq_full` interrupt is generated to alert software to such a situation.

#### Stretching during write
- Similar to the scenario above, if the host tries to write a data byte into the ACQ FIFO when there is no available space, the clock is also stretched after the ACK bit.
- The `acq_full` interrupt is generated to alert software to such a situation.

#### Stretching during read
- When a target device receives a start and read command, it may stretch the clock for either of the following two reasons.
  - If there is no data available to be sent back (TX FIFO empty case), the target stretches the clock until data is made available by software.
  - If there is more than 1 entry in the ACQ FIFO.
    - Having more than 1 entry in the ACQ FIFO suggests there is potentially an unhandled condition (STOP / RESTART) or an unhandled command (START) that requires software intervention before the read can proceed.
- The `tx_stretch` interrupt is generated to alert software to such a situation.


### Interrupts
The I2C module has a few interrupts including general data flow interrupts and unexpected event interrupts.

#### Host Mode
If the RX FIFO exceeds the designated depth of entries, the interrupt `rx_threshold` is raised to inform firmware.
Firmware can configure the threshold value via the register [`FIFO_CTRL.RXILVL`](registers.md#fifo_ctrl).

Meanwhile it the FMT FIFO level falls below a designated depth of entries the `fmt_threshold` interrupt is raised.
(Note that this behavior differs from similar interrupts in other modules, such as the UART IP module.)
Firmware can configure the threshold value via the register [`FIFO_CTRL.FMTILVL`](registers.md#fifo_ctrl).

If either FIFO receives an additional write request when its FIFO is full, the interrupt `fmt_overflow` or `rx_overflow` is asserted and the format indicator or character is dropped.

If the module transmits a byte, but receives no ACK signal, the `nak` interrupt is usually asserted.
In cases where a byte is transmitted and no ACK is expected or required, that byte should be submitted with NAKOK flag also asserted.

When the I2C module is in transmit mode, the `scl_interference` or `sda_interference` interrupts will be asserted if the IP identifies that some other device (host or target) on the bus is forcing either signal low and interfering with the transmission.
It should be noted that the `scl_interference` interrupt is not raised in the case when the target device is stretching the clock.
(However, it may be raised if the target allows SCL to go high and then pulls SCL down before the end of the current clock cycle.)

A target device should never assert 0 on the SDA lines, and in the absence of multi-host support, the `sda_interference` interrupt is raised whenever the host IP detects that another device is pulling SDA low.

On the other hand, it is legal for the a target device to assert SCL low for clock stretching purposes.
With clock stretching, the target can delay the start of the following SCL pulse by holding SCL low between clock pulses.
However the target device must assert SCL low before the start of the SCL pulse.
If SCL is pulled low during an SCL pulse which has already started, this interruption of the SCL pulse will be registered as an exception by the I2C core, which will then assert the `scl_interference` interrupt.

```wavejson
{signal: [
  {name: 'Clock', wave: 'p.....|.......|......'},
  {name: 'SCL Host Driver', wave: '0.z..0|.z....0|..z.x.'},
  {name: 'SCL Target Driver', wave: 'z.....|0..z...|...0..'},
  {name: 'SCL bus', wave: '0.u..0|...u..0|..u0..'},
  {name: 'scl_interference', wave: '0.....|.......|....1.'},
],
  head: {text: 'SCL pulses: Normal SCL pulse (Cycle 3),  SCL pulse with clock stretching (cycle 11), and SCL interference (interrupted SCL pulse)',tick:1}}
```


Though normal clock stretching does not count as SCL interference, if the module detects that a target device has held SCL low and stretched the any given SCL cycle for more than [`TIMEOUT_CTRL.VAL`](registers.md#timeout_ctrl) clock ticks this will cause the stretch timeout interrupt to be asserted.
This interrupt is suppressed, however, if [`TIMEOUT_CTRL.EN`](registers.md#timeout_ctrl) is deasserted low.

```wavejson
{signal: [
  {name: 'Clock', wave: 'p............'},
  {name: 'SCL Host Driver', wave: '0..z.......x.'},
  {name: 'SCL Target Driver', wave: 'z0...........'},
  {name: 'SCL bus', wave: '0............'},
  {name: 'TIMEOUT_CNTRL.VAL', wave: '2............', data: "8"},
  {name: 'SCL timeout counter', wave: '2...22222222x', data: '0 1 2 3 4 5 6 7 8'},
  {name: 'TIMEOUT_CNTRL.EN', wave: '1............'},
  {name: 'scl_timeout', wave: '0..........1.'},
],
  head: {text: 'SCL Timeout Example',tick:-3}}
```

Except for START and STOP symbols, the I2C specification requires that the SDA signal remains constant whenever SCL is high.
The `sda_unstable` interrupt is asserted if, when receiving data or acknowledgement pulse, the value of the SDA signal does not remain constant over the duration of the SCL pulse.

Transactions are terminated by a STOP signal.
The host may send a repeated START signal instead of a STOP, which also terminates the preceding transaction.
In both cases, the `cmd_complete` interrupt is asserted, in the beginning of a repeated START or at the end of a STOP.


#### Target Mode

The interrupt `cmd_complete` is asserted whenever a RESTART or a STOP bit is observed by the target.

The interrupt `tx_stretch` is asserted whenever target intends to transmit data but cannot.
See [stretching during read]({{< relref "#stretching-during-read" >}}).

When a host receives enough data from a target, it usually signals the end of the transaction by sending a NACK followed by a STOP or a repeated START.
In a case when a target receives a STOP without the prerequisite NACK, the interrupt `unexp_stop` is asserted.
This interrupt just means that a STOP was unexpectedly observed during a host read.
It is not necessarily harmful, but software can be made aware just in case.

If ACQ FIFO becomes full, the interrupt `acq_full` is asserted.

If a host ceases to send SCL pulses at any point during an ongoing transaction, the target waits for a specified time period and then asserts the interrupt `host_timeout`.
Host sending an address and R/W bit to all target devices, writing to the selected target, or reading from the target are examples of ongoing transactions.
The time period is counted from the last low-to-high SCL transition.
Firmware can configure the timeout value via the register [`HOST_TIMEOUT_CTRL`](registers.md#host_timeout_ctrl).

### Implementation Details: Format Flag Parsing

To illustrate the behavior induced by various flags added to the formatting queue, the following figure shows a simplified version of the `I2C_Host` state machine.
In this simplified view, many sequential states have been collapsed into four sub-sequences of states (shown in square brackets) or have their names abbreviated:
- Issue start
- Issue stop
- Transmit Byte
- Read Bytes

Within each of these sub-sequences, state transitions depend only on the SDA/SCL inputs or internal timers.
Each sub-sequence has a terminal event--generically labeled "[completed]" which prompts the transition to another sequence or state.

However, all transitions which are dependent on formatting flags are shown explicitly in this figure.

![](../doc/I2C_state_diagram.svg)

Similarly, the figure below shows a simplified version of the `I2C_Target` state machine.

![](../doc/I2C_state_diagram_target.svg)

In this diagram, "R/W" stands for a R/W bit value. The host is reading when R/W bit is "1" and writing when R/W bit is "0".
