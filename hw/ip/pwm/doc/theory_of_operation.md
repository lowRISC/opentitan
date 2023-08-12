# Theory of Operation

## Block Diagram

![](../doc/pwm_block_diagram.svg)

## Design Details

### Phase and Duty Cycle Representation

The PWM IP creates series of pulses with the desired on-off duty cycle.
The duty cycle, DC, is typically expressed a fraction of pulse duration, <i>d</i>, over the period between pulses, <i>T</i>:

$$DC\equiv d/T.$$

Since 0&lt;<i>d</i>&lt;<i>T</i>, the duty cycle ranges from 0 to 1.

The PWM IP can control the duty cycle in a number of ways:
- The PWM can be programmed to generate pulses at a firmware-defined duty cycle.
- The duty cycle can be programmed to toggle (or "blink") between two duty cycles at a programmable rate.
In the tri-color LED use-case, this would have the visual effect of making the LED blink between two colors.
- The duty cycle can linearly sweep in time, gradually shifting back-and-forth between two endpoints.

Thus the duty cycle can be controlled by firmware, or may change under hardware control.
The operation of each of these modes will be discussed later.

Each channel can also be assigned a different phase delay.
Like the duty cycle, this delay is expressed as a fraction of the pulse period, <i>T</i>.
The phase delay of each channel is always directly controlled by a firmware register value.

Since the phase and duty cycle are always a fraction less than or equal to one, the PWM IP represents them as 16-bit fixed point numbers, with an implicit 16-bit shift.
If the duty cycle is internally represented as a 16-bit value x, the output pulse train will have the duty cycle:

$$DC(x)=\frac{x}{2^{16}}.$$

Thus the allowed duty cycle in principle ranges from 0 to 99.998% (i.e. <nobr>1-(&frac12;)<sup>16</sup></nobr>).

However, the actual phase resolution may be smaller.
In order to support faster pulse rates, the phase resolution can be set to less than 16-bits, in which case the observed duty cycle will be rounded down to the next lowest multiple of <nobr>2<sup>-([`CFG.DC_RESN`](registers.md#cfg)+1)</sup></nobr>.
In other words, the [`CFG.DC_RESN`](registers.md#cfg) register effectively limits the duty cycle resolution, such that only the <nobr>[`CFG.DC_RESN`](registers.md#cfg)+1</nobr> most significant bits are relevant:

$$DC(x; \textrm{DC_RESN})=\frac{\textrm{MSB}(x; \textrm{DC_RESN}+1)}{2^{(\textrm{DC_RESN}+1)}},$$

where here we use the notation MSB(<i>x</i>; <i>y</i>), to mean the <i>y</i> most significant bits of the binary value <i>x</i>.

### PWM Phase Counter

The IP maintains a single phase counter that is shared by all outputs.
As we discuss in the next section, each channel has a comparator which compares these values to the current duty cycle and phase value and generates the appropriate pulse.
Since all phase or duty cycle related quantities are represented as 16-bit fixed point fractions-regardless of whether they are calculated by the PWM IP or determined by firmware-the phase counter is also a 16-bit quantity.

Each PWM pulse cycle is divided into <nobr>2<sup>DC_RESN+1</sup></nobr> beats.
During each beat, the 16-bit phase counter increments by 2<sup>(16-DC_RESN-1)</sup> (modulo 65536).
The beat period is defined by the [`CFG.CLK_DIV`](registers.md#cfg) register:

$$f_\textrm{beat}=\frac{f_\textrm{core clk}}{\textrm{CLK_DIV}+1}$$

A PWM pulse cycle is completed each time the phase counter overflows to 0.
The PWM drive frequency is therefore:
$$f_\textrm{PWM}=f_\textrm{beat}\frac{2^{16-\textrm{DC_RESN}-1}}{2^{16}}=\frac{f_\textrm{core clk}}{2^{\textrm{DC_RESN}+1}(\textrm{CLK_DIV}+1)}$$

The PWM phase counter is reset whenever [`CFG.CNTR_EN`](registers.md#cfg) is disabled.

The following figure illustrates the effect of the clock divider register.  Note that changes to [`CFG.CLK_DIV`](registers.md#cfg) or [`CFG.DC_RESN`](registers.md#cfg) only take effect when [`CFG.CNTR_EN`](registers.md#cfg) is disabled.

```wavejson
{signal: [
  {name: 'core_clk_i', wave: 'p..............|..........'},
  {name: 'sync(CFG.CNTR_EN)', wave: '0.1............|01........'},
  {name: 'sync(CFG.CLK_DIV)', wave: '2....4.........|..2.......', data: '2 4 4'},
  {name: 'clk_div_int', wave: 'x..2...........|..2.......', data: '2 4'},
  {name: 'sync(CFG.DC_RESN)', wave: '2..............|..........', data: '10d'},
  {name: 'dc_resn_int', wave: 'x..2...........|..........', data: '10d'},
  {name: 'phase_ctr', wave: '3..2..2..2..2..|3.2....2..', data: '0x00 0x00 0x20 0x40 0x80 0 0x00 0x20'},
  {name: 'clk_div_ctr', wave: '2...22222222222|2..2222222', data: '0 1 2 0 1 2 0 1 2 0 1 2 0 1 2 3 4 0 1 2'},
  {name: 'beat_end', wave: '0....10.10.10.1|0.....10..'}],
  config:{skin:'narrow'}
}
```

### PWM Comparators and Pulse Generation.

Whenever the phase counter loops back to zero, this marks the start of a new <i>pulse cycle</i>.
This section describes how the comparator creates pulses with the correct duty cycle and phase.

In the following sections, this document describes the various per-channel configuration options of this IP.
For concreteness, the text discusses the operation of channel 0, using registers and fields ending with "_0".
To operate other channels, simply choose the registers with the appropriate channel suffix.

Clearing [`PWM_EN.EN_0`](registers.md#pwm_en) disables the channel, suppressing all output pulses.

The pulse phase delay is always programmed by firmware into the TL-UL register [`PWM_PARAM_0.PHASE_DELAY_0`](registers.md#pwm_param).
The duty cycle however comes from the blink control hardware (which is described in the next section).
The current duty cycle is stored in a channel-specific signal register, `duty_cycle`.

When operating at full resolution (i.e. `DC_RESN`==15), the channel output rises when the phase counter equals [`PWM_PARAM_0.PHASE_DELAY_0`](registers.md#pwm_param), and falls when the phase counter equals [`PWM_PARAM_0.PHASE_DELAY_0`](registers.md#pwm_param) + `duty_cycle` (mod 2<sup>(`DC_RESN`+1)</sup>).
In both cases, the transition occurs at the beginning of the beat.
When operating at lower resolution the same comparison applies, but using only the most significant (`DC_RESN`+1) bits.

If the combination of phase delay and duty cycle is larger than one pulse cycle, the pulse will start in one pulse cycle and end in the next.
In this case the comparator output will be high at the beginning of each cycle, as seen in the example waveform below.

By default the pulses are all active-high, meaning the output is low if a PWM channel is disabled.
However, to support various drive schemes, the polarity can be inverted on a channel-by-channel basis using the [`INVERT`](registers.md#invert) register.

The following figure illustrates the effect of the [`PWM_PARAM_0.PHASE_DELAY_0`](registers.md#pwm_param) register and `duty_cycle`.
Note that this figure shows two channels, 0 and 1, where the second channel has a significant phase delay, such that the output pulse is high when `phase_ctr` overflows to zero.

```wavejson
{signal: [
  {name: 'core_clk_i', wave: 'p.....|....|......'},
  {name: 'CFG.CLK_DIV', wave: '2.....|....|......', data: '0'},
  {name: 'sync(CFG.CNTR_EN)', wave: '01....|....|......'},
  {name: 'CFG.DC_RESN', wave: '2.....|....|......', data: '3'},
  {name: 'INVERT.INVERT_0', wave: '0.....|....|......'},
  {name: 'phase_ctr[15:12]', wave: '3.2222|2222|222222', data: ['0', '0', '1', '2', '', '7', '8', '9', '10    ', '14', '15' ,'0', '1', '2', '3', '4']},
  {name: 'cycle_end', wave: '0.....|....|.10...'},
  {name: 'PHASE_DELAY_0[15:12]', wave: '2.....|....|......', data: '0'},
  {name: 'pulse_gen[0].duty_cycle[15:12]', wave: '2.....|....|......', data: '9'},
  {name: 'pwm_out_d[0]', wave: '0.1...|..0.|..1...'},
  {name: 'pwm_out_q[0]', wave: '0..1..|...0|...1..'},
  {name: 'PHASE_DELAY_1[15:12]', wave: '2.....|....|......', data: '15'},
  {name: 'pulse_gen[1].duty_cycle[15:12]', wave: '2.....|....|......', data: '3'},
  {name: 'pwm_out_d[1]', wave: '0.1.0.|....|.1..0.'},
  {name: 'pwm_out_q[1]', wave: '0..1.0|....|..1..0'}
  ],
 config:{skin:'narrow'}
}
```

Changes to [`PWM_EN.EN_0`](registers.md#pwm_en) bit have no effect on the *timing* of the pulses, as the `phase_ctr` is common to all channels.
Enabling [`PWM_EN.EN_0`](registers.md#pwm_en), or changing [`PWM_PARAM_0.PHASE_DELAY_0`](registers.md#pwm_param) is acceptable while the PWM channel is enabled.
Since these registers take effect immediately, the shape of the following pulse may be unpredictable if they are changed while [`CFG.CNTR_EN`](registers.md#cfg) is active, though this glitch in a single pulse is likely not a problem for most applications.
Changes to the duty cycle register [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle) may also be effective immediately, but only *when blinking is disabled*.

In the above waveform, the first beat (labeled "0") does not start for one clock after [`CFG.CNTR_EN`](registers.md#cfg) is asserted.
This delay is typical, and reflects the fact that it takes exactly one clock cycle for the phase counter to start (as seen in the previous waveform).

There is a register `pwm_out` at the output pin, which adds an additional delay cycle before the output pin.
Thus, in addition to delay of the clock domain crossing, there is in total a minimum two clock delay between the assertion of [`CFG.CNTR_EN`](registers.md#cfg) and the rising edge of the first output pulse.

### Hardware-Controlled Blink Features

By default, the duty cycle of each channel is directly controlled by firmware, by writing the desired PWM duty cycle to the [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle) register.

There are two other modes which allow for programmably-timed duty cycle modulations, under hardware control.
- In the standard blink mode the duty cycle toggles between two values, [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle) and [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle).
- In heartbeat mode, the duty cycle linearly transitions from [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle) to [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle) and back, via a regularly-timed sequence of duty cycle increments or decrements.

In both modes the timing and control of the blinking or transition is controlled by the register fields [`BLINK_PARAM_0.X_0`](registers.md#blink_param) and [`BLINK_PARAM_0.Y_0`](registers.md#blink_param).
However in either mode, the interpretation of these fields is different.

Note that changes to the [`BLINK_PARAM_0`](registers.md#blink_param) register or to the register field [`PWM_PARAM_0.HTBT_EN_0`](registers.md#pwm_param) only take effect when the [`PWM_PARAM_0.BLINK_EN_0`](registers.md#pwm_param) is deasserted.
Both of the blink modes make use of a 16-bit internal blink counter (one per channel).
This counter is reset whenever [`PWM_PARAM_0.BLINK_EN_0`](registers.md#pwm_param) is cleared.
In other words, changing the blink behavior requires first halting the blink pattern, and the pattern starts from the beginning whenever the blink enable bit is reasserted.

#### Standard Blink Mode

To enter standard blink mode, assert [`PWM_PARAM_0.BLINK_EN_0`](registers.md#pwm_param), while leaving [`PWM_PARAM_0.HTBT_EN_0`](registers.md#pwm_param) deasserted.

In standard blink mode, the duty cycle abruptly alternates between two values: [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle) and [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle).
The sequence starts with [`BLINK_PARAM_0.X_0`](registers.md#blink_param)+1 pulses at [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle), followed by [`BLINK_PARAM_0.Y_0`](registers.md#blink_param)+1 pulses at [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle), after which the cycle repeats until blink mode is disabled.

Typically multiple channels need to be configured to blink synchronously, for example in the tri-color LED case.
This can be achieved by first disabling the desired PWM outputs using the [`PWM_EN`](registers.md#pwm_en) multi-register.
Once the blink parameters have been configured for these channels, they can be simultaneously re-enabled using a single write to [`PWM_EN`](registers.md#pwm_en).

#### Heartbeat Mode

To enter heartbeat mode, assert both [`PWM_PARAM_0.BLINK_EN_0`](registers.md#pwm_param) and [`PWM_PARAM_0.HTBT_EN_0`](registers.md#pwm_param).

In heartbeat mode the duty cycle gradually transitions from [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle) to [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle) and back in a series of small steps.

An example of this process is illustrated in the following waveform.
```wavejson
{signal: [
  {name: 'Pulse Cycle', wave: '2222222222222222222',
   data: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]},
  {name: 'PWM_PARAM.BLINK_EN', wave: '01.................'},
  {name: 'PWM_PARAM.HTBT_EN', wave: '01.................'},
  {name: 'DUTY_CYCLE.A', wave: '2..................', data: '3'},
  {name: 'DUTY_CYCLE.B', wave: '2..................', data: '21'},
  {name: 'BLINK_PARAM.X', wave: '2..................', data: ['1']},
  {name: 'BLINK_PARAM.Y', wave: '2..................', data: ['4']},
  {name: 'duty_cycle', wave: '4.2.2.2.2.2.2.2.2.2', data: [3, 3, 8, 13, 18, 23, 18, 13, 8, 3]}
],
 config:{skin:'narrow'}
}
```

The sequence starts with [`BLINK_PARAM_0.X_0`](registers.md#blink_param)+1 pulses at [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle).
The duty cycle then increases by [`BLINK_PARAM_0.Y_0`](registers.md#blink_param)+1 units, and [`BLINK_PARAM_0.X_0`](registers.md#blink_param)+1 more pulses are generated at the new duty cycle.
The cycle repeats until the `duty cycle`&ge; [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle), at which point the cycle is reversed, decrementing with the same step-size and rate until the duty cycle once again returns to [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle) and the whole process repeats.
(This all assumes that [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle) &gt; [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle).
If [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle) &lt; [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle), the cycle is similar but with all the signs reversed.
For instance, the duty cycle is repeatedly <i>decremented</i> until reaching [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle).)

In the heartbeat process, the duty cycle always starts at [`DUTY_CYCLE_0.A_0`](registers.md#duty_cycle), but it may slightly exceed [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle) on the last step if the step-size does not evenly divide the difference between duty cycles.

The duty cycle is never allowed to overflow or underflow, even if [`DUTY_CYCLE_0.B_0`](registers.md#duty_cycle) is very close to the minimum or maximum 16-bit value.
If needed, the most extreme value in the `duty_cycle` sequence is truncated to stay within the allowable 16-bit range.
All other points in the heartbeat sequence are unaffected by this truncation.
