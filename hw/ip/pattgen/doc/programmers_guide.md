# Programmer's Guide

To start pattern generation, the register interface of the pattern generator HWIP should be properly initialized and configured.

The guide that follows provides instructions for configuring Channel 0.
To configure Channel 1, use the registers with the "CH1" suffix, instead of the "CH0" registers.

To configure a single channel:
1. Before configuration, disable the desired channel by clearing the enable bit, [`CTRL.ENABLE_CH0`](registers.md#ctrl).
1. Set the polarity bit, [`CTRL.POLARITY_CH0`](registers.md#ctrl), to determine the desired clock phase.
For either channel, a zero in the polarity bit indicates that the channel clock line (`pcl`) should start low, and the channel data line `pda` transitions on every falling edge of `pcl`.
A one in the polarity bit inverts the `pcl` clock so that it starts high and `pda` transitions on the rising edge.
The following waveform illustrates the effect of the `POLARITY` bit.
Here both channels are configured for simultaneous pattern generation, but the two channels are configured for opposite polarity.
```wavejson
{signal: [
  {name: 'CTRL.ENABLE_CH0', wave: 'lh......'},
  {name: 'CTRL.POLARITY_CH0 (default: low)', wave: '0.......'},
  {name: 'pcl0_tx', wave: '0.hlhlhl'},
  {name: 'pda0_tx', wave: 'x3.3.3.3', data: 'DATA[0] DATA[1] DATA[2]'},
  {name: 'CTRL.POLARITY_CH1 (high)', wave: '1.......'},
  {name: 'pcl1_tx', wave: '1.lhlhlh'},
  {name: 'pda1_tx', wave: 'x5.5.5.5', data: 'DATA[0] DATA[1] DATA[2]'},
],
  head: {text: 'Effect of the Polarity Registers',tick:0}}
```

1. Program the length of seed pattern using the length field, [`SIZE.LEN_CH0`](registers.md#size).
Note that since the allowed seed length ranges from 1-64, the value of this field should be one less than the pattern length.
For example, to generate an 16-bit pattern, a value of 15 should be written to the field [`SIZE.LEN_CH0`](registers.md#size).
1. Program the seed pattern (between 1 and 64 bits in length) using the multi-register [`DATA_CH0_0`](registers.md#data_ch0) and [`DATA_CH0_1`](registers.md#data_ch0).
The first 32 bits to be transmitted, are programmed in the lower half of the multi-register (i.e. [`DATA_CH0_0`](registers.md#data_ch0)), and the latter 32 bits are programmed in the upper half of the multi-register (i.e. [`DATA_CH0_1`](registers.md#data_ch0)).
1. Program the clock divider ratio using the register [`PREDIV_CH0.CLK_RATIO`](registers.md#prediv_ch0).
The resulting clock frequency will be slower than the input I/O clock by a ratio of 2&times;(CLK_RATIO+1):
$$f_{pclx}=\frac{f_\textrm{I/O clk}}{2(\textrm{CLK_RATIO}+1)}$$
1. Program the desired number of pattern repetitions using the repetition field [`SIZE.REPS_CH0`](registers.md#size).
Note that since the allowed number of pattern repetitions ranges from 1-1024, the value of this field should be one less than the desired repetition count.
For example, to repeat a pattern 30, a value of 29 should written to the field [`SIZE.REPS_CH0`](registers.md#size).
1. Finally to start the pattern, set the [`CTRL.ENABLE_CH0`](registers.md#ctrl).
To start both channel patterns at the same time, configure both channels then simultaneously assert both the [`CTRL.ENABLE_CH0`](registers.md#ctrl) and [`CTRL.ENABLE_CH1`](registers.md#ctrl) bits in the same register access.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_pattgen.h)
