# Pattern Generator HWIP Technical Specification

[`pattgen`](https://reports.opentitan.org/hw/ip/pattgen/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/pattgen/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/pattgen/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/pattgen/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/pattgen/code.svg)

# Overview

The pattern generator (`pattgen`) is designed to create configurable output patterns.
The module is controlled through a register interface and raises an interrupt when a pattern completes.
As a peripheral on the system bus, it follows the [Comportability Specification](../../../doc/contributing/hw/comportability/README.md).

## Features

There is more detailed description about the features below, but the headlines are:

- Generates time-dependent patterns on two channels, each with its own clock.
- Each channel has a 1-bit data output (`pda`) and its own clock signal (`pcl`).
- The channels can operate independently or synchronously with each other.
- The pattern data on a channel can use a pattern of up to 64 bits.
- This pattern can be repeated up to 1024 times.
- Each channel's clock can be divided by a 32-bit pre-divider.
- The polarity of each channel's clock signal is programmable.
- The block sends an interrupt for each channel when that channel completes a pattern.

## Description

The pattern generator HWIP transmits short (maximum 64 bits) time-dependent data patterns on two clock-parallel channels.
Each channel consists of one clock (`pcl`) and one data (`pda`) line.
The output channels may be activated and operated independently, or they can be started at the same time to effectively create a 4-output pattern.

## Channels

The current `pattgen` implementation is designed to support two channels.
Each channel can run independently, started with the [`CTRL`](doc/registers.md#ctrl) register.
Because the "enable" fields for the different channels are both in the same register, two channels may be started synchronously.

## Patterns

Each channel can send a pattern of up to 64 bits.
The pattern is configured by writing its bits to a multi-register for the channel.
For channel zero, this is [`DATA_CH0`](doc/registers.md#data_ch0).
These bits are presented on the output `pda` signal.
The multiregister is serialized starting with the register with the lowest index (e.g. `DATA_CH0_0`) and each register is sent LSB-first.

A pattern can be repeated, up to 1024 times.
There are no gaps between repeats: the MSB of a pattern is immediately followed by its LSB again.

The length and repeat count of a pattern are configured by fields in the [`SIZE`](doc/registers.md#size) register.
In both cases, the value in the register is one less than the length or count.
For example, a repeat count of 0 means that the pattern should be sent once.
A repeat count of `10'h3ff` means the patter should be sent 1024 times.

## Polarity

Each channel is transmitted with two signals (`pcl` and `pda`).
The data signal is synchronous with the clock, the polarity of this can be configured.
This is done with fields (`POLARITY_CH0`, `POLARITY_CH1`) in the [`CTRL`](doc/registers.md#ctrl) register.
A value of zero means that `pda` will change on the falling edge of `pcl`.

## Pre-divider

Each channel has a pre-divider, configured by [`PREDIV_CH0`](doc/registers.md#prediv-ch0), .[`PREDIV_CH1`](doc/registers.md#prediv-ch1).
The `pattgen_chan` module counts up to the value of the pre-divider each time it inverts the `pcl` value.
As such, if the pre-divider has value `N` then `pcl` will have a period of `2*N` cycles.
The count is configured a bit like the length and repeat count mentioned [above](#patterns).
A field value of zero means that the pre-divider counts to zero and alternates every cycle.
This gives a `pcl` frequency of half the main clock frequency.
In pictures, this is the behaviour:
```wavejson
{
  signal: [
    {name: 'clk',            wave: '10101010101010101010'},
    {name: 'pcl with div=0', wave: '1.0.1.0.1.0.1.0.1.0.'},
    {name: 'pcl with div=1', wave: '1...0...1...0...1...'},
    {name: 'pcl with div=2', wave: '1.....0.....1.....0.'},
    {name: 'pcl with div=3', wave: '1.......0.......1...'}
  ]
}
```

The pre-divider can be configured to be large (with a maximum value of `1 << 32`).

## Interrupts

When a pattern completes, the associated [interrupt line](doc/interfaces.md#interrupts) (`done_ch0` or `done_ch1`) goes high.

## Inactive level

While a pattern is being transmitted, the exact behaviour of the `pcl` and `pda` outputs is governed by the polarity.
In times when a pattern is not being transmitted, the channel is considered inactive.
At those times, the `pcl` and `pda` outputs are constant, set to a level that can be configured.
This configuration is controlled by single-bit fields in the [`CTRL`](doc/registers.md#ctrl) register.
For channel 0, the fields are `INACTIVE_LEVEL_PCL_CH0` and `INACTIVE_LEVEL_PDA_CH0`.

## Synchronous channels

Although the channels can be configured and enabled separately, their "enable" fields are both in the same register.
As such, a single register write can enable both channels.
This means that they can be run in lock-step, with both clocks toggling synchronously.

## Sensitivity when enabled

Each channel stores a local copy of its control parameters.
These get updated on the posedge of every clock cycle that the channel is not enabled, then stay constant when the channel is enabled.
The only field that has an effect when the channel is enabled is the associated `ENABLE_CH*` field in the [`CTRL`](doc/registers.md#ctrl) register.

## Clean output signals

In order to ensure that the output signals switch cleanly, they are driven straight from flops.
This ensures that they cannot "glitch", no matter how the registers are controlled.

## Alert behaviour

Although `pattgen` is not really a security block, it is still connected to the alert system.
This connection is just that it generates alerts if it detects signal integrity problems on the TileLink bus.
