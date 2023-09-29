# Programmer's Guide

## Pad Attributes

Software should determine and program the pad attributes at startup, or reprogram the attributes when the functionality requirements change at runtime.

This can be achieved by writing to the [`MIO_PAD_ATTR_0`](registers.md#mio_pad_attr) and [`DIO_PAD_ATTR_0`](registers.md#dio_pad_attr) registers.
Note that the IO attributes should be configured before enabling muxed IOs going through the `pinmux` matrix in order to avoid undesired electrical behavior and/or contention at the pads.

The pad attributes configuration can be locked down individually for each pad via the [`MIO_PAD_ATTR_REGWEN_0`](registers.md#mio_pad_attr_regwen) and [`DIO_PAD_ATTR_REGWEN_0`](registers.md#dio_pad_attr_regwen) registers.
The configuration can then not be altered anymore until the next system reset.

The following pad attributes are supported by this register layout by default:

ATTR Bits | Description                                   | Access
----------|-----------------------------------------------|---------
0         | Input/output inversion                        | WARL
1         | Virtual open drain enable                     | WARL
2         | Pull enable                                   | WARL
3         | Pull select (0: down, 1: up)                  | WARL
4         | Keeper enable                                 | WARL
5         | Schmitt trigger enable                        | WARL
6         | Open drain enable                             | WARL
8:7       | Slew rate (0x0: slowest, 0x3: fastest)        | WARL
12:9      | Drive strength (0x0: weakest, 0xf: strongest) | WARL

Since some of the pad attributes may not be implemented, SW can probe this capability by writing the CSRs and read them back to determine whether the value was legal.
This behavior is also referred to as "writes-any-reads-legal" or "WARL" in the RISC-V world.
For example, certain pads may only support two drive-strength bits, instead of four.
The unsupported drive-strength bits in the corresponding CSRs would then always read as zero, even if SW attempts to set them to 1.

## Pinmux Configuration

Upon POR, the `pinmux` state is such that all MIO outputs are high-Z, and all MIO peripheral inputs are tied off to 0.
Software should determine and program the `pinmux` mapping at startup, or reprogram it when the functionality requirements change at runtime.
This can be achieved by writing the following values to the [`PERIPH_INSEL_0`](registers.md#periph_insel_0) and [`MIO_OUTSEL_0`](registers.md#mio_outsel) registers.

`periph_insel` Value  | Selected Input Signal
----------------------|-----------------------
0                     | Constant zero (default)
1                     | Constant one
2 + k                 | Corresponding MIO input signal at index k

The global default at reset is `0`, but the default of individual signals can be overridden at design time, if needed.

`mio_outsel` Value    | Selected Output signal
----------------------|-----------------------
0                     | Constant zero (default)
1                     | Constant one
2                     | High-Z
3 + k                 | Corresponding peripheral output signal at index k

The global default at reset is `2`, but the default of individual signals can be overridden at design time, if needed.

Note that the `pinmux` configuration should be sequenced after any IO attribute-specific configuration in the [`MIO_PAD_ATTR_0`](registers.md#mio_pad_attr) and [`DIO_PAD_ATTR_0`](registers.md#dio_pad_attr) registers to avoid any unwanted electric behavior and/or contention.
If needed, each select signal can be individually locked down via [`MIO_PERIPH_INSEL_REGWEN_0`](registers.md#mio_periph_insel_regwen) or [`MIO_OUTSEL_REGWEN_0`](registers.md#mio_outsel_regwen).
The configuration can then not be altered anymore until the next system reset.

## Sleep Features

The sleep behavior of each individual MIO or DIO can be defined via the (registers.md#mio_pad_sleep_en), [`DIO_PAD_SLEEP_EN_0`](registers.md#dio_pad_sleep_en), [`MIO_PAD_SLEEP_MODE_0`](registers.md#mio_pad_sleep_mode) and [`DIO_PAD_SLEEP_MODE_0`](registers.md#dio_pad_sleep_mode)) registers.
Available sleep behaviors are:
`dio/mio_pad_sleep_en` Value  | `dio/mio_pad_sleep_mode` Value | Sleep Behavior
------------------------------|--------------------------------|-----------------------
0                             | -                              | Drive (default)
1                             | 0                              | Tie-low
1                             | 1                              | Tie-high
1                             | 2                              | High-Z
1                             | 3                              | Keep last value

Note that if the behavior is set to "Drive", the sleep mode will not be activated upon sleep entry.
Rather, the retention logic continues to drive the value coming from the peripheral side.
Also note that the sleep logic is located after the `pinmux` matrix, hence the sleep configuration is per MIO pad and not per MIO peripheral.

Before sleep entry, SW should configure the appropriate sleep behavior of all MIOs/DIOs via [`MIO_PAD_SLEEP_MODE_0`](registers.md#mio_pad_sleep_mode), [`DIO_PAD_SLEEP_MODE_0`](registers.md#dio_pad_sleep_mode).
This configuration can be optionally locked down, in which case it cannot be modified again until POR.
The configured behavior is then activated for all pads that have sleep mode set to enabled (registers.md#mio_pad_sleep_en) and [`DIO_PAD_SLEEP_EN_0`](registers.md#dio_pad_sleep_en)) at once by the power manager during the sleep entry sequence.

When exiting sleep, the task of disabling the sleep behavior is however up to SW.
I.e., it must clear the per-pad sleep status bits in registers [`MIO_PAD_SLEEP_STATUS_0`](registers.md#mio_pad_sleep_status) and [`DIO_PAD_SLEEP_STATUS_0`](registers.md#dio_pad_sleep_status) that have been set upon sleep entry.
The rationale for this is that it may not be desirable to disable sleep behavior on all pads at once due to some additional book keeping / re-initialization that needs to be performed while exiting sleep.

## Wakeup Features

The `pinmux` contains eight wakeup detectors.
These detectors can be individually enabled and disabled regardless of the sleep state.
This ensures that SW can set them up before and disable them after sleep in order to ensure that no events are missed during sleep entry and exit.

For more information on the patterns supported by the wakeup detectors, see [wakeup detectors](theory_of_operation.md#wakeup-detectors).

A typical programming sequence for the wakeup detectors looks as follows:

1. Before initiating any sleep mode, SW should configure the wakeup detectors appropriately and enable them via the [`WKUP_DETECTOR_0`](registers.md#wkup_detector), [`WKUP_DETECTOR_CNT_TH_0`](registers.md#wkup_detector_cnt_th) and [`WKUP_DETECTOR_PADSEL_0`](registers.md#wkup_detector_padsel) registers.

2. Optionally, lock the wakeup detector configuration via the [`WKUP_DETECTOR_REGWEN_0`](registers.md#wkup_detector_regwen) registers.

3. During sleep, the wakeup detectors will trigger a wakeup request if a matching pattern has been observed.
   A bit corresponding to the wakeup detector that has observed the pattern will be set in the [`WKUP_CAUSE`](registers.md#wkup_cause) register.

4. When exiting sleep, SW should read the wake info register in the [power manager](../../../top_earlgrey/ip_autogen/pwrmgr/README.md) to determine the reason(s) for the wakeup request.

5. If the wakeup request was due to a pin wakeup pattern detector, SW should inspect the [`WKUP_CAUSE`](registers.md#wkup_cause) registers in order to determine the exact cause.

6. SW should in any case disable the wakeup detectors and clear the [`WKUP_CAUSE`](registers.md#wkup_cause) registers once it is safe to do so (in order to not miss any events).
   Note that the [`WKUP_CAUSE`](registers.md#wkup_cause) registers reside in the slow AON clock domain, and hence clearing them takes a few uS to take effect.
   If needed, a SW readback can be performed to ensure that the clear operation has completed successfully.

## Pinout and Pinmux Mapping

The tables below summarize the pinout and pinmux connectivity for certain top-level designs.

### Top Earlgrey

{{#include ../../../top_earlgrey/ip/pinmux/doc/autogen/targets.md}}

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_pinmux.h)
