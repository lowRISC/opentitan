# PWM HWIP Technical Specification

[`pwm`](https://reports.opentitan.org/hw/ip/pwm/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/pwm/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/pwm/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/pwm/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/pwm/code.svg)

# Overview

This document specifies PWM hardware IP (HWIP) functionality.
This module conforms to the [Comportable guideline for peripheral functionality.](../../../doc/contributing/hw/comportability/README.md)
See that document for integration overview within the broader top-level system.

## Features

- Pulse-width modulated (PWM) with adjustable duty cycle
- Suitable for general-purpose use, but primarily designed for control of tri-color LEDs
- Parameterizable number of output channels
- Separate clock domains for TL-UL I/O vs. core operations
   - PWM operation can continue in low-power state.
- Independent control of duty cycle, phase, and polarity for all channels
- Programmable resolution (1 to 16 bits) in adjusting the output duty cycle and phase
- All output channels are driven at the same pulse frequency, which is selected by a 27-bit clock divider
- Hardware-controlled blink feature
   - Blinking channel toggles between two separably programmable duty cycles
   - Blink timing is independently programmable for each channel
- "Heartbeat" blink mode
   - Output duty cycle linearly increments and decrements between two programmable values
   - Step size and step frequency are independently programmable for each channel
- Channels can be configured to blink synchronously or independently
- All duty cycle settings are independently programmable

## Description

The PWM IP is primarily designed to drive a parameterizable number of pulse-width modulated outputs with periodic pulses each with a programmable frequency, phase, and duty cycle (i.e. the ratio between the pulse duration and the overall period between pulses.)

The phase and duty cycle of each output channel can then be controlled with programmable resolution, from 1-bit (half-cycle resolution) to 16-bit (in which case pulse width and timing can be controlled to one part in 2<sup>16</sup> relative to the pulse period)

By default the output pulses are active-high, however the polarity can also be inverted by firmware.

For operation in low-power modes, the PWM IP core runs from a second clock, independent of the TL-UL bus clock.

All outputs are pulsed at a common clock frequency, which can be controlled relative to the PWM core clock by a 27-bit clock divider.
The overall pulse frequency depends on this clock-divider and the phase-resolution.

The primary application is to control tri-color LEDs.
The intensity of each LED channel can be adjusted by varying the duty cycle of the PWM outputs.
The IP provides capabilities for driving a trio of RGB LEDs at any 24-bit RGB-color combination.
It principle, this requires a minimum of 8-bits of programmable duty cycle resolution for each output.
However, the proper mapping of LED duty-cycles to perceived colors will depend on many factors, such as non-linear response function of the chosen LED and the choice of current driver.
Thus the IP provides up to 16-bits of duty cycle resolution, to allow for fine-grain duty cycle control.
The resolution can be also reduced down as low as 1-bit, to allow for more frequent pulses when connected to a low-frequency, low-power bus.

This IP only controls the *timing* of the PWM drive signal.
The drive *current* must be managed by the system designer by including the appropriate off-chip circuitry.
For instance, in the LED-drive use-case, various off-chip solutions exist for controlling the current, such as selection of an appropriate series resistance, or the use of an external fixed-current LED drive IC.
Some limited possibilities for current control may also exist in a top-level ASIC design.
However, such configuration options are outside the scope of this document.

In order to support a variety of drive configurations, the polarity of each channel may be inverted.

The PWM IP is also suitable for driving other outputs, such as servo motors.
In some applications, the user may wish to stagger outputs to limit the overall magnitude of current spikes in the complete system.
Thus each output also has a phase control register, with up to 16-bit resolution.
In security applications it is the system-designer's responsibility to ensure that improper configuration of the phase control registers does not pose a security risk to the overall system (due to, for instance, a denial of service attack through the PWM configuration).

The PWM IP provides a hardware-controlled blink feature, which can periodically toggle the output between two states with separate duty cycles.
This feature can be used to significantly reduce the output duty cycle (blink-off), or, in the case of tri-color LEDs, toggle the apparent LED color between the two settings.
This feature is enabled on a per-channel basis, and for each blinking channel, the blink period and blink duty cycle are programmed in terms of the number of pulses generated in either state.

As a variant of the blink feature, the output duty cycle can also be programmed to linearly increase and decrease in time.
In this "heartbeat" mode, the duty cycle increments by a programmable amount after a programmable number of pulses, starting at some firmware-selected initial duty cycle.
Once the internal duty cycle reaches the target value, the internal duty cycle begins to decrement until it returns to the initial value, at which point the cycle repeats until heartbeat mode is disabled.
