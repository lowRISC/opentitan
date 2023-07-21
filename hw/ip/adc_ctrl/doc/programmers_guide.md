# Programmer's Guide

## Initialization

The controller should be initialized with the properties of the ADC and scan times.
* The ADC power up delay must be set in [`adc_pd_ctl.pwrup_time`](registers.md#adc_pd_ctl).
* The time to delay between samples in a slow scan should be set in [`adc_pd_ctl.wakeup_time`](registers.md#adc_pd_ctl).
* The number of samples to cause transition from slow to fast scan should be set in [`adc_lp_sample_ctl`](registers.md#adc_lp_sample_ctl).
* The number of samples for debounce should be set in [`adc_sample_ctl`](registers.md#adc_sample_ctl).
* The filter registers [`adc_chnX_filter_ctlN`](registers.md#adc_chn0_filter_ctl) should be programmed.
* The interrupt [`adc_intr_ctl`](registers.md#adc_intr_ctl) and wakeup [`adc_wakeup_ctl`](registers.md#adc_wakeup_ctl) enables should be configured.
* All ones should be written to [`adc_intr_status`](registers.md#adc_intr_status) and  [`filter_status`](registers.md#filter_status) to ensure there are no spurious pending triggers.
* Optionally, the low-power mode should be set in [`adc_pd_ctl.lp_mode`](registers.md#adc_pd_ctl) if the system is going to the low-power mode.
* The state machine will only start running when [`adc_en_ctl`](registers.md#adc_en_ctl) is set.

## Running in normal mode

If fast sampling is always required then the [`adc_pd_ctl.lp_mode`](registers.md#adc_pd_ctl) bit should be clear.
In this case the values in the [`adc_lp_sample_ctl`](registers.md#adc_lp_sample_ctl) are not used.
The ADC will always be enabled and consuming power.

If power saving is required then the controller can be set to operate in low power mode by setting [`adc_pd_ctl.lp_mode`](registers.md#adc_pd_ctl).
The [`adc_lp_sample_ctl`](registers.md#adc_lp_sample_ctl) must be programmed prior to setting this bit.

## Running with the rest of the chip in sleep

Once programmed the controller and ADC can run when the rest of the chip is in low power state and the main clocks are stopped.
This allows the chip to be woken when appropriate values are detected on the two ADC channels.
The fast sampling mode can be used but will usually consume more power than desired when the chip is in sleep.
So it is expected that [`adc_lp_sample_ctl`](registers.md#adc_lp_sample_ctl) is configured and low power mode enabled by setting [`adc_pd_ctl.lp_mode`](registers.md#adc_pd_ctl) prior to the sleep being initiated.

If the ADC wakeup is not required then the controller and ADC should both be disabled by clearing [`adc_en_ctl`](registers.md#adc_en_ctl) prior to the sleep being initiated.

## Use Case

While the ADC controller is meant to be used generically, it can be configured to satisfy more complex use cases.
As an illustrative example, the programmers guide uses the [Chrome OS Hardware Debug](https://chromium.googlesource.com/chromiumos/third_party/hdctools/+/HEAD/docs/ccd.md) as an example of how the ADC controller can be used.

The debug setup referred to uses a USB-C debug accessory.
This insertion of this debug accessory into a system, can be detected by the ADC controller.

The debug accessory voltage range of interest is shown in the diagram below:
![Debug Cable Regions](../doc/debug_cable_regions.svg)

The ADC can be used to detect debug cable connection / disconnection in the non-overlapping regions.
As an example use case of the two channel filters they can be used for detection of a USB-C debug accessory.
The ADC must meet some minimum specifications:
* Full scale range is 0.0V to 2.2V
* If the signal is below 0.0V the ADC value will be zero.
* If the signal is above 2.2V the ADC value will be maximum (i.e. same as 2.2V)
* Absolute maximum error +/- 15 mV in the 0.25 - 0.45 V range
* Absolute maximum error +/- 30 mV in the rest of the 0.0 - 2.2 V range

The following assumes:
* The slow clock runs at 200kHz or 5 us.
* The ADC requires 30 us to power on.
* The ADC takes a single sample in 44 clocks (220 us)

The controller should be initialized with the properties of the ADC and scan times.
* The ADC power up delay must be set in [`adc_pd_ctl.pwrup_time`](registers.md#adc_pd_ctl) to `6` (30 us).
* The time to delay between samples in a slow scan should be set in [`adc_pd_ctl.wakeup_time`](registers.md#adc_pd_ctl) to `1600` (8ms).
* The number of samples to cause transition from slow to fast scan should be set in [`adc_lp_sample_ctl`](registers.md#adc_lp_sample_ctl) to `4` (causing slow scan to be 4*8ms = 32ms of debounce time).
* The number of samples for debounce should be set in [`adc_sample_ctl`](registers.md#adc_sample_ctl) to `155` (causing the total debounce time to be 32ms (slow scan) + 220us * 2 * 155 = 100ms, at the low end of the USB-C spec window).

* For the 10-bit ADC granularity, the filter registers [`adc_chnX_filter_ctlN`](registers.md#adc_chn0_filter_ctl) should be programmed to:

| Filter | Ch0 Min      | Ch0 Max      | Ch1 Min      | Ch1 Max      | Device connected            |
|--------|--------------|--------------|--------------|--------------|-----------------------------|
| 0 IN   |  149 (0.32V) |  279 (0.60V) |  149 (0.32V) |  279 (0.60V) | Debug Sink (local RpUSB)    |
| 1 IN   |  391 (0.84V) |  524 (1.125V)|  391 (0.84V) |  524 (1.125V)| Debug Sink (local Rp1.5A)   |
| 2 IN   |  712 (1.53V) |  931 (2.00V) |  712 (1.53V) |  931 (2.00V) | Debug Sink (local Rp3A)     |
| 3 IN   |  712 (1.53V) |  847 (1.82V) |  405 (0.87V) |  503 (1.08V) | Debug Source with RpUSB     |
| 4 IN   |  349 (0.75V) |  512 (1.12V) |  186 (0.40V) |  279 (0.60V) | Debug Source with Rp1.5A    |
| 5 IN   |  405 (0.87V) |  503 (1.08V) |  712 (1.53V) |  841 (1.82V) | Debug Source RpUSB Flipped  |
| 6 IN   |  186 (0.40V) |  279 (0.60V) |  349 (0.75V) |  521 (1.12V) | Debug Source Rp1.5A Flipped |
| 7 OUT  |  116 (0.25V) |  954 (2.05V) |  116 (0.25V) |  954 (2.05V) | Disconnect                  |


* The interrupt [`adc_intr_ctl`](registers.md#adc_intr_ctl) and wakeup [`adc_wakeup_ctl`](registers.md#adc_wakeup_ctl) enables should be configured.
* All ones should be written to [`adc_intr_status`](registers.md#adc_intr_status) and  [`filter_status`](registers.md#filter_status) to ensure there are no spurious pending triggers.
* The state machine will only start running when [`adc_en_ctl`](registers.md#adc_en_ctl) is set.

Note that for the debug controller (DTS in USB-C specification) as a power source the filter that is hit will indicate the orientation of the connector.
If the debug controller is acting as a power sink then the orientation cannot be known unless the debug controller supports the optional behavior of converting one of its pulldowns to an Ra (rather than Rp) to indicate CC2 (the CC that is not used for communication).
This would not be detected by the filters since it happens later than connection detection and debounce in the USB-C protocol state machine, but could be detected by monitoring the current ADC value.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_adc_ctrl.h)
