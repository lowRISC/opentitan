# Theory of Operation

## Block Diagram

The diagram below shows how `sensor control` helps `analog sensor top` integration into the overall design.

## Recoverable and Fatal Alerts

The `analog sensor top` sends alert requests in independent, differential form to the `sensor control`.
Each alert request consists of a pair of signals, one active high and one active low.
The active polarity of each signal is independent, due to the imprecise sensor timing that drives the alert.
This means that the `sensor control` recognizes an active alert as long as one of the lines is active, and not the pair of signals being in a particular state.
Each signal in the differential pair is thus a separate dedicated alert indicator.

Once an alert request is detected as active, the `sensor control` formulates a proper alert event through the `prim_alert_sender` and sends a notification to the `alert handler`.

The `sensor control` can optionally generate alert acknowledgements back to the `analog sensor top`.

For each incoming alert, it can be programmed as fatal or recoverable through [`FATAL_ALERT_EN`](../data/sensor_ctrl.hjson#fatal_alert_en).
If set to recoverable, an alert will be registered in [`RECOV_ALERT`](../data/sensor_ctrl.hjson#recov_alert) and the original `analog sensor top` event acknowledged.
The acknowledgement prevents alerts from constantly being sent.

If set to fatal, an alert will be registered in [`FATAL_ALERT`](../data/sensor_ctrl.hjson#fatal_alert) but the original `analog sensor top` event will not be acknowledged.
This causes the alert to constantly send until the system escalates in some form.

## Wakeup Requests

In addition to forwarding events to the `alert handler`, incoming events can also be aggregated into a wakeup request to the system.
The `sensor control` does not make assumptions about its power domains and thus it is up to the integrating system to decide which power modes allow alert event wakeups.

As an example, if the `sensor control` is not placed in an always on domain, then it cannot send alert based wakeups if the system is in a deep low power state.
It will only be able to send wakeups when the system is powered and the `clk_aon_i` input is available.

## Hardware Interfaces

### Signals

* [Interface Tables](../data/sensor_ctrl.hjson#interfaces)
