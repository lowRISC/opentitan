# Programmer's Guide

Each available alert has a corresponding fatality configuration.
If an alert event is set to 1 in [`FATAL_ALERT_EN`](registers.md#fatal_alert_en), `sensor control` treats it as a fatal event instead of a recoverable event.
Fatal events are not acknowledged, and continuously send alert events in the system until some kind of escalation is seen.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../../sw/device/lib/dif/dif_sensor_ctrl.h)
