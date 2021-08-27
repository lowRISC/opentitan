---
title: "Sensor Control Technical Specification"
---

# Overview

This document specifies the functionality of the sensor control module.
The sensor control module is a comportable front-end to the [analog sensor top]({{< relref "hw/top_earlgrey/ip/ast/doc" >}}).

It provides basic alert functionality, pad debug hook ups, and a small amount of open source visible status readback.
Long term, this is a module that can be absorbed directly into the `analog sensor top`.

## Features

- Alert hand-shake with `analog sensor top`
- Alert forwarding to `alert handler`
- Status readback for `analog sensor top`
- Pad debug hook up for `analog sensor top`
- Wakeup based on alert events

# Theory of Operations

## Block Diagram

The diagram below shows how `sensor control` helps `analog sensor top` integration into the overall design.

## Recoverable and Fatal Alerts

The `analog sensor top` sends alert requests in independent, differential form to the `sensor control`.
Each alert request consists of a pair of signals, one active high and one active low.
The active polarity of each signal is independent.   This is due to the imprecise timing sensor that drives the alert.
This means that the `sensor control` recognizes an active alert as long as one of the lines is active, and not the pair of signals being in a particular state.
Each signal in the differential pair is thus a separate dedicated alert indicator.

Once an alert request is detected as active, the `sensor control` then formulates a proper alert event through the `prim_alert_sender` and sends a notification to the `alert handler`.

The `sensor control` can optionally generate alert acknowledgements back to the `analog sensor top`.

For each incoming alert, it can be programmed as fatal or recoverable through {{< regref "FATAL_ALERT_EN" >}}.
If set to recoverable, an alert will be registered in {{< regref "RECOV_ALERT" >}} and the original `analog sensor top` event acknowledged.
The acknowledgement prevents alerts from constantly being sent.

If set to fatal, an alert will be registered in {{< regref "FATAL_ALERT" >}} but the original `analog sensor top` event will not be acknowledged.
This causes the alert to constantly send until the system escalates in some form.

## Wakeup Requests

In addition to forwarding events to the `alert handler`, incoming events can also be aggregated into a wakeup request to the system.
The `sensor_ctrl` does not make assumptions about its power domains and thus it is up to the integrating system to decide which power modes allow alert event wakeups.

As an example, if the `sensor_ctrl` is not placed in an always on domain, then it cannot send alert based wakeups if the system is in a deep low power state.
It will only be able to send wakeups when the system is powered and the `clk_aon_i` input is available.

## Hardware Interfaces

### Signals

{{< incGenFromIpDesc "../data/sensor_ctrl.hjson" "hwcfg" >}}

The table below lists other signals.

Signal               | Direction        | Type                                   | Description
---------------------|------------------|----------------------------------------|---------------
`ast_alert_i`        | `input`          | `ast_pkg::ast_alert_req_t`             | Incoming alert requests from `analog sensor top`
`ast_alert_o`        | `output`         | `ast_pkg::ast_alert_rsp_t`             | Outgoing alert acknowledgments to `analog sensor top`
`status_i`           | `input`          | `ast_pkg::ast_status_t`                | Incoming `analog sensor top` status
`ast2pinmux_i`       | `input`          | `logic [ast_pkg::Ast2PadOutWidth-1:0]` | Incoming `analog sensor top` debug output signals
`cio_ast_debug_out`  | `output`         | `logic [ast_pkg::Ast2PadOutWidth-1:0]` | Outgoing `analog sensor top` debug output signals to `pinmux`

# Programmer's Guide

Each available alert has a corresponding acknowledgment control.
Program {{< regref "ACK_MODE.VAL" >}} to the appropriate value for no acknowledgment, software acknowledgment or hardware acknowledgment.

If software acknowledge is selected, {{< regref "ALERT_STATE" >}} can be used to determine the current state of an alert.
When the alert state is cleared (`rw1c`), the `analog sensor top` alert will also be acknowledged.

## Register Table

{{< incGenFromIpDesc "../data/sensor_ctrl.hjson" "registers" >}}
