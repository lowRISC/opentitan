# Alert Handler Technical Specification

[`alert_handler`](https://reports.opentitan.org/hw/top_earlgrey/ip_autogen/alert_handler/dv/latest/report.html):
![](https://dashboards.lowrisc.org/badges/dv/alert_handler/test.svg)
![](https://dashboards.lowrisc.org/badges/dv/alert_handler/passing.svg)
![](https://dashboards.lowrisc.org/badges/dv/alert_handler/functional.svg)
![](https://dashboards.lowrisc.org/badges/dv/alert_handler/code.svg)

# Overview

This document specifies the functionality of the alert handler mechanism.
The alert handler is a module that is a peripheral on the chip interconnect bus, and thus follows the [Comportability Specification](../../../../doc/contributing/hw/comportability/README.md).
It gathers alerts - defined as interrupt-type signals from other peripherals that are designated as potential security threats - throughout the design, and converts them to interrupts that the processor can handle.
If the processor does not handle them, the alert handler mechanism provides hardware responses to handle the threat.


## Features

- Differentially-signaled, asynchronous alert inputs from `NAlerts` peripheral sources, where `NAlerts` is a function of the requirements of the peripherals.

- Ping testing of alert sources:
    - responder module requests periodic alert response from each source to ensure proper wiring.
    - reset-asserted and clock-gated information is used to temporarily pause the ping mechanism on alert channels that are in a low-power state.

- Register locking on all configuration registers.
    - Once locked, can not be modified by software until next system reset.

- Register-based assignment of alert to alert-class.
    - Four classes, can be individually disabled.
    - Each class generates one interrupt.
    - Disambiguation history for software to determine which alert caused the class interrupt.
    - Each class has configurable response time for escalation.
    - Disable allows for ignoring alerts, should only be used in cases when alerts are faulty.
      Undesirable access is enforced by locking the register state after initial configuration.

- Register-based escalation controls.
    - Number of alerts in class before escalation.
    - Timeout for unhandled alert IRQs can also trigger escalation.
    - Configurable escalation enables for 4 escalation signals.
        - Could map to NMI, wipe secrets signal, lower privilege, chip reset, etc.
        - Escalation signals differentially-signaled with heartbeat, will trigger response if differential or heartbeat failure at destination.
    - Configurable time in cycles between each escalation level.

- Two locally sourced hardware alerts.
    - Differential signaling from a source has failed.
    - Ping response from a source has failed.


## Description

The alert handler module manages incoming alerts from throughout the system, classifies them, sends interrupts, and escalates interrupts to hardware responses if the processor does not respond to any interrupts.
The intention is for this module to be a stand-in for security responses in the case where the processor can not handle the security alerts.

It is first notable that all security alerts are rare events.
Module and top level designers should only designate events as alerts if they are expected to never happen, and if they have potential security consequences.
Examples are parity errors (which might indicate an attack), illegal actions on cryptography or security modules, physical sensors of environmental modification (e.g. voltage, temperature), etc.
Alerts will be routed through this module and initially converted to interrupts for the processor to handle.
The expectation is that the secure operating system has a protocol for handling any such alert interrupt in software.
The operating system should respond, then clear the interrupt.
Since these are possible security attacks, the response is not always obvious, but the response is beyond the scope of this document.

This module is designed to help the full chip respond to security threats in the case where the processor is not trusted: either it has been attacked, or is not responding.
It does this by escalating alerts beyond a processor interrupt.
It provides four such escalation signals that can be routed to chip functions for attack responses.
This could include such functions as wiping secret chip material, power down, reset, etc.
It is beyond the scope of this document to specify what those escalation responses are at the chip level.

To ease software management of alerts, classification is provided whereby each alert can be classified into one of four classes.
How the classification is done by software is beyond the scope of this document, but it is suggested that alerts of a similar profile (risk of occurring, level of security concern, frequency of false trigger, etc) are classed together.
For each class a counter of alerts is kept, clearable by software.
If that counter exceeds a programmable maximum value, then the escalation protocol for that class begins.

The details for alert signaling, classification, and escalation are all given in the Theory of Operations section.
