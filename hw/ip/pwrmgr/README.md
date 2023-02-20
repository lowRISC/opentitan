---
title: "Power Manager HWIP Technical Specification"
---

# Overview

This document specifies the functionality of the OpenTitan power manager.

## Features

- Cold boot, low power entry / exit and reset support.
- 2 different low power modes.
- Software initiated low power entry and hardware requested low power exit.
- Peripheral reset requests
- Low power abort and low power fall-through support.
- ROM integrity check at power-up.
- Local checks for escalator and power stability.

## Description

The power manager sequences power, clocks, and reset resources of the design through cold boot, low power entry/exit and reset scenarios.

Cold boot, also known as POR (power on reset) is the first reset state of the design.
The power manager sequences the design from a freshly reset state to an active state where software can be initialized.

- Low power entry is the process in which the device enters one of two low power modes (sleep or deep sleep).
- Low power exit is the process in which the device exits low power mode and returns to active state.
- Low power entry is always initiated by software, while low power exit is always initiated by a previously setup hardware event such as pins or internal timers.
- The power manager processes the software and hardware requests to perform the appropriate actions.

Reset scenarios refer to non-POR events that cause the device to reboot.
There are various stimuli that can cause such a reset, ranging from external user input to watchdog timeout.
The power manager processes the reset request and brings the device to an appropriate state.


# Theory Of Operation

The power manager performs the following functions:
- Turn on/off power domain(s).
- Control root resets with the reset manager.
- Control root clock enables with AST and clock manager.
- Sequence various power up activities such as OTP sensing, life cycle initiation and releasing software to execute.


## Block Diagram

See the below high level block diagram that illustrates the connections between the power manager and various system components.
Blocks outlined with a solid magenta line are always on; while blocks outlined with a dashed magenta line are a mix of components that are and those that are not.

![Power Manager Connectivity Diagram](pwrmgr_connectivity.svg)

## Hardware Interfaces

{{< incGenFromIpDesc "/hw/top_earlgrey/ip/pwrmgr/data/autogen/pwrmgr.hjson" "hwcfg" >}}

## Overall Sequencing

The power manager contains two state machines.
One operates on the always-on slow clock (this clock is always running and usually measured in KHz) and is responsible for turning faster clocks on and off and managing the power domains.
The other operates on a normal fixed clock (usually measured in MHz) and is responsible for everything else in the power sequence.

The following diagram breaks down the general functionality of both.
The state machines are colored based on their clock domains.
The green state machine is clocked by the normal fixed domain, while the orange state machine is clocked by the slow domain.
Specific request / acknowledge signals are also highlighted in this color scheme to show where the two state machines communicate.

![Power Manager FSMs](pwrmgr_fsms.svg)


Note, most of the states are transitional states, and only the following state combinations are resting states.


*   Slow FSM `Idle` and fast FSM `Active`
*   Slow FSM `Low Power` and fast FSM `Low Power`

The slow FSM `Low Power` and fast FSM `Active` states specifically are concepts useful when examining [reset handling](#reset-request-handling).


## Slow Clock Domain FSM

The slow clock domain FSM (referred to as the slow FSM from here on) resets to the Reset state.
This state is released by `por_rst_n`, which is supplied from the reset controller.
The `por_rst_n` signal is released when the reset controller detects the root power domains (`vcaon_pok` from AST) of the system are ready.
Please see the [ast]({{< relref "hw/top_earlgrey/ip/ast/doc" >}}) for more details.

The slow FSM requests the AST to power up the main domain and high speed clocks.
Once those steps are done, it requests the [fast FSM](#fast-clock-domain-fsm) to begin operation.
The slow FSM also handles power isolation controls as part of this process.

Once the fast FSM acknowledges the power-up completion, the slow FSM transitions to `Idle` and waits for a power down request.
When a power down request is received, the slow FSM turns off AST clocks and power as directed by software configuration.
This means the clocks and power are not always turned off, but are rather controlled by software configurations in {{< regref "CONTROL" >}} prior to low power entry .
Once these steps are complete, the slow FSM transitions to a low power state and awaits a wake request, which can come either as an actual wakeup, or a reset event (for example always on watchdog expiration).

#### Sparse FSM

Since the slow FSM is sparsely encoded, it is possible for the FSM to end up in an undefined state if attacked.
When this occurs, the slow FSM sends an `invalid` indication to the fast FSM and forcibly powers off and clamps everything.

The clocks are kept on however to allow the fast FSM to operate if it is able to receive the `invalid` indication.
The slow FSM does not recover from this state until the system is reset by POR.

Unlike [escalation resets](#escalation-reset-request), the system does not self reset.
Instead the system goes into a terminal non-responsive state where a user or host must directly intervene by toggling the power or asserting an external reset input.

## Fast Clock Domain FSM

The fast clock domain FSM (referred to as fast FSM from here on) resets to `Low Power` state and waits for a power-up request from the slow FSM.

Once received, the fast FSM releases the life cycle reset stage (see [reset controller]({{< relref "hw/ip/rstmgr/doc" >}}) for more details).
This allows the [OTP]({{< relref "hw/ip/otp_ctrl/doc" >}}) to begin sensing.
Once OTP sensing completes , the life cycle controller is initialized.
The initialization of the life cycle controller puts the device into its allowed operating state (see [life cycle controller]({{< relref "hw/ip/lc_ctrl/doc" >}}) for more details).

Once life cycle initialization is done, the fast FSM enables all second level clock gating (see [clock controller]({{< relref "hw/ip/clkmgr/doc" >}}) for more details) and initiates strap sampling.
For more details on what exactly the strap samples, please see [here](https://docs.google.com/spreadsheets/d/1pH8T1MhQ7TXtP_bFNT85T9jSVIHlxHAfbMnPbsMdjc0/edit?usp=sharing).

Once strap sampling is complete, the system is ready to begin normal operations (note `flash_ctrl` initialization is explicitly not done here, please see [sections below](#flash-handling) for more details).
The fast FSM acknowledges the slow FSM (which made the original power up request) and releases the system reset stage - this enables the processor to begin operation.
Afterwards, the fast FSM transitions to `Active` state and waits for a software low power entry request.

A low power request is initiated by software through a combination of WFI and software low power hint in {{< regref "CONTROL" >}}.
Specifically, this means if software issues only WFI, the power manager does not treat it as a power down request.
The notion of WFI is exported from the processor.
For Ibex, this is currently in the form of `core_sleeping_o`.

In response to the low power entry request, the fast FSM disables all second level clock gating.
Before proceeding, the fast FSM explicitly separates the handling between a normal low power entry and a [reset request](#reset-request-handlig).

For low power entry, there are two cases, [fall through handling](#fall-through-handling) and [abort handling](#abort-handling).
If none of these exception cases are matched for low power entry, the fast FSM then asserts appropriate resets as necessary and requests the slow FSM to take over.

For reset requests, fall through and aborts are not checked and the system simply resets directly.
Note in this scenario the slow FSM is not requested to take over.

#### Sparse FSM

Since the fast FSM is sparsely encoded, it is possible for the FSM to end up in an undefined state if attacked.
When this occurs, the fast FSM forcibly disables all clocks and holds the system in reset.

The fast FSM does not recover from this state until the system is reset by POR.


### ROM Integrity Checks

The power manager coordinates the [start up ROM check]({{< relref "hw/ip/rom_ctrl/doc/_index.md#the-startup-rom-check" >}}) with `rom_ctrl`.

After every reset, the power manager sends an indication to the `rom_ctrl` to begin performing integrity checks.
When the `rom_ctrl` checks are finished, a `done` and `good` indication are sent back to the power manager.

If the device is in life cycle test states (`TEST_UNLOCKED` or `RMA`), the `good` signal is ignored and the ROM contents are always allowed to execute.

If the device is not in one of the test states, the `good` signal is used to determine ROM execution.
If `good` is true, ROM execution is allowed.
If `good` is false, ROM execution is disallowed.

### Fall Through Handling

A low power entry fall through occurs when some condition occurs that immediately de-assert the entry conditions right after the software requests it.

This can happen if right after software asserts WFI, an interrupt is shown to the processor, thus breaking it out of its currently stopped state.
Whether this type of fall through happens is highly dependent on how the system handles interrupts during low power entry - some systems may choose to completely silence any interrupt not related to wakeup, others may choose to leave them all enabled.
The fall through handle is specifically catered to the latter category.

For a normal low power entry, the fast FSM first checks that the low power entry conditions are still true.
If the entry conditions are no longer true, the fast FSM "falls through" the entry handling and returns the system to active state, thus terminating the entry process.

### Abort Handling

If the entry conditions are still true, the fast FSM then checks there are no ongoing non-volatile activities from `otp_ctrl`, `lc_ctrl` and `flash_ctrl`.
If any module is active, the fast FSM "aborts" entry handling and returns the system to active state, thus terminating the entry process.

## Reset Request Handling

There are 4 reset requests in the system
- peripheral requested reset such as watchdog.
- reset manager's software requested reset, which is functionally very similar to a peripheral requested reset.
- power manager's internal reset request.
- Non-debug module reset.

Flash brownout is handled separately and described in [flash handling section](#flash-handling) below.

Peripheral requested resets such as watchdog are handled directly by the power manager, while the non-debug module reset is handled by the reset controller.
This separation is because the non-debug reset does not affect the life cycle controller, non-volatile storage controllers and alert states.
There is thus no need to sequence its operation like the others.

The power controller only observes reset requests in two states - the slow FSM `Low Power` state and the fast FSM `Active` state.
When a reset request is received during slow FSM `Low Power` state, the system begins its usual power up sequence even if a wakeup has not been received.

When a reset request is received during fast FSM `Active` state, the fast FSM asserts resets and transitions back to its `Low Power` state.
The normal power-up process described [above](#fast-clock-domain-fsm) is then followed to release the resets.
Note in this case, the slow FSM is "not activated" and remains in its `Idle` state.

### Power Manager Internal Reset Requests

In additional to external requests, the power manager maintains 2 internal reset requests:
* Escalation reset request
* Main power domain unstable reset request

#### Escalation Reset Request

Alert escalation resets in general behave similarly to peripheral requested resets.
However, peripheral resets are always handled gracefully and follow the normal FSM transition.

Alert escalations can happen at any time and do not always obey normal rules.
As a result, upon alert escalation, the power manager makes a best case effort to transition directly into reset handling.

This may not always be possible if the escalation happens while the FSM is in an invalid state.
In this scenario, the pwrmgr keeps everything powered off and silenced and requests escalation handling if the system ever wakes up.

#### Escalation Clock Timeout

Under normal behavior, the power manager can receive escalation requests from the system and handle them [appropriately](#escalation-reset-request).
However, if the escalation clock or reset are non-functional for any reason, the escalation request would not be serviced.

To mitigate this, the power manager actively checks for escalation interface clock/reset timeout.
This is done by a continuous request / acknowledge interface between the power manager's local clock/reset and the escalate network's clock/reset.

If the request / acknowledge interface does not respond within 128 power manager clock cycles, the escalate domain is assumed to be off.
When this happens, the power manager creates a local escalation request that behaves identically to the global escalation request.


#### Main Power Unstable Reset Requests
If the main power ever becomes unstable (the power okay indication is low even though it is powered on), the power manager requests an internal reset.
This reset behaves similarly to the escalation reset and transitions directly into reset handling.

Note that under normal low power conditions, the main power may be be turned off.
As a result of this, the main power unstable checks are valid only during states that power should be on and stable.
This includes any state where power manager has requested the power to be turned on.


### Reset Requests Received During Other States

All other states in the slow / fast FSM are considered transitional states.
Resets are not observed in other states because the system will always be transitioning towards one of the steady states (the system is in the process of powering down or powering up).
Once a steady state is reached, reset requests are then observed and processed.

### Reset Recording

There are three ways in which the device is reset:
- Non-debug-module reset request
- Low power entry (`sleep_req` in the state diagram)
- Direct reset requests by peripherals or alert escalation

The power manager does not handle the non-debug-module request (please see reset controller).
For the remaining two reset causes, the power manager handles only 1 pathway at a time (see state diagrams).
This means if reset request and low power entry collide, the power manager will handle them on a first come first served basis.
When the handling of the first is completed, the power manager handles the second pending request if it is still present.

This is done because low power resets and peripheral requested resets lead to different behaviors.
When the power manager commits to handling a specific request, it informs the reset manager why it has reset the processor.

For example, assume a low power entry request arrives slightly ahead of reset requests.
The power manager will:
- Transition the system into low power state.
- Inform the reset manager to record "low power exit" as the reset reason.
- Once in low state, transition the system to `Active` state by using the reset request as a wakeup indicator.
- Inform the reset manager to also record the peripheral that requested reset.
- Once in `Active` state, reset the system and begin normal power-up routines again.

If reset requests arrive slightly ahead of a low power entry request, then power manager will:
- Reset the system and begin normal power-up routines.
- Inform the reset manager to record the peripheral that requested reset.
- Once in `Active` state, if the low power entry request is still present, transition to low power state.
  - Inform the reset manager to also record "low power exit" as the reset reason.
- If the low power entry request was wiped out by reset, the system then stays in `Active` state and awaits software instructions.

Ultimately when control is returned to software, it may see two reset reasons and must handle them accordingly.


## Wakeup Recording

Similar to [reset handling](#reset-request-handling), wakeup signals are only observed during slow FSM `Low Power`; however their recording is continuous until explicitly disabled by software.

Wakeup recording begins when the fast FSM transitions out of `Active` state and continues until explicitly disabled by software.
This ensures wakeup events are not missed until software has set up the appropriate peripherals.

The software is also able to enable recording during `Active` state if it chooses to do so.  The recording enables are OR’d together for hardware purposes.


## Flash Handling
For the section below, flash macro refers to the proprietary flash storage supplied by a vendor.
`flash_ctrl`, on the other hand, refers to the open source controller that manages access to the flash macro.

### Power-Up Handling

The [AST]({{< relref "hw/top_earlgrey/ip/ast/doc" >}}) automatically takes the flash macro out of power down state as part of the power manager's power up request.

Once flash macro is powered up and ready, an indication is sent to the `flash_ctrl`.

Once the boot ROM is allowed to execute, it is expected to further initialize the `flash_ctrl` and flash macro prior to using it.
This involves the following steps:

*   Poll `flash_ctrl` register to ensure flash macro has powered up and completed internal initialization.
*   Initialize `flash_ctrl` seed reading and scrambling.

### Power-Down Handling

Before the device enters low power, the pwrmgr first checks to ensure there are no ongoing transactions to the flash macro.
When the device enters deep sleep, the flash macro is automatically put into power down mode by the AST.
The AST places the flash macro into power down through direct signaling between AST and flash macro, the pwrmgr is not directly involved.

When the device exits low power state, it is the responsibility of the boot ROM to poll for flash macro and `flash_ctrl` power-up complete similar to the above section.

### Flash Brownout Handling

When the external supply of the device dips below a certain threshold during a non-volatile flash macro operation (program or erase), the flash macro requires the operation to terminate in a pre-defined manner.
This sequence will be exclusively handled by the AST.

The power manager is unaware of the difference between POR and flash brownout.
Because of this, the software also cannot distinguish between these two reset causes.


## Supported Low Power Modes

This section details the various low power modes supported by OpenTitan.


### Deep Sleep or Standby

This is the lowest power mode of the device (outside of full power down or device held in reset).
During this state:

*   All clocks other than the always-on slow clock are turned off at the source.
*   All non-always-on digital domains are powered off.
*   I/O power domains may or may not be off.
    *   The state of the IO power domain has no impact on the digital core’s power budget, e.g. the IO power being off does not cause the accompanying digital logic in pads or elsewhere to leak more.


### Normal Sleep

This is a fast low power mode of the device that trades-off power consumption for resume latency.
During this state:

*   All clocks other than the KHz slow clock are turned off at the source.
*   All power domains are kept on for fast resume.
*   Sensor countermeasures can be opportunistically on.
*   I/O power domains may or may not be off.
    *   The state of the IO power domain has no impact on the digital core’s power budget, e.g. the IO power being off does not cause the accompanying digital logic in pads or elsewhere to leak more.

## Debug

When performing TAP debug, it is important for the debugging software to prevent the system from going to low power.
If the system enters low power during live debug, the debug session will be broken.
There is currently no standardized way to do this, so it is up to the debugging agent to perform the correct steps.


# Programmers Guide

The process in which the power manager is used is highly dependent on the system's topology.
The following proposes one method for how this can be done.

Assume first the system has the power states described [above](#supported-low-power-modes).

## Programmer Sequence for Entering Low Power

1. Disable interrupts
2. Enable desired wakeup and reset sources in {{< regref "WAKEUP_EN" >}} and {{< regref "RESET_EN" >}}.
3. Perform any system-specific low power entry steps, e.g.
   - Interrupt checks (if something became pending prior to disable)
4. Configure low power mode in {{< regref "CONTROL" >}}.
5. Set low power hint in {{< regref "LOW_POWER_HINT" >}}.
6. Set and poll {{< regref "CFG_CDC_SYNC" >}} to ensure above settings propagate across clock domains.
7. Execute wait-for-interrupt instruction on the processing host.

### Possible Exits

Once low power is initiated, the system may exit due to several reasons.
1. Graceful low power exit - This exit occurs when some source in the system gracefully wakes up the power manager.
2. System reset request - This exit occurs when either software or a peripheral requests the pwrmgr to reset the system.
3. [Fall through exit](#fall-through-handling) - This exit occurs when an interrupt manages to break the wait-for-interrupt loop.
4. [Aborted entry](#abort-handling) - This exit occurs when low power entry is attempted with an ongoing non-volatile transaction.

In both fall through exit and aborted entry, the power manager does not actually enter low power.
Instead the low power entry is interrupted and the system restored to active state.

## Programmer Sequence for Exiting Low Power

There are two separate cases for low power exit.
One is exiting from deep sleep, and the other is exiting from normal sleep.

### Exiting from Deep Sleep

When exiting from deep sleep, the system begins execution in ROM.

1. Complete normal preparation steps.
2. Check reset cause in [rstmgr]({{< relref "hw/ip/rstmgr/doc" >}})
3. Re-enable modules that have powered down.
4. Disable wakeup recording through {{< regref "WAKE_INFO_CAPTURE_DIS" >}}.
5. Check which source woke up the system through {{< regref "WAKE_INFO" >}}.
6. Take appropriate steps to handle the wake and resume normal operation.
7. Once wake is handled, clear the wake indication in {{< regref "WAKE_INFO" >}}.

### Exiting from Normal Sleep

The handling for fall-through and abort are similar to normal sleep exit.
Since in these scenarios the system was not reset, software continues executing the instruction after the wait-for-interrupt invocation.

1. Check exit condition to determine appropriate steps.
2. Clear low power hints and configuration in {{< regref "CONTROL" >}}.
3. Set and poll {{< regref "CFG_CDC_SYNC" >}} to ensure setting changes have propagated across clock boundaries.
4. Disable wakeup sources and stop recording.
5. Re-enable interrupts for normal operation and wakeup handling.
6. Once wake is handled, clear the wake indication in {{< regref "WAKE_INFO" >}}.

For an in-depth discussion, please see [power management programmers model](https://docs.google.com/document/d/1w86rmvylJgZVmmQ6Q1YBcCp2VFctkQT3zJ408SJMLPE/edit?usp=sharing) for additional details.

## Device Interface Functions (DIFs)

{{< dif_listing "sw/device/lib/dif/dif_pwrmgr.h" >}}

## Register Table

{{< incGenFromIpDesc "/hw/top_earlgrey/ip/pwrmgr/data/autogen/pwrmgr.hjson" "registers" >}}
