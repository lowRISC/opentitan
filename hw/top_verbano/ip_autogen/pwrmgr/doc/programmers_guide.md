# Programmer's Guide

The process in which the power manager is used is highly dependent on the system's topology.
The following proposes one method for how this can be done.

Assume first the system has the power states described [above](theory_of_operation.md#supported-low-power-modes).

## Programmer Sequence for Entering Low Power

1. Disable interrupt handling.
2. Mask all interrupt sources that should not prevent low power entry.
   - Note that merely *disabling* interrupt handling with the `mie` global interrupt-enable bit on the processing host is insufficient.
   - Interrupt sources that are not masked can cause the [fall through exit](theory_of_operation.md#fall-through-handling).
3. Enable desired wakeup and reset sources in [`WAKEUP_EN`](registers.md#wakeup_en) and [`RESET_EN`](registers.md#reset_en).
4. Perform any system-specific low power entry steps, e.g.
   - Interrupt checks (if something became pending prior to disable)
5. Configure low power mode configuration in [`CONTROL`](registers.md#control).
   - [`LOW_POWER_HINT`](registers.md#control--low_power_hint) must be set to trigger low power entry when the CPU sleeps.
7. Set and poll [`CFG_CDC_SYNC`](registers.md#cfg_cdc_sync) to ensure above settings propagate across clock domains.
8. Execute wait-for-interrupt instruction on the processing host.

Note that entering low power mode requires that pwrmgr's `pwr_cpu_i.core_sleeping` input be at logic high long enough to be sampled.
A wait-for-interrupt instruction does not guarantee entry into low power, since the CPU could immediately resume execution in some cases.

### Possible Exits

Once low power is initiated, the system may exit due to several reasons.
1. Graceful low power exit - This exit occurs when some source in the system gracefully wakes up the power manager.
2. System reset request - This exit occurs when either software or a peripheral requests the pwrmgr to reset the system.
3. [Fall through exit](theory_of_operation.md#fall-through-handling) - This exit occurs when an interrupt manages to break the wait-for-interrupt loop.
4. [Aborted entry](theory_of_operation.md#abort-handling) - This exit occurs when low power entry is attempted with an ongoing non-volatile transaction.

In both fall through exit and aborted entry, the power manager does not actually enter low power.
Instead the low power entry is interrupted and the system restored to active state.

In addition, a CPU's sleeping signal that is too short for the power manager to sample will not trigger even an attempt to go to low power.
In such cases, there will be no bits set in [`WAKE_INFO`](registers.md#wake_info), and no side effects of pwrmgr entering low power mode will trigger.

To check the exit condition, software can follow these steps:
1. Clear low power hint in [`CONTROL`](registers.md#control) and poll until it becomes cleared.
<!-- As of this writing, the CONTROL REGWEN locks out writes to CONTROL once pwrmgr receives the trigger to enable low power mode.
     pwrmgr enables writes again upon exiting low power mode.
     For the case where low power isn't even *attempted* due to short WFI, CONTROL will not be locked, so the clear will succeed. -->
  - Until the hint clears, the values in [`WAKE_INFO`](registers.md#wake_info) may not reflect the true exit condition.
2. Check [`WAKE_INFO`](registers.md#wake_info) to get the condition.
  - If no bits are set, then this was a fast fall through, where low power entry was not attempted.

## Programmer Sequence for Exiting Low Power

There are two separate cases for low power exit.
One is exiting from deep sleep, and the other is exiting from normal sleep.

### Exiting from Deep Sleep

When exiting from deep sleep, the system begins execution in ROM.

1. Complete normal preparation steps.
2. Check reset cause in [rstmgr](../../rstmgr/README.md)
3. Re-enable modules that have powered down.
4. Disable wakeup recording through [`WAKE_INFO_CAPTURE_DIS`](registers.md#wake_info_capture_dis).
5. Check which source woke up the system through [`WAKE_INFO`](registers.md#wake_info).
6. Take appropriate steps to handle the wake and resume normal operation.
7. Once wake is handled, clear the wake indication in [`WAKE_INFO`](registers.md#wake_info).

### Exiting from Normal Sleep

The handling for fall-through and abort are similar to normal sleep exit.
Since in these scenarios the system was not reset, software continues executing the instruction after the wait-for-interrupt invocation.

1. Check exit condition to determine appropriate steps.
2. Clear low power hints and configuration in [`CONTROL`](registers.md#control).
3. Set and poll [`CFG_CDC_SYNC`](registers.md#cfg_cdc_sync) to ensure setting changes have propagated across clock boundaries.
4. Disable wakeup sources and stop recording.
5. Re-enable interrupts for normal operation and wakeup handling.
6. Once wake is handled, clear the wake indication in [`WAKE_INFO`](registers.md#wake_info).

For an in-depth discussion, please see [power management programmers model](https://docs.google.com/document/d/1w86rmvylJgZVmmQ6Q1YBcCp2VFctkQT3zJ408SJMLPE/edit?usp=sharing) for additional details.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../../sw/device/lib/dif/dif_pwrmgr.h)
