# Theory of Operation

Clock management in OpenTitan is divided into groups.
Each group has specific attributes and controls whether software is allowed to influence individual clocks during the active power state.
For low power states, please see [power manager](../../pwrmgr/README.md).

The grouping is derived from the chip partition and related security properties.
For illustrative purposes, this document uses the following assumed chip partition

![Example chip partition](example_chip_partition.svg)

The actual partition may differ per design, however the general principles are assumed to be the same.
Each group can be made up of more than 1 source clock.
The clocks themselves may be asynchronous - the grouping is thus a logical grouping instead of a physical one.

The grouping is summarized in the table below and described in more detail afterwards.
The table shows the group name, the modules that belong to each group, and whether SW can directly (via register control) or indirectly (via wait-for-interrupt) influence the state of the clock in the form of clock gating.

| Group           | Frequencies                    | Modules                                                        | Software       | Wait for Interrupt |
| -------------   | ------------------------------ | -------------------------------------------------------------- | -------------- | ------------------ |
| Power-up        | 100~200KHz, 24MHz              | Clock Manager, Power Manager, Reset Manager, Pinmux            | No             | No                 |
| Transactional   | ~100MHz                        | Aes, Kmac, Hmac, Key Manager, Otbn                             | Yes (1)        | Yes (2)            |
| Infrastructural | 24MHz, ~100MHz                 | Fabric, Fabric gaskets (iopmp), Memories                       | No             | Yes (3)            |
| Security        | 24MHz, ~100MHz                 | Alert handler, Entropy, Life cycle, Plic, Sensors              | No             | No                 |
| Peripheral      | 24MHz, 48MHz, 96MHz            | I2c, Spi, Uart, Usb, others                                    | Yes            | Yes                |
| Timers          | 100-200KHz, 24MHz              | AON timers, Timers, Watchdog                                   | No             | No                 |

* 1 - Transactional clock group's software control is only a software hint.
* 2 - Transactional clock group's wait-for-interrupt control is only a hint.
* 3 - May require additional complexity to handle multi-host (non-wait-for-interrupt) scenarios

## Power-up Clock Group

The group refers to modules responsible for power up, such as power, reset and clock managers.
Large portions of these modules operate to release clocks and resets for the rest of the design, thus cannot operate on gated versions of the clocks themselves.
They are the only group running clocks directly from the source.
All follow groups are derived after root clock gating.
See [block diagram](#block-diagram) for more details.

## Transactional Clock Group

This group refers to the collection of modules that are transactional by nature (example: `Hmac` / `Aes` / `Kmac`).
This means these modules perform specific tasks (for example encrypt, decrypt or hashing).
While performing these tasks, it is unsafe to manipulate or change the clocks.
Once these tasks are complete, the clocks can be safely shut-off.

To ensure such behavior on the clocks, The final clock enable is qualified with an `Idle` indication to signify that a transaction is ongoing and manipulation of the clock is not permitted.
The `Idle` signal must be sourced from the transactional modules and sent to the clock manager.

For this group software can only express its intent to shut-off, and does not have full control over the final state.
This intent is indicated with a register in the clock manager register file, see [`CLK_HINTS`](registers.md#clk_hints).

Even when the hint is set, the `Idle` does not directly manipulate the clock.
When an idle indication is received, the `clkmgr` counts for a period of 10 local clocks to ensure the idle was not a glitch.

Wait-for-interrupt based control is already a software hint, it can thus be applied to this group with the same `Idle` requirement.

For modules in this group, each module can be individually influenced, and thus each has its own dedicated clock gating logic.
The added benefit of allowing software control in this group is to save power, as some transactional modules can be both power and area hungry.

## Infrastructure Clock Group

This group refers to the collection of modules that support infrastructure functions.

If the clocks to these modules are turned off, there may not be a way to turn them back on and could thus result in system deadlock.
This includes but is not limited to:
* Turning off fabric / gasket clocks, and thus having no way to access the fabric and resume the clock.
* Turning off memory clocks such that there is no way to execute code that would resume the clocks.

For this group, there is no reason to allow software control over the clocks, as it could be used to create a system deadlock where after disabling infrastructure clocks there is no way to turn them back on.
Wait-for-interrupt controls however can be used, as long as there is a way to break the processor out of wait-for-interrupt and handle other bus hosts, while also separating the functional portions from bus access.
See Wait-for-interrupt clock gating for more details.

## Security Clock Group

The security clock group is made up of security modules that either have background functions (entropy, alert manager, sensors) or perform critical security functions where disabling clocks could have unexpected side effects (life cycle, otp, pinmux, plic).

For this group, no software influence over the clock state is allowed during the active state.
The clocks are always running as long as the source is on.

This group is not functionally identical to the power-up group.
The power-up group is run on clocks directly from the clock source, while the security group is derived after root clock gating.

## Timer Clock Group

The timer clock group is composed of modules that track time for various purposes.
As influencing time can change the perspective of software and potentially reveal security vulnerabilities, the clock state for these modules cannot be directly or indirectly influenced by software.

Functionally, this group is identical to the security group.

## Peripheral Clock Group

The peripheral clock group is composed of I/O peripherals modules.
By their nature, I/O peripherals are both transactional and most of the time not security critical - so long as proper care is taken to sandbox peripherals from the system.

These modules can be both directly and indirectly controlled by software.
The controls can also be individual to each peripheral.

## Wait-for-Interrupt (wfi) Gating

Wait-for-interrupt clock gating refers to the mechanism of using a processor's sleep indication to actively gate off module clocks.
Of the groups enumerated, only transactional, infrastructural and peripheral groups can be influenced by `wfi`.

As `wfi` is effectively a processor clock request, there are subtleties related to its use.
The interaction with each clock group is briefly described below.

### Transactional Clock Group

While `wfi` gating can be applied to this group, the modules in this category are already expected to be turned off and on by software depending on usage.
Specifically, these modules are already completely managed by software when not in use, thus may not see significant benefit from `wfi` gating.

### Peripheral Clock Group

Since peripherals, especially those in device mode, are often operated in an interrupt driven way, the peripheral's core operating clock frequently must stay alive even if the processor is asleep.
This implies that in order for peripherals to completely support `wfi` clock gating, they must be split between functional clocks and bus clocks.

The bus clocks represent the software interface and can be turned off based on `wfi gating`, while the functional clocks should be kept running to ensure outside activity can be captured and interrupts created.
In this scenario, it is important to ensure the functional clocks are responsible for creating interrupts and not the bus clocks, as the latter may not be available during `wfi`.

This division may only be beneficial for peripherals where register and local fabric size is large relative to the functional component.

### Infrastructural Clock Group

This clock group matches `wfi` functionality well.
Most infrastructural components such as fabric, gaskets and memories, have no need to be clocked when the processor is idle.
Some components such as flash controller however would also need to be split into bus and functional halves to support long, background activities while the processor is idle.

However, there are additional complications.
In systems where the processor is not the only bus host, `wfi` can only be used as the software request and not final clock state decision.
Hardware driven requests, such as those coming from a `dma` or any peripheral driven bus host, would also need to be included as part of the equation.
Further, since it is possible hardware may issue requests at the boundary of a clock state changes, additional fabric gaskets would be required to protect hosts when destinations are temporarily clocked off.
The bus requests themselves thus become dynamic clock request signals to help enable components in its path.

There is thus a moderate design and high verification cost to supporting `wfi` gating for the infrastructural group.

## Block Diagram

The following is a high level block diagram of the clock manager.

![Clock Manager Block Diagram](clkmgr_block_diagram.svg)

### Reset Domains

Since the function of the clock manager is tied closely into the power-up behavior of the device, the reset domain selection must also be purposefully done.
To ensure that default clocks are available for the [power manager to release resets and initialize memories](../../pwrmgr/README.md#fast-clock-domain-fsm), the clock dividers inside the clock manager directly use `por` (power-on-reset) derived resets.
This ensures that the root clocks are freely running after power-up and its status can be communicated to the `pwrmgr` regardless of any other activity in the device.

The other functions inside the clock manager operate on the `life cycle reset` domain.
This ensures that other clock manager functions still release early relative to most functions in the system, and that a user or escalation initiated reset still restores the clock manager to a default clean slate.

The escalation reset restoration is especially important as the clock manager can generate fatal faults that lead to escalation.
If there were not a mechanism that allows escalation to clear the original fault, the system would simply remain in a faulted state until a user initiated a `por` event.

For a detailed breakdown between `por` and `life cycle` resets, please see the [reset manager](../../rstmgr/README.md).

The following diagram enhances the block diagram to illustrate the overall reset domains of the clock manager.
![Clock Manager Block Diagram](clkmgr_rst_domain.svg)

### Clock Gated Indications for Alert Handler

The alert handler needs to know the status of the various clock domains in the system to avoid false alert indications due to the ping mechanism.
To that end, the clock manager outputs a 4bit MuBi signal for each clock domain that indicates whether its clock is active.
For more information on this mechanism, see [alert handler documentation](../../alert_handler/doc/theory_of_operation.md#low-power-management-of-alert-channels).

## Design Details

### Root Clock Gating and Interface with Power Manager

All clock groups except the power-up group run from gated source clocks.
The source clocks are gated off during low power states as controlled by the power manager.
When the power manager makes a clock enable request, the clock manager ensures all root clock gates are enabled before acknowledging.
Likewise, when the power manager makes a clock disable request, the clock manager ensures all root clock gates off disabled before acknowledging.

Note, the power manager's request to turn off clocks supersedes all other local controls in the clock manager.
This means even if a particular clock is turned on by the clock manager (for example a transactional unit that is ongoing or a peripheral that is enabled), the power manager requests will still turn clocks on / off at the root.

This makes it software's responsibility to ensure low power entry requests (which can only be initiated by software) do not conflict with any ongoing activities controlled by software.
For example, software should ensure that Aes / Otbn activities have completed before initializing a low power entry process.

### Clock Division

Not all peripherals run at the full IO clock speed, hence the IO clock is divided down by 2x and 4x in normal operation.
This division ratio can be modified to 1x and 2x when switching to an external clock, since the external clock may be slower than the internal clock source.
See also [external clock switch support](#external-clock-switch-support).

The divided clock is not assumed to be synchronous with its source and is thus treated like another asynchronous branch.
Further, the clock dividers are hardwired and have no software control, this is to further ensure there are no simple paths for faulty or malicious software to tamper.

Note that for debug purposes, `ast` can also request a change in the clock division ratio via a dedicated hardware interface (`div_step_down_req_i`).

### Wait-for-Interrupt Support

Given the marginal benefits and the increased complexity of `wfi` support, the first version of this design does not support `wfi` gating.
All `wfi CG` modules in the block diagram are thus drawn with dashed lines to indicate it can be theoretically supported but currently not implemented.

It may be added for future more complex systems where there is a need to tightly control infrastructural power consumption as a result from clocks.

### External Clock Switch Support

Clock manager supports the ability to request root clocks switch to an external clock.
There are two occasions where this is required:
-  Life cycle transition from `RAW` / `TEST_LOCKED*` to `TEST_UNLOCKED*` [states](../../../../ip/lc_ctrl/README.md#clk_byp_req).
-  Software request for external clocks during normal functional mode.


### Clock Frequency / Time-out Measurements

Clock manager can continuously measure root clock frequencies to see if any of the root clocks have deviated from the expected frequency.
This feature can be enabled through the various measurement control registers such as [`IO_MEASURE_CTRL`](registers.md#io_measure_ctrl).

The root clocks, specifically the clocks supplied from `ast` and their divided variants, are constantly measured against the `always on clock` when this feature is enabled.
Software sets both an expected maximum and minimum for each measured clock.

Clock manager then counts the number of relevant root clock cycles in each always-on clock period.
If the resulting count differs from the programmed thresholds, a recoverable error is registered.

Since the counts are measured against a single cycle of always on clock, the minimal error that can be detected is dependent on the clock ratio between the measured clock and 1 cycle of the always on clock.
Assume a 24MHz clock and an always-on clock of 200KHz.
The minimal error detection is then 200KHz / 24MHz, or approximately 0.83%.

This means if the clock's actual value is between 23.8MHz and 24.2MHz, this deviation will not be detected.
Conversely, if the clock's natural operation has an error range wider than this resolution, the min / max counts must be adjusted to account for this error.

Additionally, clock manager uses a similar time-out mechanism to see if any of the root clocks have stopped toggling for an extended period of time.
This is done by creating an artificial handshake between the root clock domain and the always on clock domain that must complete within a certain amount of time based on known clock ratios.
Based on the nature of the handshake and the margin window, the minimal timeout detection window is approximately 2-4 always on clock cycles.
If the root clock domain stops and resumes in significantly less time than this window, the time-out may not be detected.

There are three types of errors:
* Clock too fast error
* Clock too slow error
* Clock time-out error

Clock too fast is registered when the clock cycle count is greater than the software programmed max threshold.
Clock too slow is registered when the clock cycle count is less than the software programmed min threshold.
Clock time-out is registered when the clock stops toggling and the timeout threshold is reached.

As these are all software supplied values, the entire measurement control can be locked from further programming through [`MEASURE_CTRL_REGWEN`](registers.md#measure_ctrl_regwen).
