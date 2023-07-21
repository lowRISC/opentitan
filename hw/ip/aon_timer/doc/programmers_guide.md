# Programmer's Guide

## Initialization

1. Write the timer values [`WKUP_COUNT`](registers.md#wkup_count) and [`WDOG_COUNT`](registers.md#wdog_count) to zero.
2. Program the desired wakeup pre-scaler value in [`WKUP_CTRL`](registers.md#wkup_ctrl).
3. Program the desired thresholds in [`WKUP_THOLD`](registers.md#wkup_thold), [`WDOG_BARK_THOLD`](registers.md#wdog_bark_thold) and [`WDOG_BITE_THOLD`](registers.md#wdog_bite_thold).
4. Set the enable bit to 1 in the [`WKUP_CTRL`](registers.md#wkup_ctrl) / [`WDOG_CTRL`](registers.md#wdog_ctrl) registers.
5. If desired, lock the watchdog configuration by writing 1 to the `regwen` bit in [`WDOG_REGWEN`](registers.md#wdog_regwen).

## Watchdog pet

Pet the watchdog by writing zero to the [`WDOG_COUNT`](registers.md#wdog_count) register.

## Interrupt Handling

If either timer reaches the programmed threshold, interrupts are generated from the AON_TIMER module.
Disable or reinitialize the wakeup timer if required by clearing the enable bit in [`WKUP_CTRL`](registers.md#wkup_ctrl) or clearing the timer value in [`WKUP_COUNT`](registers.md#wkup_count).
Clear the interrupt by writing 1 into the Interrupt Status Register [`INTR_STATE`](registers.md#intr_state).

If the timer has caused a wakeup event ([`WKUP_CAUSE`](registers.md#wkup_cause) is set) then clear the wakeup request by writing 0 to [`WKUP_CAUSE`](registers.md#wkup_cause).

If [`WKUP_COUNT`](registers.md#wkup_count) remains above the threshold after clearing the interrupt or wakeup event and the timer remains enabled, the interrupt and wakeup event will trigger again at the next clock tick.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_aon_timer.h)
