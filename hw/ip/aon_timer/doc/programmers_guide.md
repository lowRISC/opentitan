# Programmer's Guide

## Initialization

1. Set the timer values [`WKUP_COUNT_LO`](registers.md#wkup_count_lo), [`WKUP_COUNT_HI`](registers.md#wkup_count_hi) and [`WDOG_COUNT`](registers.md#wdog_count) to zero.
2. Program the desired wakeup pre-scaler value in [`WKUP_CTRL`](registers.md#wkup_ctrl).
3. Program the desired thresholds in [`WKUP_THOLD_LO`](registers.md#wkup_thold_lo), [`WKUP_THOLD_HI`](registers.md#wkup_thold_hi), [`WDOG_BARK_THOLD`](registers.md#wdog_bark_thold) and [`WDOG_BITE_THOLD`](registers.md#wdog_bite_thold).
4. Set the enable bit to 1 in the [`WKUP_CTRL`](registers.md#wkup_ctrl) / [`WDOG_CTRL`](registers.md#wdog_ctrl) registers.
5. If desired, lock the watchdog configuration by writing 0 to the `regwen` bit in [`WDOG_REGWEN`](registers.md#wdog_regwen).

## Watchdog pet

Pet the watchdog by writing zero to the [`WDOG_COUNT`](registers.md#wdog_count) register.

## Wakeup count and threshold access

The wakeup counter and threshold are both 64-bit values accessed via two 32-bit hi and lo registers.
It is not possible to read or modify the 64-bit values in a single atomic access.
Care must be taken to avoid issues due to race conditions caused by this.
Below are some recommendations on how to access the counter and threshold to avoid problems.

### Reading the counter

The counter might increment between the read of [`WKUP_COUNT_HI`](registers.md#wkup_count_hi) and the read of [`WKUP_COUNT_LO`](registers.md#wkup_count_lo).
If the [`WKUP_COUNT_LO`](registers.md#wkup_count_lo) value overflows between the two register reads the combined 64-bit value may be incorrect.
Consider the scenario where the 64-bit counter value is `0x1_ffff_ffff`.
A read of the [`WKUP_COUNT_HI`](registers.md#wkup_count_hi) value gives `0x1`.
If the counter then increments to `0x2_0000_0000` then a read of [`WKUP_COUNT_LO`](registers.md#wkup_count_lo) gives `0x0000_00000`.
The final 64-bit value of `0x1_0000_0000` is incorrect.
The pseudo code below provides a method to avoid this issue:

```
counter_hi = REG_READ(WKUP_COUNT_HI);
counter_lo = REG_READ(WKUP_COUNT_LO);
counter_hi_2 = REG_READ(WKUP_COUNT_HI);

// If WKUP_COUNT_LO overflowed between first and second read WKUP_COUNT_HI will
// have changed
if counter_hi != counter_hi_2 {
  // Read new WKUP_COUNT_LO value and use second WKUP_COUNT_HI read as top 32 bits
  counter_lo = REG_READ(WKUP_COUNT_LO);
  counter_hi = counter_hi_2;
}

counter_full = counter_hi << 32 | counter_lo;
```

### Writing the counter

Between the two count register ([`WKUP_COUNT_HI`](registers.md#wkup_count_hi) and [`WKUP_COUNT_LO`](registers.md#wkup_count_lo)) writes the counter may increment.
If the [`WKUP_COUNT_LO`](registers.md#wkup_count_lo) value overflows between a [`WKUP_COUNT_HI`](registers.md#wkup_count_hi) and [`WKUP_COUNT_LO`](registers.md#wkup_count_lo) write the intended counter value may be incorrect.
For example an attempt to clear the counter to 0 could result in a counter value of `0x1_0000_0000`.
It is recommended the wakeup timer is disabled with [`WKUP_CTRL`](registers.md#wkup_ctrl) before writing to the [`WKUP_COUNT_HI`](registers.md#wkup_count_hi) and [`WKUP_COUNT_LO`](registers.md#wkup_count_lo) registers to avoid this problem.

### Reading the threshold

The hardware does not alter the value of the [`WKUP_THOLD_LO`](registers.md#wkup_thold_lo) and [`WKUP_THOLD_HI`](registers.md#wkup_thold_hi) registers so there are no race conditions in reading them.

### Writing the threshold

When writing to [`WKUP_THOLD_LO`](registers.md#wkup_thold_lo) and [`WKUP_THOLD_HI`](registers.md#wkup_thold_hi) between the two writes the 64-bit threshold is effectively an interim value that's not intended to be the real threshold.
It is possible the interim threshold is lower than the previous threshold triggering a spurious wakeup.
Use the method in the pseudo code below to avoid this issue:

```
disable_wakeup_interrupt();

// Guaranteed 64-bit threshold greater than or equal to old threshold. This
// prevents an interrupt caused by the threshold decreasing.
REG_WRITE(WKUP_THOLD_LO, UINT32_MAX);
// Guaranteed 64-bit threshold greater than or equal to intended threshold. If
// the counter reaches this value before we've completing the final write then
// the interrupt would have happened with the intended threshold as well.
REG_WRITE(WKUP_THOLD_HI, new_thold >> 32);
// 64-bit threshold now intended value
REG_WRITE(WKUP_THOLD_LO, new_thold & 0xffff_ffff);

enable_wakeup_interrupt();
```

## Interrupt Handling

If either timer reaches the programmed threshold, interrupts are generated from the AON_TIMER module.
Disable the wakeup timer by clearing the enable bit in [`WKUP_CTRL`](registers.md#wkup_ctrl).
Reset the timer if desired by clearing [`WKUP_COUNT_HI`](registers.md#wkup_count_hi) and [`WKUP_COUNT_LO`](registers.md#wkup_count_lo) and renable by setting the enable bit in [`WKUP_CTRL`](registers.md#wkup_ctrl).
Clear the interrupt by writing 1 into the Interrupt Status Register [`INTR_STATE`](registers.md#intr_state).

If the timer has caused a wakeup event ([`WKUP_CAUSE`](registers.md#wkup_cause) is set) then clear the wakeup request by writing 0 to [`WKUP_CAUSE`](registers.md#wkup_cause).

If {[`WKUP_COUNT_HI`](registers.md#wkup_count_hi), [`WKUP_COUNT_LO`](registers.md#wkup_count_lo)} remains above the threshold after clearing the interrupt or wakeup event and the timer remains enabled, the interrupt and wakeup event will trigger again at the next clock tick.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_aon_timer.h)
