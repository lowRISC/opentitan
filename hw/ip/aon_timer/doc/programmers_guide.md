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

The counter might increment between writes to the two count registers ([`WKUP_COUNT_HI`](registers.md#wkup_count_hi) and [`WKUP_COUNT_LO`](registers.md#wkup_count_lo)).
To avoid this corrupting the value, software should set the lower word first:
- Write [`WKUP_COUNT_LO`](registers.md#wkup_count_lo).
- Write [`WKUP_COUNT_HI`](registers.md#wkup_count_hi).

This may not work for a target value that is close to overflow (where e.g. bits `[31:8]` are set).
For such values, disable the timer with [`WKUP_CTRL`](registers.md#wkup_ctrl) while writing the counter.

### Reading the threshold

The hardware does not alter [`WKUP_THOLD_LO`](registers.md#wkup_thold_lo) and [`WKUP_THOLD_HI`](registers.md#wkup_thold_hi), so there are no race conditions in reading them.

### Writing the threshold

The threshold is written by setting two registers ([`WKUP_THOLD_LO`](registers.md#wkup_thold_lo) and [`WKUP_THOLD_HI`](registers.md#wkup_thold_hi)).
As such, there will be an interim value of the threshold after the first register has been written.
To avoid this triggering a spurious wakeup, use the method below:
```
disable_wakeup_interrupt();

// Set the lower word to its maximum value. The resulting threshold will definitely be at least as
// big as the previous value.
REG_WRITE(WKUP_THOLD_LO, UINT32_MAX);

// Set the upper word to its desired value. The resulting threshold will still be at least as big
// as the desired threshold, so there cannot be any spurious trigger event.
REG_WRITE(WKUP_THOLD_HI, new_thold >> 32);

// Set the lower word to its desired value.
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
