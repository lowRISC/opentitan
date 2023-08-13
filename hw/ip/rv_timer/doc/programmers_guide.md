# Programmer's Guide

## Initialization

Software is expected to configure `prescaler` and `step` before activating the
timer. These two fields need to be stable to correctly increment the timer
value. If software wants to change these fields, it should de-activate the
timer and then proceed.

## Register Access

The timer IP has 64-bit timer value registers and 64-bit compare registers. The
register interface, however, is set to 32-bit data width. The CPU cannot access
64-bit data in a single request. However, when split into two reads, it is
possible the timer value can increment between the two requests.

The IP doesn't have a latching or blocking mechanism to avoid this issue. It is
the programmer's responsibility to ensure the correct value is read. For
instance, if the CPU reads `0xFFFF_FFFF` from lower 32-bit timer value (`mtime`)
and `0x0000_0001` from upper 32-bit timer value (`mtimeh`), there is a chance
that rather than having the value `0x1_FFFF_FFFF` the timer value has changed
from `0x0_FFFF_FFFF` to `0x1_0000_0000` between the two reads. If there is the
possibility of an interrupt between the two reads then the counter could have
advanced even more.

This condition can be detected in a standard way using a third read. Figure 10.1
in the RISC-V unprivileged specification explains how to avoid this.

```asm
again:
    rdcycleh  x3
    rdcycle   x2
    rdcycleh  x4
    bne       x3, x4, again
```

Updating `mtimecmp` register also follows a similar approach to avoid a spurious
interrupt during the register update. Please refer to the `mtimecmp` section in
the RISC-V privileged specification.

```asm
# New comparand is in a1:a0.
li t0, -1
sw t0, mtimecmp   # No smaller than old value.
sw a1, mtimecmp+4 # No smaller than new value.
sw a0, mtimecmp   # New value.
```

## Timer behaviour close to 2^64

There are some peculiarities when `mtime` and `mtimecmp` get close to the end of
the 64-bit integer range. In particular, because an unsigned comparison is done
between `mtime` and `mtimecmp` care is needed. A couple of cases are:

1. `mtimecmp` close to 0xFFFF_FFFF_FFFF_FFFF. In this case the time-out event
   will be signaled when `mtime` passes the comparison value, the interrupt will
   be raised and the source indicated in the corresponding bit of the interrupt
   status register. However, if there is a delay in servicing the interrupt the
   `mtime` value could wrap to zero (and continue to increment) so the value
   read by the interrupt service routine will be less than the comparison value.

2. When the timer is setup to trigger a `timeout` some number of timer ticks
   into the future, the computation of the comparison value `mtime + timeout`
   may overflow. If this value is set in `mtimecmp` it would make `mtime`
   greater than `mtimecmp` and immediately signal an interrupt.
   A possible solution is to have an intermediate interrupt by setting the
   `mtimecmp` to 64-bit all-ones, `0xFFFF_FFFF_FFFF_FFFF`. Then the service
   routine for that interrupt will need to poll `mtime` until it wraps (which
   could take up to a timer clock tick) before scheduling the required interrupt
   using the originally computed `mtimecmp` value.

## Interrupt Handling

If `mtime` is greater than or equal to the value of `mtimecmp`, the interrupt is generated from the RV_TIMER module.
If the core enables the timer interrupt in `MIE` CSR, it jumps into the timer interrupt service routine.
Clearing the interrupt can be done by writing 1 into the Interrupt Status register [`INTR_STATE0`](../../spi_device/data/spi_device.hjson#intr_state0).
The RV_TIMER module also follows RISC-V Privileged spec that requires the interrupt to be cleared by updating `mtimecmp` memory-mapped CSRs.
In this case both [`COMPARE_LOWER0_0`](../../spi_device/data/spi_device.hjson#compare_lower0_0) and [`COMPARE_UPPER0_0`](../../spi_device/data/spi_device.hjson#compare_upper0_0) can clear the interrupt source.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_rv_timer.h)
