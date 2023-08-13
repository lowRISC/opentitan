# Programmer's Guide

There are in general only two software controllable functions in the clock manager.


## Transactional Clock Hints

To enable a transactional clock, set the corresponding hint in [`CLK_HINTS`](registers.md#clk_hints) to `1`.
To disable a transactional clock, set the corresponding hint in [`CLK_HINTS`](registers.md#clk_hints) to `0`.
Note, a `0` does not indicate clock is actually disabled, software can thus check [`CLK_HINTS_STATUS`](registers.md#clk_hints_status) for the actual state of the clock.

## Peripheral Clock Controls
To control peripheral clocks, directly change the bits in [`CLK_ENABLES`](registers.md#clk_enables).

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_clkmgr.h)
