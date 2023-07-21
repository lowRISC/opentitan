# Programmer's Guide

## Initialization

The following code snippet demonstrates initializing the EDN block.

```cpp

void edn_init(unsigned int enable) {

  // set the control register enable bit
  *CTRL_REG = enable; // should be 0x1 by default

  // the EDN interrupts can optionally be enabled
}
```

## Module enable and disable

EDN may only be enabled if CSRNG is enabled.
Once disabled, EDN may only be re-enabled after CSRNG has been disabled and re-enabled.

## Error conditions

Need to alert the system of a FIFO overflow condition.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_edn.h)
