# Test Boot ROM

The Boot ROM is a **testing-only** device image.
The [ROM](https://opentitan.org/book/sw/device/silicon_creator/rom) is the reference implementation of the OpenTitan Secure Boot specification.

The boot ROM is always the first piece of code run in the system.
At the moment, it serves 2 functions:

* Bootstrap additional code if requested.
* Jump to embedded flash and begin execution.

## Bootstrap Overview

The boot ROM bootstrap function differs between Verilator, DV and FPGA.

In DV and in Verilator, embedded flash code can be backdoor loaded.
So, for most of the tests, the run times can be sped up by bypassing the code load.
However, both do support the bootstrap function and can be used similarly to the FPGA in loading code.
In DV, a subset of tests will indeed exercise the bootstrap code paths since it is a system level usecase.

In FPGA, bootstrap is required and requested by an external host via GPIO.
Bootstrap can be requested by driving TAP\_STRAP0 (USB\_A18) and TAP\_STRAP1 (USB\_A19) to 0 and 1, respectively, and presenting strong pull-ups on all SW\_STRAP* pins (USB\_A15, USB\_A16, and USB\_A17).
If bootstrap is requested, the boot ROM initializes the SPI interface and flash controller.
OpenTitan uses a SPI Flash based bootstrap protocol and can be programmed using the `opentitantool`.
