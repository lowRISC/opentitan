# Boot ROM Overview

The Boot ROM is a **testing-only** device image.
The [Mask ROM]({{< relref "sw/device/mask_rom/docs/index.md" >}}) is the reference implementation of the OpenTitan Secure Boot specification.

The boot ROM is always the first piece of code run in the system.
At the moment, it serves 2 functions:

* Bootstrap additional code if requested.
* Jump to embedded flash and begin execution.

## Bootstrap Overview

The boot ROM bootstrap function differs between Verilator, DV and FPGA.

In DV and in Verilator, embedded flash code can be backdoor loaded.
So, for most of the tests, the run times can be sped up by bypassing the code load.
However, both do support the bootstrap function and can be used similarly to the FPGA in loading code.
In DV, a subset of tests will indeed exercise the the bootstrap code paths since it is a system level usecase.

In FPGA, bootstrap is required and requested by an external host via GPIO (IO_DPS7 in the NexysVideo FPGA, which is tied to GPIO17 in the design).
If bootstrap is true (the connected pin is driven to 1), the boot ROM initializes the SPI interface and flash controller.
The executable image is broken down into 1KB frames and sent one by one by the host over spi.
Each frame is made up of a header and associated payload.
The header contains information such as a SHA256 hash of the entire frame, the frame numer and the flash location to which it should be programmed.
See [spiflash]({{< relref "sw/host/spiflash/README.md" >}}) for more details.

The boot ROM and host communicate through a request / ACK interface.
Upon receiving each frame, boot ROM computes the hash of that frame and sends it back to the host.
If the hash matches what the host expects, the host then continues to send the next frame; otherwise, it retries the previous frame.

Upon reception of the first successful frame, boot ROM erases all flash contents and begins programming frame by frame.
At the successful conclusion of bootstrap, boot ROM then jumps to the newly downloaded and programme code.
