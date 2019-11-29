DMI DPI module for OpenOCD remote_bitbang driver
================================================

This DPI module provides a "virtual" JTAG connection between a simulated chip and [OpenOCD](http://openocd.org/).
It makes use of the `remote_bitbang` JTAG driver shipped with OpenOCD, which forwards JTAG requests over TCP to a remote server.
The `dmidpi` module is instantiated in the hardware simulation to receive the JTAG requests from OpenOCD and drive DMI pins directly.

Note that this module replaces the JTAG Debug Transport Module ("DTM") inside the debug system.

```code
  |------------|          |------------|          |--------------|
  |            |          |            |          |              |
  |            | TCP intf |            | DMI intf |              |
  |  OpenOCD   |<========>|   dmidpi   |<========>| Debug Module |
  |  (remote   |          |   (DTM)    |          |              |
  |   bitbang) |          |            |          |              |
  |------------|          |------------|          |--------------|
```

The `remote_bitbang` protocol is documented in the OpenOCD source tree at
`doc/manual/jtag/drivers/remote_bitbang.txt`, or online at
https://repo.or.cz/openocd.git/blob/HEAD:/doc/manual/jtag/drivers/remote_bitbang.txt
