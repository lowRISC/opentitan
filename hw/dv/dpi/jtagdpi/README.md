# JTAG DPI module for OpenOCD remote_bitbang driver

This DPI module provides a "virtual" JTAG connection between an simulated chip and [OpenOCD](https://openocd.org/).
It makes use of the `remote_bitbang` JTAG driver shipped with OpenOCD, which forwards JTAG requests over TCP to a remote server.
The `jtagdpi` module is instantiated in the hardware simulation to receive the JTAG requests from OpenOCD and drive the JTAG pins (TCK, TMS, TDI, etc.) from it.

The `remote_bitbang` protocol is documented in the OpenOCD source tree at `doc/manual/jtag/drivers/remote_bitbang.txt`, or [online](https://repo.or.cz/openocd.git/blob/HEAD:/doc/manual/jtag/drivers/remote_bitbang.txt).
In case you're wondering how to configure this interface, there is rendered documentation [here](https://openocd.org/doc/html/Debug-Adapter-Configuration.html).

OpenOCD does not automatically get built with remote bitbang enabled.
If you are building from source you must look in `configure.ac` and change the `no` to `yes` in this expression `build_remote_bitbang=no`.
