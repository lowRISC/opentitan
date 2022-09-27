---
title: Install OpenOCD
---

OpenOCD is a tool to connect with the target chip over JTAG and similar transports.
It also provides a GDB server which is an "intermediate" when debugging software on the chip with GDB.

At least OpenOCD 0.11.0 is required.

It is recommended to use the regular upstream version of OpenOCD instead of the [RISC-V downstream fork](https://github.com/riscv/riscv-openocd).

As most distributions do not yet include OpenOCD 0.11 in its package repositories building from source is likely to be required.
The following steps build OpenOCD (this should be done outside the `$REPO_TOP` directory):

```console
wget https://downloads.sourceforge.net/project/openocd/openocd/0.11.0/openocd-0.11.0.tar.bz2
tar -xf openocd-0.11.0.tar.bz2
cd openocd-0.11.0/
mkdir build
cd build
../configure --enable-ftdi --enable-verbose-jtag-io --disable-vsllink --enable-remote-bitbang --prefix=/tools/openocd
make -j4
sudo make install
```
