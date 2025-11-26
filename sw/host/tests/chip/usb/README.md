# USB tests

This directory contains the test harnesses for USB tests.
Some of these tests not only require permissions to access the OT USB device,
but also the USB hub to which the OT USB device is connected.
For this reason, it is **strongly** encouraged to connect the device under test
to a dedicated hub and not your root hub (otherwise you will give access to all USB
device on the bus to any program).

If you do not have sufficient permissions, the test will fail and let you know.
The following instructions explain how to correctly set those permissions.

## Permissions for OT USB

The OT USB device appears with VID 0x18d1 (Google) and PID 0x503a.
Since the device will connect and disconnect several times during the test,
the only correct way to set the permissions is to use a udev rule.
The following rule is recommended:
```
# USB device under test: uses Google as VID and a Google allocated PID
ACTION=="add|change", SUBSYSTEM=="usb|tty", ATTRS{idVendor}=="18d1", ATTRS{idProduct}=="503a", MODE="0666"
```

## Permissions for the hub

The hub changes a lot less frequency than OT USB. Furthermore, most hubs do not have unique serial numbers,
and it is common for all hubs in a system to have the same VID and PID. For this reason, the recommended
way to set the hub permission is to set it manually. Doing so is a two step process:
- identify the hub,
- set the permission.

### Identifying the hub

You need to identify the bus and addres of the hub.
The simplest option is to run a test, let it fail and use the error message to get the path.
For example, running `//sw/device/tests:usbdev_deep_disconnect_test_fpga_cw310_sival_rom_ext` with
the wrong permissions will lead the following error:
```
[2025-07-10T11:59:59.430Z INFO  usbdev_suspend] waiting for device...
[2025-07-10T11:59:59.958Z INFO  usbdev_suspend] device found at bus=1 address=35
[2025-07-10T11:59:59.958Z INFO  usbdev_suspend] parent hub at bus=1, address=2, port numbers=[2]
[2025-07-10T11:59:59.958Z INFO  usbdev_suspend] device under test is on port 3
361:Finished test usbdev_suspend: Err(for this test, you need to make sure that the program has sufficient permissions to access the hub
```
The important line is:
```
[2025-07-10T11:59:59.958Z INFO  usbdev_suspend] parent hub at bus=<BUS>, address=<ADDR>, port numbers=<PORTS>
```
From this, we now know the bus and address of the hub.

### Setting the permissions

Once you know the bus and address of the device, run as root:
```bash
chmod 0666 /dev/bus/usb/<BUS>/<ADDR>
```
Note that bus is usually 0 padded to three characters, and the address to 2 characters.
