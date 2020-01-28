# Device-specific Symbols

This subtree provides the header `device.h`, which contains declarations for symbols that represent device-specific information, like the clock frequency.

## Using `device.h`

When a library needs to make use of device-specific information, it should only pull in the header itself, and not depend directly on any of the libraries in this directory.
Instead, the symbols' definitions will be provided at link time by the executable's build rule, which should depend on exactly one of the libraries in this directory (failing to do so is Undefined Behavior).

If an executable is designed to be device-independent (i.e., obtains all of its device-specific information from `device.h`), the following Meson template may be used to generate executable targets for most devices:
```meson
foreach device_name, device_lib : sw_lib_arch_core_devices
  executable(
    'my_binary_' + device_name,
    sources: [...],
    dependencies: [
      ...,
      device_lib,
    ],
  )
  
  # ...
endforeach
```
Note that this will not generate targets for some specialized devices, such as DV testbenches.

## Adding a new device

It is sometimes necessary to add a new device. The following considerations should be taken:
- Make sure to add a new entry to `device_type_t`. Multiple variants of the same device (e.g., a DV testbench with different settings) may use the same `device_type_t`.
- If your device is not "specialized" (i.e., not a DV testbench), it should be added to `sw_lib_arch_core_devices`.
- Users should only ever link in exactly one target from this directory.
  If multiple devices share a lot of the same symbol definitions, those can be factored into a separate `.c` file, but the targets should, ultimately, look like this:
  ```meson
  sw_lib_arch_my_dev1 = declare_dependency(
    link_with: static_library(
      'my_dev1',
      sources: [
        'device_my_dev_base.c'
        'device_my_dev1.c'
      ],
    ),
  )

  sw_lib_arch_my_dev2 = declare_dependency(
    link_with: static_library(
      'my_dev2',
      sources: [
        'device_my_dev_base.c'
        'device_my_dev2.c'
      ],
    ),
  )
  ```
- Your device may be specialized and require symbols that are straight-up not meaningful on other devices.
  These symbols should be specified in a separate header in this subtree, and targets that use that header should not be declared using the `sw_lib_arch_core_devices` shorthand above.