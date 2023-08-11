# OpenTitanTool

The OpenTitanTool is a CLI tool for interacting with an OpenTitan device via the various platforms available for development.

Operations supported by OpenTitanTool include:

* Flashing an OpenTitan bitstream to an FPGA board.
* Bootstrapping (flashing) software onto a device.
* Connecting to a device's console.
* Manipulating a device's GPIO pins, particularly for "[strapping][]".

## Building

OpenTitanTool is written in Rust and built using Bazel.
It is used throughout the OpenTitan repository for executing tests.

To build and run the tool manually:

```sh
bazel build //sw/host/opentitantool
bazel run //sw/host/opentitantool -- help
```

## Configuration

OpenTitanTool reads additional CLI arguments from the file at `$HOME/.config/opentitantool/config`.

[strapping]: https://opentitan.org/book/hw/ip/pinmux/doc/theory_of_operation.html?highlight=strapping#strap-sampling-and-tap-isolation
