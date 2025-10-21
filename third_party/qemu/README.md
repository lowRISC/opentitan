# QEMU

For instructions on setting up QEMU for local development and troubleshooting steps, see the [setup guide](./setup.md).

## Testing

### Test parameters

Tests with a `sim_qemu_*` execution environment can be further configured by adding `qemu_params` to the test target.
The currently supported parameters are:

* `icount` (`int`): scale for Ibex's reported execution speed (`1GHz >> icount`) (defaults to 6).
* `globals` (`dict[str, str]`): global properties for the QEMU machine.
* `traces` (`[str]`): globs of [QEMU traces](https://qemu-project.gitlab.io/qemu/devel/tracing.html) to enable for debugging purposes.
QEMU accepts different trace event patterns with support for wildcard matching with an `"*"`.
* `qemu_args` (`[str]`): additional command line flags to pass to QEMU.
* `bootstrap` (`bool`): by setting to `True`, bootstrap test firmware instead of splicing a flash image.
Mutually exclusive with specifying a custom test harness.

Example:

```python
opentitan_test(
    name = "my_test",
    exec_env = {
      "//hw/top_earlgrey:sim_qemu_rom_with_fake_keys": None,
    },
    qemu = qemu_params(
      icount = 5,
      globals = {
        "ot-aes.fast-mode": "false",
      },
      qemu_args = {
        "-s", # spawn GDB server
      },
      traces = [
        "ot_spi_device*",
      ],
    ),
    # ...
)
```

### Command-line arguments

It can often be inconvenient to manually modify test targets to contain the desired list of QEMU arguments whilst debugging.
In particular, manually adding and removing traces can quickly become unwieldy.

Instead, you can pass in arguments to QEMU as command-line arguments using the form `--qemu-arg="X"` or `--qemu-args="X Y Z"`.
The former forwards a single argument `X` to QEMU, whereas the latter forwards `X`, `Y` and `Z` each as _different_ arguments to QEMU.

For example, to manually add some traces for the USB device and alert updates whilst debugging a test, you might run:
```
./bazelisk.sh test //path_to_qemu_test:my_test --test_arg=--qemu-args="--trace ot_usbdev* --trace ot*update_alert*"
```
