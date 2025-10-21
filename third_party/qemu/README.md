# QEMU

For instructions on setting up QEMU for local development and troubleshooting steps, see the [setup guide](./setup.md).

## Test parameters

Tests with a `sim_qemu_*` execution environment can be further configured by adding `qemu_params` to the test target.
The currently supported parameters are:

* `icount` (`int`): scale for Ibex's reported execution speed (`1GHz >> icount`) (defaults to 6).
* `globals` (`dict[str, str]`): global properties for the QEMU machine.
* `traces` (`[str]`): globs of QEMU traces to enable for debugging purposes.
* `qemu_args` (`[str]`): additional command line flags to pass to QEMU.

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
