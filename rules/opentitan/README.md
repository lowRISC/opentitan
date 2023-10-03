# OpenTitan binary and test rules

The bazel rules defined in `//rules/opentitan/...` define how to build and test C and C++ binaries on the OpenTitan platform.
The test rules also permit dispatching test binaries/images produced by other languages or rule sets.

## Execution Environments

A core concept of the new rule structure is that of an execution environment (or **exec_env**). An execution environment is a unique hardware and software configuration.
Our exec\_envs include the `sim_verilator`, `sim_dv` and `fpga_cw310` environments (among others).
In addition to simply referring to the simulation or emulation platforms, the exec\_envs also include the ROM, OTP configuration and linker maps for a given environment.
For example, the `fpga_cw310_test_rom` environment is used to execute test programs on the CW310 board with the test program linked in flash memory at the ROM\_EXT stage and executed after the `test_rom`.
There may be several additional environments for the `fpga_cw310` that execute the test program under different conditions (ie: under the real ROM or under the ROM\_EXT).

An exec\_env defines everything about building and dispatching testing binaries for that environment.
In addition to the resources needed to build and dispatch binaries (e.g. the test\_rom, linker scripts, signing keys, etc), the exec\_env also supplies some starlark functions to help the various environments perform the build and test actions.

- Building
  - An exec\_env-specific provider, such as `Cw310BinaryInfo` or `SimVerilatorBinaryInfo`.
  - An exec\_env-specific `transform` function that converts binaries into the environment's required form (e.g. `vmem` files for DV or Verilator).
- Testing
  - An exec\_env-specific `test_dispatch` function that configures the test environment and dispatches the binary to that environment.

The exec\_envs are provided to the `opentitan_binary` and `opentitan_test` rules in order to allow them to perform their function.

## The `opentitan_binary` rule

The `opentitan_binary` rule is very similar to bazel's built-in `cc_binary` rule: it accepts a list of sources, dependencies and other compiler configuration parameters and produces a linked binary.
Unlike the built-in `cc_binary`, the `opentitan_binary` rule transitions the C toolchain to the opentitan platform and accepts a list of exec\_envs describing for which targets to build binaries.

**Example: building a binary for 3 exec\_envs**
```python
opentitan_binary(
    name = "hello_world",
    srcs = ["hello_world.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:sim_dv",
        "//hw/top_earlgrey:sim_verilator",
    ],
    deps = [
        ":hello_world_lib",
        "//sw/device/lib/base:mmio",
    ],
)
```

The `opentitan_binary` rule builds and links the binary for each provided exec\_env.
The rule emits several providers which are meant to be consumed by downstream rules.
These include:
- A per-exec\_env provider (ie: `Cw310BinaryInfo`).
- A `DefaultInfo` provider with the default binary form as specified by each exec\_env.
- An `OutputGroupInfo` containing a field for every file produced in the build.
  These fields are of the form `{exec_env_name}_{artifact_type}`.
For example,
  `fpga_cw310_binary`, `fpga_cw310_mapfile`, `fpga_cw310_disassembly`, etc.

Because the `opentitan_binary` rule emits several providers, any rule that accepts the outputs of `opentitan_binary` must be prepared to deal with the providers it emits.
You can use a `filegroup` to capture individual files from the `OutputGroupInfo` provider should you need to provide a file to a rule that does not understand the per-exec\_env providers.


## The `opentitan_test` rule

The `opentitan_test` rule is actually a macro exported by `defs.bzl`.
There is a real `_opentitan_test` rule in `cc.bzl`, but users are expected to use the macro.
The reason for using a macro is to instantiate an individual test rule per exec\_env so that tests can be filtered by rule name or test tags.

Like the binary rule, the test rule builds and links a binary, but then dispatches that binary according to the exec\_env-specific dispatch function and the test parameters in the `exec_env`.

**Example: instantiating a test for 3 exec_envs**
```python

opentitan_test(
    name = "uart_smoketest",
    srcs = ["uart_smoketest.c"],
    cw310 = cw310_params(timeout = "long"),
    exec_env = {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:sim_dv": None,
        "//hw/top_earlgrey:sim_verilator": None,
    },
    deps = [
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/arch:device",
        "//sw/device/lib/base:mmio",
        "//sw/device/lib/dif:uart",
        "//sw/device/lib/runtime:hart",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)
```

The test macro will instatiate individual tests for each exec\_env and name the bazel targets with the "basename" of the exec\_env.
In the example above, the tests will be:
- `uart_smoketest_fpga_cw310_test_rom`
- `uart_smoketest_sim_dv`
- `uart_smoketest_sim_verilator`

While the binary rule accepts a list of exec\_envs, the test macro requires a dictionary.
This is because tests can specify additional parameters via a params block (ie: `cw310_params(...)`). A dict value of `None` instructs the macro to fetch the params block from the default-named argument for the exec\_env (ie: the `fpga_cw310` exec\_env gets it's param block from the `cw310` parameter).
Any other dict str-value instructs the macro to find a parameter with the same name as the value.
This allows us to dispatch a test to multiple `fpga_cw310_...` exec\_envs with different parameter blocks (as needed).
