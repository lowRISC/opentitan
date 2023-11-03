# Cryptotest Framework

Cryptotest is a unified framework for injecting testvectors and exercising the cryptolib API to verify functionality, perform compliance testing, and enable instrumentation for penetration testing.

## Overview

The cryptotest framework allows the host to send commands to the device over UART.
The device runs firmware that listens for these commands and performs the corresponding operations before sending the results back to the host.
This communication is enable by uJSON which uses the C preprocessor to generate serialize/deserialize functions for each command in C and Rust.

## Code Organization

There are four components:

1. uJSON command definitions (defined in C header files)
1. Auto-generated uJSON serialize/deserialize functions (generated during the Bazel build)
1. Device-side command listener firmware
1. Host-side test harness program that uses the commands

These components are organized as follows:

- `sw/device/tests/crypto/cryptotest`
  - `firmware`: on-device command listener firmware
  - `json`: uJSON definitions of the cryptotest commands
- `sw/host/cryptotest/ujson_lib`: Rust stubs to import the generated uJSON Rust functions and collect them into a single library.
- `sw/host/tests/crypto`: host-side test harnesses for each test

## Adding a New Command

This section describes the process for adding a new command to the framework.
Adding a new command requires first defining a uJSON representation for it.
Then, on the device side, a handler must be added to the device firmware to listen for the command.
On the host side, the generated uJSON functions need to be added to the Cryptotest's Rust uJSON library.
Lastly, a test harness can be written that uses the new command.

The following snippets demonstrate adding a new command, `ExampleCommand`, alongside existing `Aes` and `Rsa` commands.

### Define a uJSON Command

Define the top-level uJSON command in `sw/device/tests/crypto/cryptotest/json/commands.h`.
If the command has subcommands or additional parameters, define them in another file in the same directory.
See `sw/device/lib/ujson/example.h` for a uJSON example.

**sw/device/tests/crypto/cryptotest/json/commands.h**

```c
#define COMMAND(_, value) \
    value(_, Aes) \
    value(_, Rsa) \
    value(_, ExampleCommand)
UJSON_SERDE_ENUM(CryptotestCommand, cryptotest_cmd_t, COMMAND);
```

**sw/device/tests/crypto/cryptotest/json/example_command.h**

```c
#include "sw/device/lib/ujson/ujson_derive.h"

// Defining two subcommands, A and B, to the top-level Example command
#define EXAMPLE_SUBCOMMAND(_, value) \
    value(_, A) \
    value(_, B)
UJSON_SERDE_ENUM(ExampleSubcommand, example_subcommand_t, EXAMPLE_SUBCOMMAND);
```

### Add Device-Side Firmware Handler

Register a handler in the device firmware: `sw/device/tests/crypto/cryptotest/firmware/firmware.c`.

**sw/device/tests/crypto/cryptotest/firmware/firmware.c**

```c
switch (cmd) {
  case kCryptotestCommandAes:
    RESP_ERR(uj, handle_aes(uj));
    break;
  case kCryptotestCommandRsa:
    RESP_ERR(uj, handle_rsa(uj));
    break;
  case kCryptotestCommandExample:
    RESP_ERR(uj, handle_example(uj));
    break;
  default:
    LOG_ERROR("Unrecognized command: %d", cmd);
    RESP_ERR(uj, INVALID_ARGUMENT());
}
```

Now, add the handler code in another file in the same directory.

**sw/device/tests/crypto/cryptotest/firmware/example.c**

```c
status_t handle_example(ujson_t *uj) {
  example_subcommand_t cmd;
  TRY(ujson_deserialize_example_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kExampleSubcommandA:
      return handle_subcommand_a(uj);
      break;
    case kExampleSubcommandB:
      return handle_subcommand_b(uj);
      break;
    default:
      LOG_ERROR("Unrecognized Example subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
```

### Add to Host-Side Rust Library

Add a Rust stub to `sw/host/cryptotest/ujson_lib` to import the uJSON-generated serialize/deserialize functions for the new command.

**sw/host/cryptotest/ujson_lib/src/example.rs**

```rust
include!(env!("example_commands_path"));
```

**sw/host/cryptotest/ujson_lib/BUILD**

```rust
ujson_rust(
    name = "example_commands_rust",
    srcs = ["//sw/device/tests/crypto/cryptotest/json:example_commands"],
)

rust_library(
    name = "cryptotest_commands",
    ...
    rustc_env = {
        "commands_loc": "$(execpath :commands_rust)",
        "example_commands_loc": "$(execpath :example_commands_rust)",
        ...
    },
    ...
)
```

### Write Test Harness

To write the test itself, create a host-side test harness in rust in `sw/host/tests/crypto` that sends the commands.
See `sw/host/cryptotest/tests/crypto/aes_nist_kat/src/main.rs` for an example.
