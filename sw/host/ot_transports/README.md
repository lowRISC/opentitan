# OpenTitan transports

The crates under this directory each implement a specific transport telling OpenTitanLib on how to connect to the hardware (actual or simulated).

They use `inventory` to register themselves to OpenTitanLib, so most users do not need to interact with it directly (unless you need a type from it).
However, users would need to link with them so the transports are actually registered.

Currently, this requires the user to have
```rust
extern crate ot_transport_hyperdebug;
```
which explicitly tells rustc that you need to link against it.
If https://github.com/rust-lang/rust/issues/111302 is stable, this step can potentially be replaced by Bazel.
If you depend on `//sw/host/opentitanlib` target, this step is already done for you.
