# Hardware trust

Reliable trust in a device's hardware is the basis of a growing set of features,
for example remote key provisioning.

## `libhwtrust`

The library for handling, inspecting and validating data realted to the hardware
root-of-trust and the features that rely on it is `libhwtrust`.

## `hwtrust`

There is a command-line utility that provides easy access to the logic in
`libhwtrust` called `hwtrust`.

Build it as part of Android with `m hwtrust` and run `hwtrust --help` to see a
list of its functions.

Alternatively, use Cargo by running `cargo run -- --help` in this directory to
build and run the utility. If the Cargo build has errors, please help to keep it
working by sending fixes or reporting the problem. Building as part of Android
should always work as a fallback.

### Verifying DICE chains

`hwtrust` can be used to validate that a DICE chain is well-formed and check
that the signatures verify correctly. To do so, place the CBOR-encoded DICE
chain in a file, e.g. `chain.bin`, then call the tool.

```shell
hwtrust dice-chain chain.bin
```

The exit code is zero if the chain passed verification and non-zero otherwise.

### Verifying Factory Certificate Signing Requests

The `rkp_factory_extraction_tool` is used in the manufacturing process to capture
a "CSR" that contains a full DICE chain and other device properties. The `factory-csr`
subcommand parses and validates the output of `rkp_factory_extraction_tool`.


```shell
hwtrust factory-csr csr.json
```
