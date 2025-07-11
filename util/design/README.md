# Design-related Tooling Scripts

## OTP Memory Map Translation Script

The OTP_CTRL is generated via ipgen, and most of the templates depend exclusively on a OTP memory map.
Each top that uses OTP has a memory map Hjson configuration file located at hw/top_<topname>/data/otp/otp_ctrl_mmap.hjson.

The `gen-otp-mmap.py` script can also be used to translate the OTP memory map definition Hjson file into documentation and SV package collateral.

```console
$ cd ${PROJ_ROOT}
$ ./util/design/gen-otp-mmap.py --topname <mytop>
```

The `--topname` switch is mandatory and is used to select the given topname's hjon configuration file.
The seed value used to generate OTP-related random netlist constants can optionally be overridden with the `--seed` switch when calling the script directly.
Otherwise that seed value is taken from the Hjson file, or generated on-the-fly if the Hjson file does not contain a seed.

## Life Cycle State Encoding Generator

The `gen-lc-state-enc.py` script is used to generate the redundant life cycle state encoding and print the constants and type definitions into the life cycle state package.
The life cycle definition file for top_earlgrey is currently located at `hw/ip/lc_ctrl/data/lc_ctrl_state.hjson`.

The script can either be invoked via the makefile
```console
$ cd ${PROJ_ROOT}
$ make -C hw lc-state-enc

```

or directly using the command

```console
$ cd ${PROJ_ROOT}
$ ./util/design/gen-lc-state-enc.py
```

The seed value used for generating life-cycle-state-related random netlist constants can optionally be overridden with the `--seed` switch when calling the script directly.
Otherwise that seed value is taken from the Hjson file, or generated on-the-fly if the Hjson file does not contain a seed.

## OTP Preload Image Generator

The OTP preload image generation tool builds on top of the memory map and life cycle state generation Python classes in order to transform a memory image configuration into a memory hexfile that can be used for OTP preloading in simulation and FPGA emulation runs.
The generated hexfile is compatible with the Verilog `$readmemh` command.

OTP image configurations are defined using hjson objects. Currently there are
two ways to build images:

1. Pre-built OTP image overlays defined in hjson. These is the approach
   currently used in most DV test cases.
2. Dynamically built OTP image overlays defined in [Bazel](#bazel). This is the
   approach currently used in FPGA and Silicon Validation (SiVal) targets.

### Bazel

#### OTP HJSON Map

OTP image overlays are first defined using the `otp_json` Bazel rule. The
following example shows the definition of a `SECRET2` partition configuration:

```python
otp_json(
    name = "otp_json_secret2_unlocked",
    partitions = [
        otp_partition(
            name = "SECRET2",
            items = {
                "RMA_TOKEN": "<random>",
                "CREATOR_ROOT_KEY_SHARE0": "<random>",
                "CREATOR_ROOT_KEY_SHARE1": "<random>",
            },
            lock = False,
        ),
    ],
)
```

See `//rules/otp.bzl` for additional documentation on additional parameters
available in the `otp_json` rule.

#### OTP Image

An OTP image is a collection of OTP JSON files used to create an OTP image.
An OTP can have multiple `otp_json` dependencies. Each dependency has the
ability of override the values of the previous dependency, so the order in
which these are listed is important.

```python
# Represents a device in DEV state with the SECRET0 and SECRET1 partitions in
# locked state. SECRET2 partition is unlocked.
otp_image(
    name = "img_dev_individualized",
    src = ":otp_json_dev",
    overlays = [
        ":otp_json_secret0",
        ":otp_json_secret1",
    ] + STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS,
)
```

In this example, the `src` attribute points to the baseline OTP JSON
configuration, and the list of overlay dependencies are applied in order
of precedence in the `overlays` attribute.

The `STD_OTP_OVERLAYS_WITHOUT_SECRET_PARTITIONS` definition imported from
`//rules:otp.bzl` declares a list of `otp_json` targets that are used
as overlays. There are other list of predefined overlays that are used
throughout the code base.

### FPGA Integration

See [FPGA bitstreams](../../hw/bitstream/README.md) documentation for more details.

### DV Flow

The OTP memory image configuration file is basically an Hjson file that lists the names and corresponding values of items defined in the OTP memory map definition.
Further, since the life cycle state is stored in OTP, the image generator script also supports generating the correct life cycle state encodings.
To that end, the desired life cycle state name can be declared in the image configuration file, and the generator script looks up and assigns the correct netlist constants.

The following snippet shows a memory image configuration that puts the device into the `DEV` life cycle state, and that defines the SECRET2 partition items and locks down the partition:
```
{
    // Seed to be used for generation of partition randomized values.
    // Can be overridden on the command line.
    seed: 01931961561863975174

    // The partition and item names must correspond with the OTP memory map.
    partitions: [
        {
            name:  "SECRET2",
            // If True, a digest will be calculated for this partition.
            // Note that this only applies to partitions with a hardware digest.
            lock:  "True",
            items: [
                {
                    name:  "RMA_TOKEN",
                    // This item is assigned is a fixed Hex value
                    value: "0x9cfbd7383959a62a4438bc468d76eed6 ",
                }
                {
                    name:  "CREATOR_ROOT_KEY_SHARE0",
                    // This item will be assigned a random value, based on the seed above.
                    value: "<random>",
                }
                {
                    name:  "CREATOR_ROOT_KEY_SHARE1",
                    // This item will be assigned a random value, based on the seed above.
                    value: "<random>",
                }
            ],
        }
        {
            name:  "LIFE_CYCLE",
            // Can be one of the following strings:
            // RAW, TEST_UNLOCKED0-3, TEST_LOCKED0-2, DEV, PROD, PROD_END, RMA, SCRAP
            state: "DEV",
            // Can be either "RAW", or any number from 1 to 16.
            count: "5"
        }
    ]
}
```

Common example configuration files that can be used for simulation and emulation are checked in under `hw/top_earlgrey/data/otp`, e.g. `hw/top_earlgrey/data/otp/otp_ctrl_img_dev.hjson` which provisions all buffered partitions and puts the device into the `DEV` life cycle.

Note that the preload image generator script automatically scrambles secret partitions, computes digests of locked partitions using the PRESENT cipher, and computes the OTP ECC bits.

The OTP preload image generator expects at least one main image configuration file to be specified with the `--img-cfg` switch, for example:
```console
$ cd ${PROJ_ROOT}
$ ./util/design/gen-otp-img.py --img-cfg hw/top_earlgrey/data/otp/otp_ctrl_img_dev.hjson \
                               --out otp-img.mem
```

Additional configuration files can be added using the `--add-cfg` switch.
The switch can be specified multiple times, and the configuration files are processed in the order they are specified.
This allows to incrementally "patch in" additional data, if needed.

For example, this can be used to patch in additional software configuration data, specified in an additional file `otp_ctrl_img_sw_cfg.hjson` that looks as follows (it is also possible to split the individual items into their own files):
```
{
   // The partition and item names must correspond with the OTP memory map.
    partitions: [
        {
            name:  "CREATOR_SW_CFG",
            items: [
                {
                    name:  "CREATOR_SW_CFG_CONTENT",
                    value: "0x0", // data to be put into this partition
                }
                {
                    name:  "CREATOR_SW_CFG_DIGEST",
                    value: "0x0", // 64bit digest to be written to this partition
                }
            ],
        },
        {
            name:  "OWNER_SW_CFG",
            items: [
                {
                    name:  "OWNER_SW_CFG_CONTENT",
                    value: "0x0", // data to be put into this partition
                }
                {
                    name:  "OWNER_SW_CFG_DIGEST",
                    value: "0x0", // 64bit digest to be written to this partition
                }
            ],
        }
    ]
}
```

The generator script call would then look as follows:
```console
$ cd ${PROJ_ROOT}
$ ./util/design/gen-otp-img.py --img-cfg hw/top_earlgrey/data/otp/otp_ctrl_img_dev.hjson \
                               --add-cfg otp_ctrl_img_sw_cfg.hjson \
                               --out otp-img.mem
```

## ECC Generator Tool

The `./util/design/secded_gen.py` script is used to create C and SV artifacts related to SECDED.
It uses the `./util/design/data/secded_cfg.hjson` file to determine the secded type and widths supported.
It creates artifacts to implement and emulate the encode and decode operations for each supported secded, and to instantiate these modules in parameterized contexts.
The artifacts are generated for each type and width, and include the following:

- RTL for decoder and encoders for each supported secded type and width
- Testbench, assertions, bind, and core files to be used in the formal verification flow
- C code and header files to emulate secded encoding and decoding
- SV package with relevant types and code to emulate each encoder and decoder
- SV types and constant functions that can be used in generate blocks
- Macros to instantiate encode and decode prims driven by parameters using case generates

The functions and macros to be used for parameterized cases have comments that explain their use.
These functions are in `hw/ip/prim/rtl/prim_secded_pkg.sv`, and the macros in `hw/ip/prim/rtl/prim_secded_inc.svh`.
An example of how to parameterize secded is in `hw/ip/otp_macro/rtl/otp_macro.sv`.

## LFSR Coefficient Generator Tool

The `get-lfsr-coeffs.py` script is used to fetch a list of primitive polynomials for Galois and Fibonacci type LFSRs.

By default, the coefficients are downloaded from [https://users.ece.cmu.edu/~koopman/lfsr/](https://users.ece.cmu.edu/~koopman/lfsr/).
The script downloads text files containing the first 100 primitive polynomials for LFSR widths ranging from 4 to 64 and places them into a temporary folder.
The script also produces an output file containing a SystemVerilog template with LFSR polynomials for widths 4 to 64.
This template contains exactly one polynomial for each LFSR width, which is always the first polynomial listed in the corresponding file.

When used with the `--pdf <pdf file>` option, the script outputs polynomials extracted from the Xilinx application note.
To run this option, the user first needs to download the Xilinx application note from [https://docs.xilinx.com/v/u/en-US/xapp052](https://docs.xilinx.com/v/u/en-US/xapp052).
The produced output file contains a SystemVerilog template with LFSR polynomials for widths ranging from 3 to 168.

## LFSR Seed Generator Tool

The `gen-lfsr-seed.py` script creates a SystemVerilog template for LFSR parameters, i.e. width, default seed and the permutation of the output bits.
Switch `-w` is used to specify the LFSR width.
The other two parameters are generated randomly.
The seed for the underlying pseudo-random number generator can optionally be passed using the `--seed` parameter.
An optional name prefix can be specified using the `--prefix` parameter.

For example, running the following command:

```console
$ cd ${PROJ_ROOT}
$ ./util/design/gen-lfsr-seed.py -w 8 --prefix "my"
```
produces the following parameters for an 8-bit LFSR.

```
------------------------------------------------
| COPY PASTE THE CODE TEMPLATE BELOW INTO YOUR |
| RTL CODE, INCLUDING THE COMMENT IN ORDER TO  |
| EASE AUDITABILITY AND REPRODUCIBILITY.       |
------------------------------------------------


// These LFSR parameters have been generated with
// $ ./util/design/gen-lfsr-seed.py --width 8 --seed 3816832368 --prefix "my"
parameter int myLfsrWidth = 8;
typedef logic [myLfsrWidth-1:0] my_lfsr_seed_t;
typedef logic [myLfsrWidth-1:0][$clog2(myLfsrWidth)-1:0] my_lfsr_perm_t;
parameter my_lfsr_seed_t RndCnstmyLfsrSeedDefault = {
  8'h3a
};
parameter my_lfsr_perm_t RndCnstmyLfsrPermDefault = {
  24'hde9622
};
```

## Sparse FSM State Encoding Tool

TODO

## KECCAK Coefficient Generation Tool

TODO
