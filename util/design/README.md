# Design-related Tooling Scripts

## Life Cycle and OTP Tools

### OTP Memory Map Translation Script

The `gen-otp-mmap.py` script is used to translate the OTP memory map definition Hjson file into documentation and SV package collateral.
The memory map definition file for top_earlgrey is currently located at `hw/ip/otp_ctrl/data/otp_ctrl_mmap.hjson`.

The script can either be invoked via the makefile
```console
$ cd ${PROJ_ROOT}
$ make -C hw otp-mmap

```

or directly using the command

```console
$ cd ${PROJ_ROOT}
$ ./util/design/gen-otp-mmap.py
```

The seed value used for generating OTP-related random netlist constants can optionally be overridden with the `--seed` switch when calling the script directly.
Otherwise that seed value is taken from the Hjson file, or generated on-the-fly if the Hjson file does not contain a seed.

### Life Cycle State Encoding Generator

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

### OTP Preload Image Generator

The OTP preload image generation tool builds on top of the memory map and life cycle state generation Python classes in order to transform a memory image configuration into a memory hexfile that can be used for OTP preloading in simulation and FPGA emulation runs.
The generated hexfile is compatible with the Verilog `$readmemh` command.

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

Common example configuration files that can be used for simulation and emulation are checked in under `hw/ip/otp_ctrl/data`, e.g. `hw/ip/otp_ctrl/data/otp_ctrl_img_dev.hjson` which provisions all buffered partitions and puts the device into the `DEV` life cycle.

Note that the preload image generator script automatically scrambles secret partitions, computes digests of locked partitions using the PRESENT cipher, and computes the OTP ECC bits.

The OTP preload image generator expects at least one main image configuration file to be specified with the `--img-cfg` switch, for example:
```console
$ cd ${PROJ_ROOT}
$ ./util/design/gen-otp-img.py --img-cfg hw/ip/otp_ctrl/data/otp_ctrl_img_dev.hjson \
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
$ ./util/design/gen-otp-img.py --img-cfg hw/ip/otp_ctrl/data/otp_ctrl_img_dev.hjson \
                               --add-cfg otp_ctrl_img_sw_cfg.hjson \
                               --out otp-img.mem
```

## ECC Generator Tool

TODO

## LFSR Coefficient Generator Tool

The `get-lfsr-coeffs.py` script is used to fetch a list of primitive polynomials for Galois and Fibonacci type LFSRs.

Galois coefficients are downloaded from [https://users.ece.cmu.edu/~koopman/lfsr/](https://users.ece.cmu.edu/~koopman/lfsr/).
The script downloads text files containing the first 100 primitive polynomials for LFSR widths ranging from 4 to 64 and places them into a temporary folder.
The script also produces an output file containing a SystemVerilog template with LFSR polynomials for widths 4 to 64.
This template contains exactly one polynomial for each LFSR width, which is always the first polynomial listed in the corresponding file.

When used with the `--fib <pdf file>` option, the script outputs polynomials for the XNOR Fibonacci-type LFSR.
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
| RTL CODE, INLUDING THE COMMENT IN ORDER TO   |
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
