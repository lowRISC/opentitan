# CoreMark Benchmark

## Running CoreMark

To build and run CoreMark on the CW340:

```sh
bazel test --test_tag_filters=cw340 \
//third_party/coremark/top_earlgrey:coremark_test
```

To build and run CoreMark on Verilator:

```sh
bazel test --test_tag_filters=verilator \
//third_party/coremark/top_earlgrey:coremark_test
```

## CoreMark Options

The BUILD file is hardcoded to give a PERFORMANCE_RUN with
TOTAL_DATA_SIZE=2000. These settings are required for reportable CoreMark
figures. If you wish to use other options, please modify
`third_party/coremark/top_earlgrey/BUILD` appropriately. See the CoreMark
[README](https://github.com/eembc/coremark/blob/main/README.md) for
further information on the possibilities.
