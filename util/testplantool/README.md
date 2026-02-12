# Testplantool

A tool to manipulate and extract information from the testplans.

## Exporting a csv for the top earlgrey:
```sh
python util/testplantool/testplantool.py export-csv \
hw/top_earlgrey/data/chip_testplan.hjson /tmp/earlgrey.csv
```
or with bazel:
```sh
bazel run util/testplantool -- export-csv \
$(pwd)/hw/top_earlgrey/data/chip_testplan.hjson /tmp/earlgrey.csv
```

## Query testpoints
With DEV lifecycle:
```sh
bazel run util/testplantool -- query \
$(pwd)/hw/top_earlgrey/data/chip_testplan.hjson --lc-state="DEV"
```
With PROD lifecycle and `aes` in the name:
```sh
bazel run util/testplantool -- query \
$(pwd)/hw/top_earlgrey/data/chip_testplan.hjson --name=".*aes.*" --lc-state="DEV"
```

With PROD lifecycle and `aes` in the name, only add the fields `name` and `bazel` to the output:
```sh
bazel run util/testplantool -- query \
$(pwd)/hw/top_earlgrey/data/chip_testplan.hjson --name=".*aes.*" \
--lc-state="DEV" --fields="name,bazel"
```
Available testpoint filters:
    --name: Regex to match testpoint name.
    --stage: Regex to match dv stage.
    --si-stage: Regex to match SiVal stage.
    --lc-state: Regex to match life-cycle stage.

fields filters:
    --fields: Comma separated list of fields that should be in the output.

## Exporting bazel testsuites:
Based on SiVal stage
```sh
bazel run util/testplantool -- export-testsuite \
$(pwd)/hw/top_earlgrey/data/chip_testplan.hjson $(pwd)/sw/device/tests/sival/BUILD
```

Based on `lc_state`
```sh
mkdir -p sw/device/tests/lc_state
bazel run util/testplantool -- export-testsuite -g "lc_state" \
$(pwd)/hw/top_earlgrey/data/chip_testplan.hjson $(pwd)/sw/device/tests/lc_state/BUILD
```
