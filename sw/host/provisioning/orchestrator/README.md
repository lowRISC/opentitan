# Provisioning Orchestrator

The provisioning orchestrator is a Python script that enables running benchtop
provisioning flows for Earlgrey chips. The script can be run in two different
ways:
1. via Bazel, or
2. directly.

## Running with Bazel

To run on an FPGA for testing, run:

```
# Select either cw340 or cw310
export FPGA_TARGET=hyper310
bazel run \
  --//hw/bitstream/universal:env=//hw/top_earlgrey:fpga_${FPGA_TARGET}_rom_with_fake_keys \
  --//hw/bitstream/universal:otp=//hw/top_earlgrey/data/otp/emulation:otp_img_test_unlocked0_manuf_empty \
  //sw/host/provisioning/orchestrator/src:orchestrator -- \
    --sku-config=$(pwd)/sw/host/provisioning/orchestrator/configs/skus/sival.hjson \
    --test-unlock-token="0x11111111_11111111_11111111_11111111" \
    --test-exit-token="0x22222222_22222222_22222222_22222222" \
    --fpga=${FPGA_TARGET} \
    --non-interactive \
    --ast-cfg-version=0 \
    --db-path=$(pwd)/provisioning.sqlite
```

To run on silicon, run:

```
bazel run \
  //sw/host/provisioning/orchestrator/src:orchestrator -- \
    --sku-config=$(pwd)/sw/host/provisioning/orchestrator/configs/skus/emulation.hjson \
    --test-unlock-token=<token as a hexstring> \
    --test-exit-token=<token as a hexstring> \
    --non-interactive \
    --db-path=$(pwd)/provisioning.sqlite
```

## Running Directly

Build the orchestrator package. This will build a package with all SKU
dependencies.

```
export FPGA_TARGET=hyper310
bazel build \
  --//hw/bitstream/universal:env=//hw/top_earlgrey:fpga_${FPGA_TARGET}_rom_with_fake_keys \
  --//hw/bitstream/universal:otp=//hw/top_earlgrey/data/otp/emulation:otp_img_test_unlocked0_manuf_empty \
  //sw/host/provisioning/orchestrator/src:orchestrator.zip
```

To run the packaged orchestrator script:

```
export ORCHESTRATOR_RUN_DIR=/tmp/orchestrator
mkdir -p ${ORCHESTRATOR_RUN_DIR}
cd ${ORCHESTRATOR_RUN_DIR}
cp ${REPO_TOP}/bazel-bin/sw/host/provisioning/orchestrator/src/orchestrator.zip .

export ORCHESTRATOR_ZIP="${ORCHESTRATOR_RUN_DIR}/orchestrator.zip"
unzip ${ORCHESTRATOR_ZIP} "runfiles/sc_hsm/*"

# Run tool. The path to the --sku-config parameter is relative to the
# workspace root.
export FPGA_TARGET=hyper310
python3 ${ORCHESTRATOR_ZIP} \
  --sku-config=sw/host/provisioning/orchestrator/configs/skus/emulation.hjson \
  --test-unlock-token="0x11111111_11111111_11111111_11111111" \
  --test-exit-token="0x22222222_22222222_22222222_22222222" \
  --fpga=${FPGA_TARGET} \
  --non-interactive \
  --db-path=provisioning.sqlite
```
