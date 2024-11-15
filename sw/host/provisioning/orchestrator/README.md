# Provisioning Orchestrator

The provisioning orchestrator is a Python script that enables running benchtop
provisioning flows for Earlgrey chips. The script can be run in two different
ways:
1. via Bazel, or
2. directly.

## Running with Bazel

To run on an CW310 FPGA for testing, run:
```
bazel run \
  --//hw/bitstream/universal:env=//hw/top_earlgrey:fpga_hyper310_rom_with_fake_keys \
  --//hw/bitstream/universal:otp=//hw/ip/otp_ctrl/data/earlgrey_skus/sival:otp_img_test_unlocked0_manuf_empty \
  //sw/host/provisioning/orchestrator/src:orchestrator -- \
    --sku-config=$(pwd)/sw/host/provisioning/orchestrator/configs/skus/sival.hjson \
    --test-unlock-token="0x11111111_11111111_11111111_11111111" \
    --test-exit-token="0x22222222_22222222_22222222_22222222" \
    --rma-unlock-token="0x33333333_33333333_33333333_33333333" \
    --fpga=hyper310 \
    --non-interactive
```

To run on silicon, run:
```
bazel run \
  //sw/host/provisioning/orchestrator/src:orchestrator -- \
    --sku-config=$(pwd)/sw/host/provisioning/orchestrator/configs/skus/sival.hjson \
    --test-unlock-token=<token as a hexstring> \
    --test-exit-token=<token as a hexstring> \
    --rma-unlock-token=<token as a hexstring> \
    --non-interactive
```

## Running Directly

WIP
