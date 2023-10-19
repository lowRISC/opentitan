# OTP Build and Test Infrastructure

OTP image configurations are defined using hjson objects. Currently there are
two ways to build images:

1. Pre-built OTP image overlays defined in hjson. These is the approach
   currently used in most DV test cases.
2. Dynamically built OTP image overlays defined in [Bazel](#bazel). This is the
   approach currently used in FPGA and Silicon Validation (SiVal) targets.

## Bazel

See `//hw/ip/otp_ctrl/data/BUILD` for detailed references on the rules
described below.

### OTP HJSON Map

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

### OTP Image

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

See [FPGA bitstreams](../../../bitstream/README.md) documentation for more details.
