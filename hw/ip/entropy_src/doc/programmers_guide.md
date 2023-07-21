# Programmer's Guide

## Initialization

To initialize the ENTROPY_SRC block, see the Device Interface Functions (DIFs) section.


## Entropy Processing

Once entropy has been prepared for delivery, it can be consumed by either hardware (CSRNG block hardware instance) or by a software interface (CSRNG software instance).

Note that when software makes frequent re-seed requests to CSRNG, any stored up entropy seeds in the final entropy FIFO will quickly consumed.
Once the FIFO is empty, subsequent entropy seed requests will have to wait the worst case latency time while new entropy is being created.


## Entropy Source Module Disable

A useful feature for the ENTROPY_SRC block is the ability to disable it in a graceful matter.
Since there exists another feature to avoid power spikes between ENTROPY_SRC and CSRNG, software needs to monitor the disabling process.
Bit 16 in the [`DEBUG_STATUS`](registers.md#debug_status) should be polled after the ENTROPY_SRC enable bits are cleared in the [`CONF`](registers.md#conf) register.
After the handshakes with CSRNG are finished, the above bit should be set and the ENTROPY_SRC block can be safely enabled again.

ENTROPY_SRC may only be disabled if CSRNG is disabled.

Disabling Entropy Source does not clear the bits in `RECOV_ALERT_STS` (see [*Handling a Recoverable Alert*](#handling-a-recoverable-alert)).


## Firmware Override / Bypass Modes

The ENTROPY_SRC block supports different ways in which firmware can observe or extract and insert entropy into the entropy flow, e.g., for validation testing or to perform additional firmware-based health tests and conditioning.

This section discusses how to enable the different modes.
For more details on the individual modes, refer to [Theory of Operations](theory_of_operation.md).

### Firmware Override - Observe

Using the firmware override function, firmware can observe post-health test entropy bits by reading from the [`FW_OV_RD_DATA`](registers.md#fw_ov_rd_data) register (observe FIFO), e.g., for validation testing.
To this end, the `otp_en_entropy_src_fw_over` input needs to be set to `kMultiBitBool8True`.
In addition, firmware has to set the `FW_OV_MODE` field in the [`FW_OV_CONTROL`](registers.md#fw_ov_control) register to `kMultiBitBool4True`.

Note that the post-health test entropy bits collected in the observe FIFO continue to flow through the hardware pipeline and may eventually reach the block hardware interface.

### Firmware Override - Extract & Insert

Using the firmware override function, firmware can extract entropy bits by reading from the [`FW_OV_RD_DATA`](registers.md#fw_ov_rd_data) register (observe FIFO), e.g., for performing additional health tests and/or firmware-based conditioning, and then insert entropy bits back into the entropy flow by writing the [`FW_OV_WR_DATA`](registers.md#fw_ov_wr_data) register.
To this end, the `otp_en_entropy_src_fw_over` input needs to be set to `kMultiBitBool8True`.
In addition, firmware has to:
1. Set the `FW_OV_MODE` field in the [`FW_OV_CONTROL`](registers.md#fw_ov_control) register to `kMultiBitBool4True`.
1. Set the `FW_OV_ENTROPY_INSERT` field in the [`FW_OV_CONTROL`](registers.md#fw_ov_control) register to `kMultiBitBool4True`.

If firmware wants to use hardware conditioning for the inserted entropy bits, it also has to:
1. Set the `FIPS_ENABLE` field in the [`CONF`](registers.md#conf) register to `kMultiBitBool4True`.
1. Set `ES_TYPE` or `ES_ROUTE` (or both) in [`ENTROPY_CONTROL`](registers.md#entropy_control) to `kMultiBitBool4False`.

It further has to set the `FW_OV_INSERT_START` field in the [`FW_OV_SHA3_START`](registers.md#fw_ov_sha3_start) register to `kMultiBitBool4True`.
Once all entropy bits have been written to the [`FW_OV_WR_DATA`](registers.md#fw_ov_wr_data) register, firmware can set `FW_OV_INSERT_START` to `kMultiBitBool4False` to trigger the hardware conditioning mechanism.

Note that if the `FW_OV_ENTROPY_INSERT` field is set to `kMultiBitBool4True`, post-health test entropy bits do NOT continue to flow through the hardware pipeline.
The observe FIFO will collect 2 kBit of contiguous entropy bits.
Any entropy bits arriving after the observe FIFO is full are being discarded.
Firmware has to read out the entire observe FIFO to restart entropy collection.
Only entropy bits inserted by firmware by writing the [`FW_OV_WR_DATA`](registers.md#fw_ov_wr_data) register may eventually reach the block hardware interface.

The `cs_aes_halt` interface that should halt CSRNG's AES while Entropy Source's SHA3 is active (to prevent power peaks) does not work when firmware inserts entropy.
In this case, SHA3 activity is controlled by software.
Thus, if power peaks are a concern, software must ensure that SHA3 is not active too frequently or not together with CSRNG's AES.

### Hardware Conditioning Bypass

Firmware can enable bypassing of the hardware conditioning inside the ENTROPY_SRC block.
To this end, firmware has to either:
- set the `ES_TYPE` and `ES_ROUTE` fields in [`ENTROPY_CONTROL`](registers.md#entropy_control) to `kMultiBitBool4True` (this causes the ENTROPY_SRC block to not pass any entropy to the block hardware interface), or
- set the `FIPS_ENABLE` field in the [`CONF`](registers.md#conf) register to `kMultiBitBool4False` to disable FIPS mode and enable the bypass or boot-time mode.

Note that in bypass or boot-time mode, health test window sizes other than 384 bits (the seed length) are currently not tested nor supported.

### Reading Entropy Output

Firmware can read the entropy output of the ENTROPY_SRC block from the [`ENTROPY_DATA`](registers.md#entropy_data) register.
To this end, the `otp_en_entropy_src_fw_read` input needs to be set to `kMultiBitBool8True`.
In addition, firmware has to:
1. Set the `ENTROPY_DATA_REG_ENABLE` field in the [`CONF`](registers.md#conf) register to `kMultiBitBool4True`.
1. Set the `ES_ROUTE` field in the [`ENTROPY_CONTROL`](registers.md#entropy_control) register to `kMultiBitBool4True`.

Note that once the field `ES_ROUTE` is set to `kMultiBitBool4True`, no entropy is being passed to the block hardware interface.
This mode is compatible with [Hardware Conditioning Bypass](#hardware-conditioning-bypass) (enabled by setting the `ES_TYPE` field in [`ENTROPY_CONTROL`](registers.md#entropy_control) to `kMultiBitBool4True`).


## Handling a Recoverable Alert

Reasons for a recoverable alert are tracked in the [`RECOV_ALERT_STS`](registers.md#recov_alert_sts) register.
Each bit gets set based on the condition in its description.
To handle a recoverable alert, go through the bits that are set and resolve the underlying problems, then write zero to each bit to clear it.
Disabling Entropy Source does not clear the bits in `RECOV_ALERT_STS`.


## Error conditions

Need to alert the system of a FIFO overflow condition.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_entropy_src.h)
