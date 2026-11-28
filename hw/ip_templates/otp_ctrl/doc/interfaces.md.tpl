<%
  # Name of the partition holding FIELD_ENTROPY, if the memory map contains that item.
  field_entropy_part = next((part["name"] for part in otp_mmap["partitions"]
                             for item in part["items"] if item["name"] == "FIELD_ENTROPY"), None)
  # Name of the partition holding SECONDARY_ROOT_KEY_SHARE0/1, if the memory map contains them.
  secondary_root_key_part = next((part["name"] for part in otp_mmap["partitions"]
                                  for item in part["items"]
                                  if item["name"] == "SECONDARY_ROOT_KEY_SHARE0"), None)
  keymgr_sigs = ["keymgr_creator_root_key_o", "keymgr_creator_seed_o", "keymgr_owner_seed_o"]
  if field_entropy_part:
    keymgr_sigs.append("keymgr_field_entropy_o")
  if secondary_root_key_part:
    keymgr_sigs.append("keymgr_secondary_root_key_o")
%>\
# Hardware Interfaces

${"##"} Clocks and Resets

- `clk_i`/`rst_ni` clock the whole controller apart from the EDN interface.
  The macro interface and the life cycle controller interfaces are synchronous to `clk_i`, so the macro interface backend (`${macro_backend}` in this top) and `lc_ctrl` must be clocked and reset by the same clock and reset.
- `clk_edn_i`/`rst_edn_ni` clock the EDN interface and must be the clock and reset of the EDN.

All crossings into `clk_i` use synchronization primitives.
The EDN interface is crossed with `prim_edn_req`.
The initialization request from the power manager is synchronized with `prim_flop_2sync`.
The life cycle inputs are synchronized with `prim_lc_sync`.
The key interfaces to the ${"SRAM, OTBN and NVM" if enable_nvm_key else "SRAM and OTBN"} scramblers and the key manager outputs are synchronous to `clk_i`, and the receiving IP synchronizes them, as described below.

${"##"} Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/top_${topname}/ip_autogen/otp_ctrl/data/otp_ctrl.hjson -->
<!-- END CMDGEN -->

The OTP controller contains various interfaces that connect to other comportable IPs within OpenTitan, and these are briefly explained further below.

${"###"} EDN Interface

The entropy request interface that talks to EDN in order to fetch fresh entropy for ephemeral SRAM scrambling key derivation and the LFSR counters for background checks.
It is comprised of the `edn_o` and `edn_i` signals and follows a req / ack protocol.

See also [EDN documentation](../../../../ip/edn/README.md).

${"###"} Power Manager Interface

The power manager interface is comprised of three signals overall: an initialization request (`pwr_otp_i.otp_init`), an initialization done response (`pwr_otp_o.otp_done`) and an idle indicator (`pwr_otp_o.otp_idle`).

The power manager asserts `pwr_otp_i.otp_init` in order to signal to the OTP controller that it can start initialization, and the OTP controller signals completion of the initialization sequence by asserting `pwr_otp_o.otp_done` (the signal will remain high until reset).

The idle indication signal `pwr_otp_o.otp_idle` indicates whether there is an ongoing write operation in the Direct Access Interface (DAI) or Life Cycle Interface (LCI), and the power manager uses that indication to determine whether a power down request needs to be aborted.

Since the power manager may run in a different clock domain, the `pwr_otp_i.otp_init` signal is synchronized within the OTP controller.
The power manager is responsible for synchronizing the `pwr_otp_o.otp_done` and `pwr_otp_o.otp_idle` signals.

See also [power manager documentation](../../pwrmgr/README.md).

${"###"} Life Cycle Interfaces

The interface to the life cycle controller can be split into two functional sub-interfaces (state output and state transitions), and these are explained in more detail below.
Note that the OTP and life cycle controllers are supposed to be in the same clock domain, hence no additional signal synchronization is required.
See also [life cycle controller documentation](../../../../ip/lc_ctrl/README.md) for more details.

The vendor-specific OTP test signals of the life cycle controller are not connected to the OTP controller.
% if macro_backend == "otp_macro":
In this top, they are connected to `otp_macro` instead (see the [macro interface backends](theory_of_operation.md#macro-interface-and-backends)).
% else:
In this top, they are not connected, since the `${macro_backend}` backend does not provide vendor-specific OTP test functionality (see the [macro interface backends](theory_of_operation.md#macro-interface-and-backends)).
% endif

${"####"} State, Counter and Token Output

After initialization, the life cycle partition contents, as well as the tokens and personalization status is output to the life cycle controller via the `otp_lc_data_o` struct.
The life cycle controller uses this information to determine the life cycle state, and steer the appropriate qualifier signals.
Some of these qualifier signals are fed back to the OTP controller:
- `lc_creator_seed_sw_rw_en_i` enables SW access to the partitions holding the creator key material (for example the root key in the `SECRET2` partition).
- `lc_owner_seed_sw_rw_en_i` enables SW access to the partitions holding the owner key material, if the memory map contains such partitions.
- `lc_seed_hw_rd_en_i` enables hardware read access to the root keys.
- `lc_check_byp_en_i` bypasses the consistency checks of the buffered partitions while a life cycle transition is ongoing.
- `lc_rma_state_i` re-enables DAI read access to partitions that are configured to ignore their read lock in RMA.
- `lc_escalate_en_i` pushes the OTP controller into escalation state.

A possible sequence for the signals described is illustrated below.
```wavejson
{signal: [
  {name: 'clk_i',                           wave: 'p.................'},
  {name: 'otp_lc_data_o.valid',             wave: '0.|...|.1.|...|...'},
  {name: 'otp_lc_data_o.state',             wave: '03|...|...|...|...'},
  {name: 'otp_lc_data_o.count',             wave: '03|...|...|...|...'},
  {},
  {name: 'otp_lc_data_o.test_unlock_token', wave: '0.|...|.3.|...|...'},
  {name: 'otp_lc_data_o.test_exit_token',   wave: '0.|...|.3.|...|...'},
  {name: 'otp_lc_data_o.test_tokens_valid', wave: '0.|...|.3.|...|...'},
  {},
  {name: 'otp_lc_data_o.rma_token',         wave: '0.|.3.|...|...|...'},
  {name: 'otp_lc_data_o.rma_token_valid',   wave: '0.|.3.|...|...|...'},
  {},
  {name: 'otp_lc_data_o.secrets_valid',     wave: '0.|.3.|...|...|...'},
  {},
  {name: 'lc_creator_seed_sw_rw_en_i',      wave: '0.|...|...|.4.|...'},
  {name: 'lc_seed_hw_rd_en_i',              wave: '0.|...|...|.4.|...'},
  {name: 'lc_owner_seed_sw_rw_en_i',        wave: '0.|...|...|.4.|...'},
  {},
  {name: 'lc_escalate_en_i',                wave: '0.|...|...|...|.5.'},
]}
```

Note that the `otp_lc_data_o.valid` signal is only asserted after the `LIFE_CYCLE`, `SECRET0` and `SECRET2` partitions have successfully initialized, since the life cycle collateral contains information from all three partitions.
The `otp_lc_data_o.test_tokens_valid` and `otp_lc_data_o.rma_token_valid` signals are multibit valid signals indicating whether the corresponding tokens are valid.
The ``otp_lc_data_o.secrets_valid`` signal is a multibit valid signal that is set to `lc_ctrl_pkg::On` iff the `SECRET2` partition containing the root keys has been locked with a digest.


${"####"} State Transitions

In order to perform life cycle state transitions, the life cycle controller can present the new value of the life cycle state and counter via the programming interface as shown below:

```wavejson
{signal: [
  {name: 'clk_i',                          wave: 'p.......'},
  {name: 'lc_otp_program_i.req',           wave: '01.|..0.'},
  {name: 'lc_otp_program_i.state',         wave: '03.|..0.'},
  {name: 'lc_otp_program_i.count',         wave: '03.|..0.'},
  {name: 'lc_otp_program_o.ack',           wave: '0..|.10.'},
  {name: 'lc_otp_program_o.err',           wave: '0..|.40.'},
]}
```

The request must remain asserted until the life cycle controller has responded.
An error is fatal and indicates that the OTP programming operation has failed.

Note that the new state must not clear any bits that have already been programmed to OTP - i.e., the new state must be incrementally programmable on top of the previous state.
There are hence some implications on the life cycle encoding due to the ECC employed, see [life cycle state encoding](../../../../ip/lc_ctrl/doc/theory_of_operation.md#life-cycle-manufacturing-state-encodings) for details.

${"###"} Interface to Key Manager

Each individual secret key material (CREATOR_ROOT_KEY, OWNER_SEED, CREATOR_SEED) gets its own connection to the keymgr.
These secrets are provided to the keymgr if they have been provisioned and locked (via CREATOR_KEY_LOCK), otherwise these signals are tied to random netlist constants.
% if field_entropy_part:

The FIELD_ENTROPY in the `${field_entropy_part}` partition is provided to the key manager via the `keymgr_field_entropy_o` signal.
`keymgr_field_entropy_o.secret_valid` is set once the `${field_entropy_part}` partition has been locked with a digest, has been successfully initialized, and the FIELD_ENTROPY is not all-zero.
If the FIELD_ENTROPY is not valid, the key manager uses its own netlist constant instead.
Like for the CREATOR_ROOT_KEY, the FIELD_ENTROPY value is only output if `lc_seed_hw_rd_en_i` is asserted, otherwise `keymgr_field_entropy_o.secret` is tied to a random netlist constant.
Like for the `SECRET1` partition, SW access via the DAI is only restricted by the partition's own digest lock, and read access is re-enabled in RMA.
% endif
% if secondary_root_key_part:

The SECONDARY_ROOT_KEY (SECONDARY_ROOT_KEY_SHARE0, SECONDARY_ROOT_KEY_SHARE1) in the `${secondary_root_key_part}` partition is provided to the key manager via the `keymgr_secondary_root_key_o` signal.
`keymgr_secondary_root_key_o.share0/1_valid` are each set once the `${secondary_root_key_part}` partition has been locked with a digest, has been successfully initialized, the respective share is not all-zero, and `lc_seed_hw_rd_en_i` is asserted.
The key manager only accepts the secondary root key if both shares are valid.
Like for the CREATOR_ROOT_KEY, the key shares are only provided if `lc_seed_hw_rd_en_i` is asserted, otherwise they are tied to random netlist constants.
% endif

Since the key manager may run in a different clock domain, key manager is responsible for synchronizing the ${", ".join(f"`{s}`" for s in keymgr_sigs)} signals.

${"###"} Interfaces to SRAM and OTBN Scramblers

The interfaces to the SRAM and OTBN scrambling devices follow a req / ack protocol, where the scrambling device first requests a new ephemeral key by asserting the request channel (`sram_otp_key_i[*]`, `otbn_otp_key_i`).
The OTP controller then fetches entropy from EDN and derives an ephemeral key using the SRAM_DATA_KEY_SEED and the [PRESENT scrambling data path](#scrambling-datapath).
Finally, the OTP controller returns a fresh ephemeral key via the response channels (`sram_otp_key_o[*]`, `otbn_otp_key_o`), which complete the req / ack handshake.
The wave diagram below illustrates this process for the OTBN scrambling device.

```wavejson
{signal: [
  {name: 'clk_i',                     wave: 'p.......'},
  {name: 'otbn_otp_key_i.req',        wave: '01.|..0.'},
  {name: 'otbn_otp_key_o.ack',        wave: '0..|.10.'},
  {name: 'otbn_otp_key_o.nonce',      wave: '0..|.30.'},
  {name: 'otbn_otp_key_o.key',        wave: '0..|.30.'},
  {name: 'otbn_otp_key_o.seed_valid', wave: '0..|.10.'},
]}
```

If the key seeds have not yet been provisioned, the keys are derived from all-zero constants, and the `*.seed_valid` signal will be set to 0 in the response.
The resulting scrambling key is still ephemeral (i.e., it is derived using entropy from CSRNG) and okay to be used.
It should be noted that this mechanism requires the EDN and entropy distribution network to be operational, and a key derivation request will block if they are not.

Note that the req/ack protocol runs on the OTP clock.
It is the task of the scrambling device to synchronize the handshake protocol by instantiating the `prim_sync_reqack.sv` primitive as shown below.

![OTP Key Req Ack](../doc/otp_ctrl_key_req_ack.svg)

Note that the key and nonce output signals on the OTP controller side are guaranteed to remain stable for at least 62 OTP clock cycles after the `ack` signal is pulsed high, because the derivation of a 64bit half-key takes at least two passes through the 31-cycle PRESENT primitive.
Hence, if the scrambling device clock is faster or in the same order of magnitude as the OTP clock, the data can be directly sampled upon assertion of `src_ack_o`.
If the scrambling device runs on a significantly slower clock than OTP, an additional register (as indicated with dashed grey lines in the figure) has to be added.

% if enable_nvm_key:
${"###"} Interface to NVM Scrambler

The interface to the NVM scrambling device is a simple req/ack interface that provides the nvm controller with the two 128bit keys for data and address scrambling.

The keys can be requested as illustrated below:

```wavejson
{signal: [
  {name: 'clk_i',                    wave: 'p...........'},
  {name: 'nvm_otp_key_i.data_req',   wave: '01.|..0.|...'},
  {name: 'nvm_otp_key_i.addr_req',   wave: '01.|....|..0'},
  {name: 'nvm_otp_key_o.data_ack',   wave: '0..|.10.|...'},
  {name: 'nvm_otp_key_o.addr_ack',   wave: '0..|....|.10'},
  {name: 'nvm_otp_key_o.key',        wave: '0..|.30.|.40'},
  {name: 'nvm_otp_key_o.seed_valid', wave: '0..|.10.|.10'},
]}
```

The keys are derived from the NVM_DATA_KEY_SEED and NVM_ADDR_KEY_SEED values stored in the `SECRET1` partition using the [scrambling primitive](#scrambling-datapath).
If the key seeds have not yet been provisioned, the keys are derived from all-zero constants, and the `nvm_otp_key_o.seed_valid` signal will be set to 0 in the response.
The resulting scrambling key is still ephemeral (i.e., it is derived using entropy from CSRNG) and okay to be used.

Note that the req/ack protocol runs on the OTP clock.
It is the task of the scrambling device to perform the synchronization as described in the previous subsection on the [interface to SRAM and OTBN scramblers](#interface-to-sram-and-otbn-scramblers).

% endif
${"###"} Macro Interface

The OTP controller accesses its non-volatile storage via the `otp_macro_o` and `otp_macro_i` structs.
This interface is connected either to `otp_macro`, which wraps a dedicated OTP macro, or to `rram_ctrl`, which emulates OTP in the RRAM.
In this top, it is connected to `${macro_backend}`.
See [Macro Interface and Backends](theory_of_operation.md#macro-interface-and-backends) for the protocol and the two backends.

${"###"} Hardware Config Bits

The bits of the HW_CFG* partitions are output via the `otp_broadcast_o` struct.
IPs that consume collateral stored in this partition shall connect to this struct via the topgen feature, and break out the appropriate bits by either accessing the correct index or using the struct fields.
These fields are autogenerated from the memory map items allocated to the HW_CFG* partitions, and the autogenerated struct type can be found in the `otp_ctrl_part_pkg.sv` package.
Note that it is the task of the receiving IP to synchronize these bits accordingly to the local clock.
For convenience, a valid bit is also available in that struct.
The valid bit indicates that the HW_CFG* partitions have initialized.

${"##"} Parameter and Memory Map Changes after D3/V3

Note that all instantiation parameters can be changed without affecting D3/V3 status of the module.
Similarly, it is permissible to change the contents (partition size, adding and removing items) of the `CREATOR_SW_CFG`, `OWNER_SW_CFG` and `HW_CFG*` partitions without affecting D3 status.
Note however that partition size changes may affect V3 coverage metrics, hence if the size any of the above three partitions is changed, V3 needs to be re-assessed.
