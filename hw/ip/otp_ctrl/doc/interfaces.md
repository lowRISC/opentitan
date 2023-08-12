# Hardware Interfaces

## Parameters

The following table lists the instantiation parameters of OTP.
Note that parameters prefixed with `RndCnst` are random netlist constants that need to be regenerated via topgen before the tapeout (typically by the silicon creator).

Parameter                   | Default (Max) | Top Earlgrey | Description
----------------------------|---------------|--------------|---------------
`AlertAsyncOn`              | 2'b11         | 2'b11        |
`RndCnstLfsrSeed`           | (see RTL)     | (see RTL)    | Seed to be used for the internal 40bit partition check timer LFSR. This needs to be replaced by the silicon creator before the tapeout.
`RndCnstLfsrPerm`           | (see RTL)     | (see RTL)    | Permutation to be used for the internal 40bit partition check timer LFSR. This needs to be replaced by the silicon creator before the tapeout.
`RndCnstKey`                | (see RTL)     | (see RTL)    | Random scrambling keys for secret partitions, to be used in the [scrambling datapath](#scrambling-datapath).
`RndCnstDigestConst`        | (see RTL)     | (see RTL)    | Random digest finalization constants, to be used in the [scrambling datapath](#scrambling-datapath).
`RndCnstDigestIV`           | (see RTL)     | (see RTL)    | Random digest initialization vectors, to be used in the [scrambling datapath](#scrambling-datapath).
`RndCnstRawUnlockToken`     | (see RTL)     | (see RTL)    | Global RAW unlock token to be used for the first life cycle transition. See also [conditional life cycle transitions](../../lc_ctrl/README.md#conditional-transitions).

## Signals

<!-- BEGIN CMDGEN util/regtool.py --interfaces ./hw/ip/otp_ctrl/data/otp_ctrl.hjson -->
Referring to the [Comportable guideline for peripheral device functionality](https://opentitan.org/book/doc/contributing/hw/comportability), the module **`otp_ctrl`** has the following hardware interfaces defined
- Primary Clock: **`clk_i`**
- Other Clocks: **`clk_edn_i`**
- Bus Device Interfaces (TL-UL): **`core_tl`**, **`prim_tl`**
- Bus Host Interfaces (TL-UL): *none*

## Peripheral Pins for Chip IO

| Pin name   | Direction   | Description                                                       |
|:-----------|:------------|:------------------------------------------------------------------|
| test[7:0]  | output      | Test-related GPIOs. Only active in DFT-enabled life cycle states. |

## [Inter-Module Signals](https://opentitan.org/book/doc/contributing/hw/comportability/index.html#inter-signal-handling)

| Port Name                | Package::Struct                  | Type    | Act   |   Width | Description                                                                                                                                                                                                     |
|:-------------------------|:---------------------------------|:--------|:------|--------:|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| otp_ext_voltage_h        |                                  | io      | none  |       1 |                                                                                                                                                                                                                 |
| otp_ast_pwr_seq          | otp_ctrl_pkg::otp_ast_req        | uni     | req   |       1 | Power sequencing signals to AST (VDD domain).                                                                                                                                                                   |
| otp_ast_pwr_seq_h        | otp_ctrl_pkg::otp_ast_rsp        | uni     | rcv   |       1 | Power sequencing signals coming from AST (VCC domain).                                                                                                                                                          |
| edn                      | edn_pkg::edn                     | req_rsp | req   |       1 | Entropy request to the entropy distribution network for LFSR reseeding and ephemeral key derivation.                                                                                                            |
| pwr_otp                  | pwrmgr_pkg::pwr_otp              | req_rsp | rsp   |       1 | Initialization request/acknowledge from/to power manager.                                                                                                                                                       |
| lc_otp_vendor_test       | otp_ctrl_pkg::lc_otp_vendor_test | req_rsp | rsp   |       1 | Vendor test control signals from/to the life cycle TAP.                                                                                                                                                         |
| lc_otp_program           | otp_ctrl_pkg::lc_otp_program     | req_rsp | rsp   |       1 | Life cycle state transition interface.                                                                                                                                                                          |
| otp_lc_data              | otp_ctrl_pkg::otp_lc_data        | uni     | req   |       1 | Life cycle state output holding the current life cycle state, the value of the transition counter and the tokens needed for life cycle transitions.                                                             |
| lc_escalate_en           | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 | Life cycle escalation enable coming from life cycle controller. This signal moves all FSMs within OTP into the error state.                                                                                     |
| lc_creator_seed_sw_rw_en | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 | Provision enable qualifier coming from life cycle controller. This signal enables SW read / write access to the RMA_TOKEN and CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1.                              |
| lc_seed_hw_rd_en         | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 | Seed read enable coming from life cycle controller. This signal enables HW read access to the CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1.                                                              |
| lc_dft_en                | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 | Test enable qualifier coming from life cycle controller. This signals enables the TL-UL access port to the proprietary OTP IP.                                                                                  |
| lc_check_byp_en          | lc_ctrl_pkg::lc_tx               | uni     | rcv   |       1 | Life cycle partition check bypass signal. This signal causes the life cycle partition to bypass consistency checks during life cycle state transitions in order to prevent spurious consistency check failures. |
| otp_keymgr_key           | otp_ctrl_pkg::otp_keymgr_key     | uni     | req   |       1 | Key output to the key manager holding CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1.                                                                                                                      |
| flash_otp_key            | otp_ctrl_pkg::flash_otp_key      | req_rsp | rsp   |       1 | Key derivation interface for FLASH scrambling.                                                                                                                                                                  |
| sram_otp_key             | otp_ctrl_pkg::sram_otp_key       | req_rsp | rsp   |       3 | Array with key derivation interfaces for SRAM scrambling devices.                                                                                                                                               |
| otbn_otp_key             | otp_ctrl_pkg::otbn_otp_key       | req_rsp | rsp   |       1 | Key derivation interface for OTBN scrambling devices.                                                                                                                                                           |
| otp_hw_cfg               | otp_ctrl_part_pkg::otp_hw_cfg    | uni     | req   |       1 | Output of the HW_CFG partition.                                                                                                                                                                                 |
| obs_ctrl                 | ast_pkg::ast_obs_ctrl            | uni     | rcv   |       1 | AST observability control signals.                                                                                                                                                                              |
| otp_obs                  | logic                            | uni     | req   |       8 | AST observability bus.                                                                                                                                                                                          |
| core_tl                  | tlul_pkg::tl                     | req_rsp | rsp   |       1 |                                                                                                                                                                                                                 |
| prim_tl                  | tlul_pkg::tl                     | req_rsp | rsp   |       1 |                                                                                                                                                                                                                 |

## Interrupts

| Interrupt Name     | Type   | Description                                                                                                                  |
|:-------------------|:-------|:-----------------------------------------------------------------------------------------------------------------------------|
| otp_operation_done | Event  | A direct access command or digest calculation operation has completed.                                                       |
| otp_error          | Event  | An error has occurred in the OTP controller. Check the [`ERR_CODE`](registers.md#err_code) register to get more information. |

## Security Alerts

| Alert Name            | Description                                                                                                                                        |
|:----------------------|:---------------------------------------------------------------------------------------------------------------------------------------------------|
| fatal_macro_error     | This alert triggers if hardware detects an uncorrectable error during an OTP transaction, for example an uncorrectable ECC error in the OTP array. |
| fatal_check_error     | This alert triggers if any of the background checks fails. This includes the digest checks and concurrent ECC checks in the buffer registers.      |
| fatal_bus_integ_error | This fatal alert is triggered when a fatal TL-UL bus integrity fault is detected.                                                                  |
| fatal_prim_otp_alert  | Fatal alert triggered inside the OTP primitive, including fatal TL-UL bus integrity faults of the test interface.                                  |
| recov_prim_otp_alert  | Recoverable alert triggered inside the OTP primitive.                                                                                              |

## Security Countermeasures

| Countermeasure ID                    | Description                                                                                                                                                         |
|:-------------------------------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| OTP_CTRL.BUS.INTEGRITY               | End-to-end bus integrity scheme.                                                                                                                                    |
| OTP_CTRL.SECRET.MEM.SCRAMBLE         | Secret partitions are scrambled with a full-round PRESENT cipher.                                                                                                   |
| OTP_CTRL.PART.MEM.DIGEST             | Integrity of buffered partitions is ensured via a 64bit digest.                                                                                                     |
| OTP_CTRL.DAI.FSM.SPARSE              | The direct access interface FSM is sparsely encoded.                                                                                                                |
| OTP_CTRL.KDI.FSM.SPARSE              | The key derivation interface FSM is sparsely encoded.                                                                                                               |
| OTP_CTRL.LCI.FSM.SPARSE              | The life cycle interface FSM is sparsely encoded.                                                                                                                   |
| OTP_CTRL.PART.FSM.SPARSE             | The partition FSMs are sparsely encoded.                                                                                                                            |
| OTP_CTRL.SCRMBL.FSM.SPARSE           | The scramble datapath FSM is sparsely encoded.                                                                                                                      |
| OTP_CTRL.TIMER.FSM.SPARSE            | The background check timer FSM is sparsely encoded.                                                                                                                 |
| OTP_CTRL.DAI.CTR.REDUN               | The direct access interface address counter employs a cross-counter implementation.                                                                                 |
| OTP_CTRL.KDI_SEED.CTR.REDUN          | The key derivation interface counter employs a cross-counter implementation.                                                                                        |
| OTP_CTRL.KDI_ENTROPY.CTR.REDUN       | The key derivation entropy counter employs a cross-counter implementation.                                                                                          |
| OTP_CTRL.LCI.CTR.REDUN               | The life cycle interface address counter employs a cross-counter implementation.                                                                                    |
| OTP_CTRL.PART.CTR.REDUN              | The address counter of buffered partitions employs a cross-counter implementation.                                                                                  |
| OTP_CTRL.SCRMBL.CTR.REDUN            | The srambling datapath counter employs a cross-counter implementation.                                                                                              |
| OTP_CTRL.TIMER_INTEG.CTR.REDUN       | The background integrity check timer employs a duplicated counter implementation.                                                                                   |
| OTP_CTRL.TIMER_CNSTY.CTR.REDUN       | The background consistency check timer employs a duplicated counter implementation.                                                                                 |
| OTP_CTRL.TIMER.LFSR.REDUN            | The background check LFSR is duplicated.                                                                                                                            |
| OTP_CTRL.DAI.FSM.LOCAL_ESC           | The direct access interface FSM is moved into an invalid state upon local escalation.                                                                               |
| OTP_CTRL.LCI.FSM.LOCAL_ESC           | The life cycle interface FSM is moved into an invalid state upon local escalation.                                                                                  |
| OTP_CTRL.KDI.FSM.LOCAL_ESC           | The key derivation interface FSM is moved into an invalid state upon local escalation.                                                                              |
| OTP_CTRL.PART.FSM.LOCAL_ESC          | The partition FSMs are moved into an invalid state upon local escalation.                                                                                           |
| OTP_CTRL.SCRMBL.FSM.LOCAL_ESC        | The scramble datapath FSM is moved into an invalid state upon local escalation.                                                                                     |
| OTP_CTRL.TIMER.FSM.LOCAL_ESC         | The background check timer FSM is moved into an invalid state upon local escalation.                                                                                |
| OTP_CTRL.DAI.FSM.GLOBAL_ESC          | The direct access interface FSM is moved into an invalid state upon global escalation via life cycle.                                                               |
| OTP_CTRL.LCI.FSM.GLOBAL_ESC          | The life cycle interface FSM is moved into an invalid state upon global escalation via life cycle.                                                                  |
| OTP_CTRL.KDI.FSM.GLOBAL_ESC          | The key derivation interface FSM is moved into an invalid state upon global escalation via life cycle.                                                              |
| OTP_CTRL.PART.FSM.GLOBAL_ESC         | The partition FSMs are moved into an invalid state upon global escalation via life cycle.                                                                           |
| OTP_CTRL.SCRMBL.FSM.GLOBAL_ESC       | The scramble datapath FSM is moved into an invalid state upon global escalation via life cycle.                                                                     |
| OTP_CTRL.TIMER.FSM.GLOBAL_ESC        | The background check timer FSM is moved into an invalid state upon global escalation via life cycle.                                                                |
| OTP_CTRL.PART.DATA_REG.INTEGRITY     | All partition buffer registers are protected with ECC on 64bit blocks.                                                                                              |
| OTP_CTRL.PART.DATA_REG.BKGN_CHK      | The digest of buffered partitions is recomputed and checked at pseudorandom intervals in the background.                                                            |
| OTP_CTRL.PART.MEM.REGREN             | Unbuffered ('software') partitions can be read-locked via a CSR until the next system reset.                                                                        |
| OTP_CTRL.PART.MEM.SW_UNREADABLE      | Secret buffered partitions become unreadable to software once they are locked via the digest.                                                                       |
| OTP_CTRL.PART.MEM.SW_UNWRITABLE      | All partitions become unwritable by software once they are locked via the digest.                                                                                   |
| OTP_CTRL.LC_PART.MEM.SW_NOACCESS     | The life cycle partition is not directly readable nor writable via software.                                                                                        |
| OTP_CTRL.ACCESS.CTRL.MUBI            | The access control signals going from the partitions to the DAI are MUBI encoded.                                                                                   |
| OTP_CTRL.TOKEN_VALID.CTRL.MUBI       | The token valid signals going to the life cycle controller are MUBI encoded.                                                                                        |
| OTP_CTRL.LC_CTRL.INTERSIG.MUBI       | The life cycle control signals are multibit encoded.                                                                                                                |
| OTP_CTRL.TEST.BUS.LC_GATED           | Prevent access to test signals and the OTP backdoor interface in non-test lifecycle states.                                                                         |
| OTP_CTRL.TEST_TL_LC_GATE.FSM.SPARSE  | The control FSM inside the TL-UL gating primitive is sparsely encoded.                                                                                              |
| OTP_CTRL.DIRECT_ACCESS.CONFIG.REGWEN | The direct access CSRs are REGWEN protected.                                                                                                                        |
| OTP_CTRL.CHECK_TRIGGER.CONFIG.REGWEN | The check trigger CSR is REGWEN protected.                                                                                                                          |
| OTP_CTRL.CHECK.CONFIG.REGWEN         | The check CSR is REGWEN protected.                                                                                                                                  |
| OTP_CTRL.MACRO.MEM.INTEGRITY         | The OTP macro employs a vendor-specific integrity scheme at the granularity of the native 16bit OTP words. The scheme is able to at least detect single bit errors. |
| OTP_CTRL.MACRO.MEM.CM                | The OTP macro may contain additional vendor-specific countermeasures.                                                                                               |


<!-- END CMDGEN -->

The OTP controller contains various interfaces that connect to other comportable IPs within OpenTitan, and these are briefly explained further below.

### EDN Interface

The entropy request interface that talks to EDN in order to fetch fresh entropy for ephemeral SRAM scrambling key derivation and the LFSR counters for background checks.
It is comprised of the `otp_edn_o` and `otp_edn_i` signals and follows a req / ack protocol.

See also [EDN documentation](../../edn/README.md).

### Power Manager Interface

The power manager interface is comprised of three signals overall: an initialization request (`pwr_otp_i.otp_init`), an initialization done response (`pwr_otp_o.otp_done`) and an idle indicator (`pwr_otp_o.otp_idle`).

The power manager asserts `pwr_otp_i.otp_init` in order to signal to the OTP controller that it can start initialization, and the OTP controller signals completion of the initialization sequence by asserting `pwr_otp_o.otp_done` (the signal will remain high until reset).

The idle indication signal `pwr_otp_o.otp_idle` indicates whether there is an ongoing write operation in the Direct Access Interface (DAI) or Life Cycle Interface (LCI), and the power manager uses that indication to determine whether a power down request needs to be aborted.

Since the power manager may run in a different clock domain, the `pwr_otp_i.otp_init` signal is synchronized within the OTP controller.
The power manager is responsible for synchronizing the `pwr_otp_o.otp_done` and `pwr_otp_o.otp_idle` signals.

See also [power manager documentation](../../pwrmgr/README.md).

### Life Cycle Interfaces

The interface to the life cycle controller can be split into three functional sub-interfaces (vendor test, state output, state transitions), and these are explained in more detail below.
Note that the OTP and life cycle controllers are supposed to be in the same clock domain, hence no additional signal synchronization is required.
See also [life cycle controller documentation](../../lc_ctrl/README.md) for more details.

#### Vendor Test Signals

The `lc_otp_vendor_test_i` and `lc_otp_vendor_test_o` signals are connected to a 32bit control and a 32bit status register in the life cycle TAP, respectively, and are directly routed to the `prim_otp` wrapper.
These control and status signals may be used by the silicon creator to exercise the OTP programming smoke checks on the VENDOR_TEST partition.
The signals are gated with the life cycle state inside the life cycle controller such that they do not have any effect in production life cycle states.

#### State, Counter and Token Output

After initialization, the life cycle partition contents, as well as the tokens and personalization status is output to the life cycle controller via the `otp_lc_data_o` struct.
The life cycle controller uses this information to determine the life cycle state, and steer the appropriate qualifier signals.
Some of these qualifier signals (`lc_dft_en_i`, `lc_creator_seed_sw_rw_en_i`, `lc_seed_hw_rd_en_i` and `lc_escalate_en_i`) are fed back to the OTP controller in order to ungate testing logic to the OTP macro; enable SW write access to the `SECRET2` partition; enable hardware read access to the root key in the `SECRET2` partition; or to push the OTP controller into escalation state.

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
  {name: 'lc_dft_en_i',                     wave: '0.|...|...|.4.|...'},
  {},
  {name: 'lc_escalate_en_i',                wave: '0.|...|...|...|.5.'},
]}
```

Note that the `otp_lc_data_o.valid` signal is only asserted after the `LIFE_CYCLE`, `SECRET0` and `SECRET2` partitions have successfully initialized, since the life cycle collateral contains information from all three partitions.
The `otp_lc_data_o.test_tokens_valid` and `otp_lc_data_o.rma_token_valid` signals are multibit valid signals indicating whether the corresponding tokens are valid.
The ``otp_lc_data_o.secrets_valid`` signal is a multibit valid signal that is set to `lc_ctrl_pkg::On` iff the `SECRET2` partition containing the root keys has been locked with a digest.


#### State Transitions

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
There are hence some implications on the life cycle encoding due to the ECC employed, see [life cycle state encoding](../../lc_ctrl/README.md#life-cycle-manufacturing-state-encodings) for details.

Note that the behavior of the `lc_otp_program_i.otp_test_ctrl` signal is vendor-specific, and hence the signal is set to `x` in the timing diagram above.
The purpose of this signal is to control vendor-specific test mechanisms, and its value will only be forwarded to the OTP macro in RAW, TEST_* and RMA states.
In all other life cycle states this signal will be clamped to zero.

### Interface to Key Manager

The interface to the key manager is a simple struct that outputs the CREATOR_ROOT_KEY_SHARE0 and CREATOR_ROOT_KEY_SHARE1 keys via `otp_keymgr_key_o` if these secrets have been provisioned and locked (via CREATOR_KEY_LOCK).
Otherwise, this signal is tied to a random netlist constant.

Since the key manager may run in a different clock domain, key manager is responsible for synchronizing the `otp_keymgr_key_o` signals.

### Interface to Flash Scrambler

The interface to the FLASH scrambling device is a simple req/ack interface that provides the flash controller with the two 128bit keys for data and address scrambling.

The keys can be requested as illustrated below:

```wavejson
{signal: [
  {name: 'clk_i',                      wave: 'p...........'},
  {name: 'flash_otp_key_i.data_req',   wave: '01.|..0.|...'},
  {name: 'flash_otp_key_i.addr_req',   wave: '01.|....|..0'},
  {name: 'flash_otp_key_o.data_ack',   wave: '0..|.10.|...'},
  {name: 'flash_otp_key_o.addr_ack',   wave: '0..|....|.10'},
  {name: 'flash_otp_key_o.key',        wave: '0..|.30.|.40'},
  {name: 'flash_otp_key_o.seed_valid', wave: '0..|.10.|.10'},
]}
```

The keys are derived from the FLASH_DATA_KEY_SEED and FLASH_ADDR_KEY_SEED values stored in the `SECRET1` partition using the [scrambling primitive](#scrambling-datapath).
If the key seeds have not yet been provisioned, the keys are derived from all-zero constants, and the `flash_otp_key_o.seed_valid` signal will be set to 0 in the response.

Note that the req/ack protocol runs on the OTP clock.
It is the task of the scrambling device to synchronize the handshake protocol by instantiating the `prim_sync_reqack.sv` primitive as shown below.

![OTP Key Req Ack](../doc/otp_ctrl_key_req_ack.svg)

Note that the key and nonce output signals on the OTP controller side are guaranteed to remain stable for at least 62 OTP clock cycles after the `ack` signal is pulsed high, because the derivation of a 64bit half-key takes at least two passes through the 31-cycle PRESENT primitive.
Hence, if the scrambling device clock is faster or in the same order of magnitude as the OTP clock, the data can be directly sampled upon assertion of `src_ack_o`.
If the scrambling device runs on a significantly slower clock than OTP, an additional register (as indicated with dashed grey lines in the figure) has to be added.

### Interfaces to SRAM and OTBN Scramblers

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
It should be noted that this mechanism requires the EDN and entropy distribution network to be operational, and a key derivation request will block if they are not.

Note that the req/ack protocol runs on the OTP clock.
It is the task of the scrambling device to perform the synchronization as described in the previous subsection on the [flash scrambler interface](#interface-to-flash-scrambler).

### Hardware Config Bits

The bits of the HW_CFG partition are output via the `otp_hw_cfg_o` struct.
IPs that consume collateral stored in this partition shall connect to this struct via the topgen feature, and break out the appropriate bits by either accessing the correct index or using the struct fields.
These fields are autogenerated from the memory map items allocated to the HW_CFG partition, and the autogenerated struct type can be found in the `otp_ctrl_part_pkg.sv` package.
Note that it is the task of the receiving IP to synchronize these bits accordingly to the local clock.
For convenience, a valid bit is also available in that struct.
The valid bit indicates that the HW_CFG partition has initialized.

## Parameter and Memory Map Changes after D3/V3

Note that all instantiation parameters can be changed without affecting D3/V3 status of the module.
Similarly, it is permissible to change the contents (partition size, adding and removing items) of the `CREATOR_SW_CFG`, `OWNER_SW_CFG` and `HW_CFG` partitions without affecting D3 status.
Note however that partition size changes may affect V3 coverage metrics, hence if the size any of the above three partitions is changed, V3 needs to be re-assessed.
