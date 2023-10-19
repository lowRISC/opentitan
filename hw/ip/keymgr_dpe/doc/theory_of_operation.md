# Theory of Operation

The following diagram gives an example on how keymgr DPE handles multiple DICE contexts.

![Key Manager Functional Model](../doc/keymgr_dpe_diagram.svg)

This example diagram describes a sequence of advance operations on multiple keymgr slots, assuming that keymgr_dpe is instantiated with 4 key slots.
Blue rounded rectangles represent empty key slots and green color is used to denote when they become active. Each slot stores a secret key as well as context data for its key.
Purple rectangles denote key derivation function (KDF) calls that are used to compute slot keys.

In OpenTitan, the KDF is instantiated as [KMAC](../../kmac/README.md).
Each valid operation involves a KMAC invocation, which uses the internal key from the selected source slot for its key input, and other HW / SW supplied inputs as its message.
The concatenated components of the message is dependent on the context of the source slot as well as further inputs provided from HW / SW.

In theory, KMAC can generate outputs of arbitrary length, however this design uses a specific variant with 256-bit security strength, 384-bit digest size, and 256-bit key input.

Effectively, the key manager behavior is divided into 2 classes of functions:
* Key manager state advancement (also referred to as deriving children slots/nodes). The resulting secrets/keys from these operations are not visible to software and not directly usable by any software controlled hardware.

* Output key generation. Results can be visible to software or accessible only by hardware (a.k.a. sideloaded keys).

For clarity, all commands issued to the key manager by software are referred to as operations.
Transactions refer to the interaction between key manager and KMAC if a valid operation is issued.
A DPE context refers to what is stored in a keymgr slot, and it consists of a secret key and its associated information.
A keymgr slot refers to the storage unit for DPE contexts, and the actual DPE context it stores is dynamically controlled by SW commands.
In order to address the relationships among keymgr_dpe slots and their stored DPE contexts more clearly, we use the terms _parent slot_ and _child slot_ to mean that their stored DPE contexts follow parent-child relationship in DICE hierarchy.

## Key Manager Slots

keymgr_dpe consists of `DpeNumBootStages` slots, which is a generic parameter.
Each of these key manager slots can store a DPE context, i.e. all DICE-related information for a particular boot stage. That includes a secret key along with additional context information described below.
The secret key size is fixed to 256-bit.

Each slot data consists of the following fields:
* `valid` bit that tells whether the slot is occupied.
* `boot_stage` that refers to which boot stage this slot belongs to.
* `max_key_version` stores the maximum allowed key version that can be generated from this slot.
* `key_policy` limits some of the operations that can be performed with this slot.

A slot is a dynamic storage unit and the DPE context it stores is controlled by SW, even though their secret keys never leave HW.
A slot becomes active (i.e. `valid` is set to 1) when it is chosen as a destination slot during a successful advance call.

When a slot is active, `boot_stage` refers to its DPE context boot stage.
For flexibility, `boot_stage` is a simple unsigned integer that is incremented from the parent's `boot_stage` during advance calls.
Its actual mapping to boot stages such as ROM, BL0 or Kernel can be determined by SW.
Hence, keymgr_dpe is oblivious to this mapping between counter values and the boot stages, with an exception.
The exception is that the first two stages are treated specially by RTL during KDF advance calls, as they consume other HW-backed inputs that come from keymgr_dpe’s peripheral inputs.
From SW's point of view, they are still treated as any arbitrary DICE layer in that SW can provide further inputs through `SW_CDI_INPUT` CSR.

`max_key_version` is copied from a `MAX_KEY_VERSION` register into the slot field only during the advance call, and its value is effectively determined by the earlier boot stage through this CSR.
When a versioned key generation is invoked, max_key_version is compared against the key version value provided from SW.
The result of this inequality decides whether keymgr_dpe initiates the generation of the requested versioned key.

`key_policy` includes other miscellaneous bits such as allow_child, is_exportable or further reserved fields that can be used to limit which operations SW can request with a given slot.

## Key Manager State

The key manager working state represents the current working state of the key manager and it is decoupled from the DICE hierarchy.
From SW point of view, keymgr_dpe's FSM can only be in the following states: {`Reset`, `Available`, `Disabled`, `Invalid`}.
After reset, keymgr_dpe remains in `Reset` state until the first advance call that latches the UDS.
After this advance call, the FSM remains in `Available` state, and it can serve the advance/generate/erase requests.
Unless keymgr_dpe encounters is explicitly disabled or encounters a fatal error, the FSM remains in `Available` state.
Invalid states, such as {`Reset`, `Invalid`} on the other hand, are used to denote out-of-operation states.

### Reset
The advancement from `Reset` to `Available` internally goes through few FSM states, but from the SW point of view, this only requires a single advance call.
During these FSM transitions, the OTP root key (UDS) is latched into a destination slot specified by SW.
The latching of the root key can only happen once until the keymgr_DPE is reset.
Until the initial advance is invoked and keymgr_DPE reaches to `Ready`, the key manager rejects key generation requests.

### Available

During `Available`, keymgr_DPE accepts further advance and key generation requests.

When transitioning from `Reset` to `Available`, as a SCA counter-measure, random values obtained from the entropy source are used to populate the key slot first in a manner that both shares have the same random mask.
Then the root key is XORed on top of this randomness, in order to have fresh randomness for the root key (UDS).
During these transitions, keymgr_DPE's working state will be reported as `Reset`, until the latching is done and keymgr_DPE is ready to accept further commands.

### Disabled
`Disabled` is reached through an explicit disable command invocation.
In this state, keymgr_DPE is no longer operational and advance/generate/erase/disable commands return error.
Upon `Disabled` entry, the internal key slots are wiped.
However, previously generated sideload key slots and software key slots are preserved.
This allows the software to keep the last valid keys while preventing keymgr_DPE to produce further valid slots.

### Invalid
`Invalid` state is entered whenever key manager is deactivated through the [life cycle connection](#life-cycle-connection) or when an operation encounters a [fault](#faults-and-operational-faults).
Upon `Invalid` entry, the internal key, the sideload key slots and the software keys are all wiped.

### Invalid and Disabled State

`Invalid` and `Disabled` states are functionally very similar.
The main difference between the two is "how" the states were reached and the entry behavior.

`Disabled` state is reached through intentional software commands where the sideload key slots and software key are not wiped, while `Invalid` state is reached through life cycle deactivation or operational faults where the internal key, sideload key slots and software key are wiped.

This also means that only `Invalid` is a terminal state.
If after entering `Disabled` life cycle is deactivated or a fault is encountered, the same [invalid entry procedure](#Invalid) is followed to bring the system to a terminal `Invalid` state.

If ever multiple conditions collide (a fault is detected at the same time software issues disable command), the `Invalid` entry path always takes precedence.


## Accepted Commands
During each state, there are 4 valid commands software can issue:
* Advance state
* Output key generation (a.k.a versioned key generation)
* Erase slot
* Disable

The software is able to select a command and trigger the key manager FSM to process one of the commands.
If a command is valid during the current working state, it is processed and acknowledged when complete.
If a command is invalid, the requested operation is rejected and the values in key slots remain unmodified.
More details about command interactions can be found in Programmers Guide.

### Advance

Advancing a keymgr_dpe slot (also referred to as deriving a child) uses multiple inputs.
In particular, since there are multiple slots inside keymgr_dpe, source and destination parameters need to be passed to advance calls.

The very first advance call only latches the OTP root key, therefore most of these registers are ignored during the first call.
The only relevant registers (or register fields) during the first advance call are: `CONTROL_SHADOWED.OPERATION`, `CONTROL_SHADOWED.SLOT_DST_SEL` and `START`.
In particular, the destination slot for the UDS is chosen by SW, and there is no designated special slot for the UDS.
This initial latching can only be done once unless keymgr_dpe is reset.
If the OTP root key is not valid during the latching cycle, keymgr_dpe moves to `Invalid`state.

Further advance calls use the key stored in the specified `CONTROL_SHADOWED.SLOT_SRC_SEL` slot (equally referred to as _parent_ or _source_ slot) , and the result of the derivation updates the slot specified by `CONTROL_SHADOWED.SLOT_DST_SEL`  (referred to as _destination_ or _child_ slot).
Assuming that `key_policy`, `boot_stage` or `valid` bits of the parent context permit, the child secret is derived from the parent secret through a key derivation function during advance operation.
`KDF(child_key) = KDF(parent_key, message)`, where the message input might take few forms depending on boot_stage of the parent slot.
In particular:
* If `boot_stage=0` for the parent, then `message = (SW_CDI_INPUT || hw_revision_seed || device_identifier || health_st_measurement || rom_descriptors || creator_seed)`. See [KDF Details](#kdf-details) for more details on HW backed inputs.
* If `boot_stage=1` for the parent, the concatenated message input of KDF call is `(SW_CDI_INPUT || owner_seed)`.
* If `boot_stage>1` for the parent, then the message input is simply `SW_CDI_INPUT`.

At the end of a successful advance operation, the following updates are made for the slot selected by SLOT_DST_SEL:
* `valid` bit is set to 1.
* `key_policy` is updated (based on the parent’s policy and SLOT_POLICY).
* `max_key_version` is updated with MAX_KEY_VERSION register.
* `boot_stage` is set to the parent’s `boot_stage + 1`.
* `key` is updated from the key received from KMAC.

Note that the same slot can be chosen both as source and destination. In this case, the child DICE context overwrites the parent DICE context. Otherwise (if the source and destination are not same), then the source slot remains unmodified.

The `SLOT_POLICY` together with `key_policy` stored inside the parent is used to derive the policy bits of the child context. The details of how each policy field is determined is deferred to another section.

An advance operation returns error in the following cases:

* The UDS is not latched yet.
* The source slot is not valid.
* `boot_stage` reached to the maximum allowed value.
* The policy bits of the source slot prevent advancing (e.g. `allow_child` is false).

In particular note that the destination slot does not have be empty/invalid.
If the destination slot is already valid, its context will be overwritten by the computed child context.

### Versioned Key Generation

A versioned key generation operation uses the following registers:
* `CONTROL_SHADOWED.DST_SEL` determines the target use for the generated key, and that is either one of {AES, KMAC, OTBN}.
* `CONTROL_SHADOWED.SLOT_SRC_SEL` determines the source slot whose key should be used for the key derivation.
* `SALT` is used as a part of the message during the key derivation.
* `KEY_VERSION` is the target key value, and it also becomes the part of the message for KDF call.

During the generate operation, a versioned key is generated from the secret of the source slot selected by `SLOT_SRC_SEL`.
After a successful key generation operation, if the generated key is requested for HW use, then the generated key is loaded into the sideload slot that drives the specified target peripheral port (`DST_SEL` being either one of {AES, KMAC, OTBN}.
In the case of SW key, the generated key is loaded into a CSR (see `SW_SHARE0_OUTPUT` and `SW_SHARE1_OUTPUT` registers).

The key is generated with a KDF call, where the secret key is read from source slot.
Then, `generated_key = KDF(parent_key, KEY_VERSION || SALT || dest_seed || output_key)` where `dest_seed` and `output_key` are domain separators (i.e. diversification values from netlist) to distinguish SW/HW outputs as well as the target HWIP peripheral {AES, KMAC, OTBN}.

KDF used for key generation calls is the same KMAC instance used in advance calls.
The only difference is that the input messages are 0-padded to another length parameter, `GenDataWidth`.

Key generation request is invalid and return operation error in the following cases:
* The internal FSM is not in `Available` state. Namely, keymgr_dpe rejects key generation requests during `Invalid`/`Disabled` as they are inactive states, and during `Reset` for not having latched the UDS key yet.
* The selected source slot is not valid.

### Erase slot

Erasing operation can be used to clear the DICE context from a destination slot. This is done by selecting the slot with `CONTROL_SHADOWED.DST_SEL`, and then configuring and initiating the operation. At the end of a successful erase, the DPE context is removed from the destination slot.

Note that it is also possible to use the occupied slot as the destination of an operation call, there erase operation might not be always required to empty slots. Its existence is for the sake of security.

Erase request returns an error for either of the following cases:
* The destination slot is already empty/inactive.
* keymgr_dpe FSM's working state is not `Available`.

### Disable

## Peripheral Connections

### KDF Details

KDF used for advance calls is the KMAC instance with (keylen=256, digest_len=384, sec_lvl = 256) parameters. The input messages to KDF are always 0-padded to the fixed length specified below.

During advance operations, KDF inputs are 0 padded to `AdvDataWidth` bits. Depending on the boot stage, KDF message input also receives the following inputs:
* `hw_revision_seed` is a 256-bit netlist constant.
* `device_identifier` is a 256-bit non-secret device identifier. This value is received from peripheral OTP port.
* `health_st_measurement` is a 128-bit domain separator (i.e. diversification constant) that depends on the life cycle stage. This value is received from peripheral LC port.
* `rom_descriptors` are two hash values for ROM0, ROM1. Each digest is 256-bits. These values are received from their respective ROM controllers.
* `creator_seed` is 256-bit creator secret received from the `SECRET2` OTP partition..
* `owner_seed` is 256-bit owner secret received from the `SECRET3` OTP partition.

During key generation operations, KDF inputs are 0 padded to `GenDataWidth` bits. Some diversification constants are:
* `dest_seed` is a 256-bit diversification value for each cryptograhic key type {AES, KMAC, OTBN}.
* `output_key` is a 256-bit diversification value for distinguishing software and sideload keys.

### Life Cycle Connection
The function of the key manager is directly managed by the [life cycle controller](../../lc_ctrl/README.md#key_manager_en).

Until the life cycle controller activates the key manager, the key manager does not accept any software commands.
Once the key manager is activated by the life cycle controller, it is then allowed to transition to the various states previously [described](#key-manager-states).

When the life cycle controller deactivates the key manager, the key manager transitions to the `Invalid` state.
