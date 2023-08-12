# Theory of Operation

Key manager behavior can be summarized by the functional model below.

![Key Manager Functional Model](../doc/keymgr_functional_model.svg)

In the diagram, the red boxes represent the working state and the associated internal key, the black ovals represent derivation functions, the green squares represent software inputs, and the remaining green / purple shapes represent outputs to both software and hardware.

In OpenTitan, the derivation method selected is [KMAC](../../kmac/README.md).
Each valid operation involves a KMAC invocation using the key manager internal key and other HW / SW supplied inputs as data.
While KMAC can generate outputs of arbitrary length, this design fixes the size to 256b.

Effectively, the key manager behavior is divided into 3 classes of functions
*  Key manager state advancement
   *  The results are never visible to software and not directly usable by any software controlled hardware

*  Output key generation
   *  Results can be visible to software or consumed by hardware (sideload)

*  Identity / seed generation
   *  Results are always visible to software and used for asymmetric cryptography

In general, the key generation and seed generation functions are identical.
They differ only in how software chooses to deploy the outputs.

For clarity, all commands issued to the key manager by software are referred to as operations.
Transactions refer to the interaction between key manager and KMAC if a valid operation is issued.

## Key Manager State

The key manager working state (red boxes in the functional model) represents both the current state of the key manager as well as its related internal key.
Each valid state (`Initialized` / `CreatorRootKey` / `OwnerIntermediateKey` / `OwnerRootKey`), supplies its secret material as the "key" input to a KMAC operation.
Invalid states, such as `Reset / Disabled` on the other hand, either do not honor operation requests, or supplies random data when invoked.

The data input is dependent on each state, see below.

### Reset
To begin operation, the state must first transition to Initialize.
The advancement from `Reset` to `Initialized` is irreversible during the current power cycle.
Until the initialize command is invoked, the key manager rejects all other software commands.

### Initialized

When transitioning from `Reset` to `Initialized`, random values obtained from the entropy source are used to populate the internal key first.
Then the root key stored in OTP, if valid, is loaded into the internal key.
This ensures that the hamming delta from the previous value to the next value is non-deterministic.
The advancement from `Initialized` to `CreatorRootKey` is irreversible during the current power cycle.

### CreatorRootKey

`CreatorRootKey` is the first operational state of the key manager.
When transitioning from `Initialized` to this state, a KMAC operation is invoked using the `RootKey` as the key (from OTP), and the remaining inputs as data.
The output of the KMAC operation replaces the previous value of the internal key, and the new value becomes the `CreatorRootKey`.

Inputs to the derivation function are:
*  `DiversificationKey`: Secret seed from flash
*  `HealthMeasurement`: Current life cycle state
   *  To avoid a state value corresponding to each life cycle state, the raw life cycle value is not used.
   *  Instead, certain life cycle states diversify the same way.
   *  Please see the life cycle controller for more details.
*  `DeviceIdentifier`: Unique device identification.
*  `HardwareRevisionSecret`: A global design time constant.

Other than the `DiversificationKey` and `HardwareRevisionSecret`, none of the values above are considered secret.

Once the `CreatorRootKey` is reached, software can request key manager to advance state, generate output key or generate output identity.
The key used for all 3 functions is the `CreatorRootKey`.

The advancement from `CreatorRootKey` to the `OwnerIntermediateKey` is irreversible during the current power cycle.

Keymgr reads the root key from OTP in a single clock cycle. It assumes that when keymgr's internal FSM reaches to this clock cycle, OTP root key is already available (`valid` is set to 1). Otherwise, keymgr skips loading the root key.

### OwnerIntermediateKey

This is the second operational state of the key manager.
This state is reached through another invocation of the KMAC operation using the previous internal key, and other inputs as data.
The output of the KMAC operation replaces the previous value of the internal key, and the new value becomes the `OwnerIntermediateKey`.

The relevant data inputs are:
*  `OwnerRootSecret`: Secret seed from flash.
*  `SoftwareBinding`: A software programmed value representing the first owner code to be run.

Once the `OwnerIntermediateKey` is created, software can request key manager to advance state, generate output key or generate output identity.
The key used for all 3 functions is the `OwnerIntermediateKey`.

The advancement from `OwnerIntermediateKey` to the `OwnerRootKey` is irreversible during the current power cycle.

### OwnerRootKey

This is the last operational state of the key manager.
This state is reached through another invocation of the KMAC operation using the previous internal key, and other inputs as data.
The output of the KMAC operation replaces the previous value of the internal key, and the new value becomes the `OwnerRootKey`.

The relevant inputs are:
*   `SoftwareBinding` - A software programmed value representing the owner kernel code.

Once the `OwnerRootKey` is created, software can request key manager to advance state, generate output key or generate output identity.
An advance command invoked from `OwnerRootKey` state simply moves the state to `Disabled`.

The generate output and generate identity functions use `OwnerRootKey` as the KMAC key.
The advancement from `OwnerRootKey` to the `Disabled` is irreversible during the current power cycle.

### Disabled
`Disabled` is a state where the key manager is no longer operational.
Upon `Disabled` entry, the internal key is updated with KMAC computed random values; however, previously generated sideload key slots and software key slots are preserved.
This allows the software to keep the last valid keys while preventing the system from further advancing the valid key.

When advance and generate calls are invoked from this state, the outputs and keys are indiscriminately updated with randomly computed values.
Key manager enters disabled state based on direct invocation by software:
* Advance from `OwnerRootKey`
* Disable operation

### Invalid
`Invalid` state is entered whenever key manager is deactivated through the [life cycle connection](#life-cycle-connection) or when an operation encounters a [fault](#faults-and-operational-faults) .
Upon `Invalid` entry, the internal key, the sideload key slots and the software keys are all wiped with entropy directly.

#### Invalid Entry Wiping
Since the life cycle controller can deactivate the key manager at any time, the key manager attempts to gracefully handle the wiping process.
When deactivated, the key manager immediately begins wiping all keys (internal key, hardware sideload key, software key) with entropy.
However, if an operation was already ongoing, the key manager waits for the operation to complete gracefully before transitioning to invalid state.

While waiting for the operation to complete, the key manager continuously wipes all keys with entropy.

### Invalid and Disabled State

`Invalid` and `Disabled` states are functionally very similar.
The main difference between the two is "how" the states were reached and the entry behavior.

`Disabled` state is reached through intentional software commands where the sideload key slots and software key are not wiped, while `Invalid` state is reached through life cycle deactivation or operational faults where the internal key, sideload key slots and software key are wiped.

This also means that only `Invalid` is a terminal state.
If after entering `Disabled` life cycle is deactivated or a fault is encountered, the same [invalid entry procedure](#Invalid) is followed to bring the system to a terminal `Invalid` state.

If ever multiple conditions collide (a fault is detected at the same time software issues disable command), the `Invalid` entry path always takes precedence.

## Life Cycle Connection
The function of the key manager is directly managed by the [life cycle controller](../../lc_ctrl/README.md#key_manager_en).

Until the life cycle controller activates the key manager, the key manager does not accept any software commands.
Once the key manager is activated by the life cycle controller, it is then allowed to transition to the various states previously [described](#key-manager-states).

When the life cycle controller deactivates the key manager, the key manager transitions to the `Invalid` state.

## Commands in Each State
During each state, there are 3 valid commands software can issue:
*  Advance state
*  Output generation
*  Identity generation

The software is able to select a command and trigger the key manager FSM to process one of the commands.
If a command is valid during the current working state, it is processed and acknowledged when complete.

If a command is invalid, the behavior depends on the current state.
If the current state is `Reset`, the invalid command is immediately rejected as the key manager FSM has not yet been initialized.
If the current state is any other state, the key manager sequences random, dummy data to the KMAC module, but does not update internal key, sideload key slots or software keys.
For each valid command, a set of inputs are selected and sequenced to the KMAC module.

During `Disable` and `Invalid` states, the internal key, sideload key slots and software key are updated based on the input commands as with normal states.
There are however a few differences:
-  The updates are made regardless of any error status to ensure their values are further scrambled.
-  Instead of normal input data, random data is selected for KMAC processing.
-  All operations return an invalid operations error, in addition to any other error that might naturally occur.

## Generating Output Key
The generate output command is composed of 2 options
*  Generate output key for software, referred to as `generate-output-sw`
*  Generate output key for hardware, referred to as `generate-output-hw`

The hardware option is meant specifically for symmetric sideload use cases.
When this option is issued, the output of the KMAC invocation is not stored in software visible registers, but instead in hardware registers that directly output to symmetric primitives such as AES, KMAC and OTBN.

## KMAC Operations
All invoked KMAC operations expect the key in two shares.
This means the internal key, even though functionally 256b, is maintained as 512b.
The KMAC processed outputs are also in 2-shares.
For `generate-output-sw` commands, software is responsible for determining whether the key manager output should be preserved in shares or combined.

## Errors, Faults and Alerts

The key manager has two overall categories of errors:
* Recoverable errors
* Fatal errors

Recoverable errors are those likely to have been introduced by software and not fatal to the key manager or the system.
Fatal errors are logically impossible errors that have a high likelihood of being a fault and thus fatal.

Each category of error can be further divided into two:
* Synchronous errors
* Asynchronous errors

Synchronous errors happen only during a key manager operation.
Asynchronous errors can happen at any time.

Given the above, we have 4 total categories of errors:
* Synchronous recoverable errors
* Asynchronous recoverable errors
* Synchronous fatal errors
* Asynchronous fatal errors

All recoverable errors (synchronous and asynchronous) are captured in [`ERR_CODE`](registers.md#err_code).
All fatal errors (synchronous and asynchronous) are captured in [`FAULT_STATUS`](registers.md#fault_status).

Recoverable errors cause a recoverable alert to be sent from the key manager.
Fatal errors cause a fatal alert to be sent from the key manager.

Below, the behavior of each category and its constituent errors are described in detail.

### Synchronous Recoverable Errors

These errors can only happen when a key manager operation is invoked and are typically associated with incorrect software programming.
At the end of the operation, key manager reports whether there was an error in [`ERR_CODE`](registers.md#err_code) and sends a recoverable alert.

* [`ERR_CODE.INVALID_OP`](registers.md#err_code) Software issued an invalid operation given the current key manager state.
* [`ERR_CODE.INVALID_KMAC_INPUT`](registers.md#err_code) Software supplied invalid input (for example a key greater than the max version) for a key manager operation.

### Asynchronous Recoverable Errors

These errors can happen at any time regardless of whether there is a key manager operation.
The error is reported in [`ERR_CODE`](registers.md#err_code) and the key manager sends a recoverable alert.

* [`ERR_CODE.INVALID_SHADOW_UPDATE`](registers.md#err_code) Software performed an invalid sequence while trying to update a key manager shadow register.

### Synchronous Fatal Errors

These errors can only happen when a key manager operation is invoked and receives malformed operation results that are not logically possible.
At the end of the operation, key manager reports whether there was an error in [`FAULT_STATUS`](registers.md#fault_status) and continuously sends fatal alerts .

Note, these errors are synchronous from the perspective of the key manager, but they may be asynchronous from the perspective of another module.

### Asynchronous Fatal Errors

These errors can happen at any time regardless of whether there is a key manager operation.
The error is reported in [`FAULT_STATUS`](registers.md#fault_status) and the key manager continuously sends fatal alerts.


### Faults and Operational Faults

When a fatal error is encountered, the key manager transitions to the `Invalid` [state](#invalid-entry-wiping).
The following are a few examples of when the error occurs and how the key manager behaves.

#### Example 1: Fault During Operation
The key manager is running a generate operation and a non-onehot command was observed by the KMAC interface.
Since the non-onehot condition is a fault, it is reflected in [`FAULT_STATUS`](registers.md#fault_status) and a fatal alert is generated.
The key manager transitions to `Invalid` state, wipes internal storage and reports an invalid operation in [`ERR_CODE.INVALID_OP`](registers.md#err_code).

#### Example 2: Fault During Idle
The key manager is NOT running an operation and is idle.
During this time, a fault is observed on the regfile (shadow storage error) and FSM (control FSM integrity error).
The faults are reflected in [`FAULT_STATUS`](registers.md#fault_status).
The key manager transitions to `Invalid` state, wipes internal storage but does not report an invalid operation.

#### Example 3: Operation after Fault Detection
Continuing from the example above, the key manager now begins an operation.
Since the key manager is already in `Invalid` state, it does not wipe internal storage and reports an invalid operation in [`ERR_CODE.INVALID_OP`](registers.md#err_code).

#### Additional Details on Invalid Input

What is considered invalid input changes based on current state and operation.

When an advance operation is invoked:
- The internal key is checked for all 0's and all 1's.
- During `Initialized` state, creator seed, device ID and health state data is checked for all 0's and all 1's.
- During `CreatorRootKey` state, the owner seed is checked for all 0's and all 1's.
- During all other states, nothing is explicitly checked.

When a generate output key operation is invoked:
- The internal key is checked for all 0's and all 1's.
- The key version is less than or equal to the max key version.

When a generate output identity is invoked:
- The internal key is checked for all 0's and all 1's.

#### Invalid Operation

The table below enumerates the legal operations in a given state.
When an illegal operation is supplied, the error code is updated and the operation is flagged as `done with error`.

| Current State    | Legal Operations               |
| -------------    | ------------------------------ |
| Reset            | Advance                        |
| Initialized      | Disable / Advance              |
| CreatorRootKey   | Disable / Advance / Generate   |
| OwnerIntKey      | Disable / Advance / Generate   |
| OwnerRootKey     | Disable / Advance / Generate   |
| Invalid/Disabled | None                           |

*  All operations invoked during `Invalid` and `Disabled` states lead to invalid operation error.

### Error Response
In addition to alerts and interrupts, key manager may also update the internal key and relevant outputs based on current state.
See the tables below for an enumeration.

| Current State    | Invalid States  | Invalid Output | Invalid Input | Invalid Operation   |
| -------------    | ----------------| ---------------|---------------|---------------------|
| Reset            | Not Possible    | Not Possible   | Not possible  | Not updated         |
| Initialized      | Updated         | Updated        | Not updated   | Not updated         |
| CreatorRootKey   | Updated         | Updated        | Not updated   | Not possible        |
| OwnerIntKey      | Updated         | Updated        | Not updated   | Not possible        |
| OwnerRootKey     | Updated         | Updated        | Not updated   | Not possible        |
| Invalid/Disabled | Updated         | Updated        | Updated       | Updated             |

*  During `Reset` state, the KMAC module is never invoked, thus certain errors are not possible.
*  During `Initialized`, `CreatorRootKey`, `OwnerIntermediateKey` and `OwnerRootKey` states, a fault error causes the relevant key / outputs to be updated; however an operational error does not.
*  During `Invalid` and `Disabled` states, the relevant key / outputs are updated regardless of the error.
*  Only the relevant collateral is updated -> ie, advance / disable command leads to working key update, and generate command leads to software or sideload key update.
*  During `Disabled` state, if life cycle deactivation or an operational fault is encountered, the key manager transitions to `Invalid` state, see [here](#invalid-and-disabled-state)

## DICE Support

The key manager supports [DICE open profile](https://pigweed.googlesource.com/open-dice/+/HEAD/docs/specification.md#Open-Profile-for-DICE).
Specifically, the open profile has two compound device identifiers.
* Attestation CDI
* Sealing CDI

The attestation CDI is used to attest hardware and software configuration and is thus expected to change between updates.
The sealing CDI on the other hand, is used to attest the authority of the hardware and software configuration.
The sealing version is thus expected to remain stable across software updates.

To support these features, the key manager maintains two versions of the working state and associated internal key.
There is one version for attestation and one version for sealing.

The main difference between the two CDIs is the different usage of `SW_BINDING`.
For the Sealing CDI, the [`"SEALING_SW_BINDING"`](registers.md#sealing_sw_binding) is used, all other inputs are the same.
For the Attestation CDI, the [`"ATTEST_SW_BINDING"`](registers.md#attest_sw_binding) is used, all other inputs are the same.

When invoking an advance operation, both versions are advanced, one after the other.
There are thus two KMAC transactions.
The first transaction uses the Sealing CDI internal key, [`"SEALING_SW_BINDING"`](registers.md#sealing_sw_binding) and other common inputs.
The second transaction uses the Attestation CDI internal key, [`"ATTEST_SW_BINDING"`](registers.md#attest_sw_binding) and other common inputs.

When invoking a generate operation, the software must specify which CDI to use as the source key.
This is done through [`"CONTROL.CDI_SEL"`](registers.md#control).
Unlike the advance operation, there is only 1 KMAC transaction since we pick a specific CDI to operate.

When disabling, both versions are disabled together.


## Block Diagram
The following is a high level block diagram of the key manager.

![Key Manager Block Diagram](../doc/keymgr_block_diagram.svg)

## Design Details

Key manager is primarily composed of two components:
*  keymgr_ctrl
*  keymgr_kmac_if

### Key Manager Control

The key manager control block manages the working state, sideload key updates, as well as what commands are valid in each state.
It also handles the life cycle `keymgr_en` input, which deactivates the entire key manager function in the event of an escalation.

![Key Manager Control Block Diagram](../doc/keymgr_control_diagram.svg)


### KMAC Interface Control

The KMAC interface control represents the bulk of key manager logic.
Based on input from key manager control, this module selects the inputs for each given command and sequences the data to KMAC.

![Key Manager KMAC Interface Block Diagram](../doc/keymgr_kmac_if_diagram.svg)

The KMAC interface works on a simple `valid / ready` protocol.
When there is data to send, the KMAC interface sends out a `valid` and keeps it active.
When the destination accepts the transaction, the `ready` is asserted.
Note just like with any bus interface, the `ready` may already be asserted when `valid` asserts, or it may assert some time later, there are no restrictions.
Since the data to be sent is always pre-buffered in key manager, the valid, once asserted, does not de-assert until the entire transaction is complete.

The data interface itself is 64b wide.
However, there may not always be 64b multiple aligned data to be sent.
In these situations, the last transfer beat sent to KMAC has a byte mask / strobe attached.
The byte mask indicates on the last beat which bytes are actually valid, and which are not.
Not beats prior to the last always have fully asserted byte masks.

Once KMAC receives all the required data and the last indication, it begins processing the data into a digest.
This process may take an arbitrary number of cycles.
When this process is complete, a `done` indication pulse is sent back with the digest.
Note, the acceptance of `done` has no back-pressure and `keymgr` must accept it within one cycle.

See diagram below for an example transfer:

```wavejson
{signal: [
  {name: 'kmac_data_o.valid',     wave: '01...........|....0..'},
  {name: 'kmac_data_i.ready',     wave: '1...0..101...|.......'},
  {name: 'kmac_data_o.data',      wave: 'x2222...2.222|2222x..'},
  {name: 'kmac_data_o.last',      wave: '0................10..'},
  {name: 'kmac_data_o.strb',      wave: 'x2...............2x..'},
  {name: 'kmac_data_i.done',      wave: '0..................10'},
  {name: 'kmac_data_i.digest*',   wave: 'x..................3x'},
  ],
}
```

### Sideload Keys

There are three sideload keys.
One for AES, one for KMAC and one for OTBN.
When a sideload key is generated successfully through the `generate-output-hw` command, the derived data is loaded into key storage registers.
There is a set of storage registers for each destination.

The KMAC key however is further overloaded as it is the main derivation mechanism for key manager internal stage.
The KMAC key thus has two possible outputs, one is the sideload key, and the other is internal state key.

When a valid operation is called, the internal state key is sent over the KMAC key.
During all other times, the sideloaded value is presented.
Note, there may not be a valid key in the sideload register if it has been cleared or never generated.
The sideload key can be overwritten with another generate command, or cleared with entropy through [`SIDELOAD_CLEAR`](registers.md#sideload_clear).

The clearing can be done one slot at a time, or all at once.
Once a clearing bit is enabled for a particular key slot, its value is continuously re-randomized every clock cycle.
Therefore, SW is responsible for toggling this bit back to disabled state, which makes the last random value remain stable on the sideload slot.
Otherwise, the sideload key slot is continuously randomized which prevents sideloading an actual key to the target HWIP.

The following diagram illustrates an example when there is no valid key in the KMAC sideload registers and an operation is called.
During the duration of the operation, the key is valid and shows the internal key state.
Once the operation is complete, it falls back to the sideload key state, which is invalid in this case.

```wavejson
{signal: [
  {name: 'u_sideload_ctrl.u_kmac_key.key_o.valid',     wave: '0................'},
  {name: 'u_sideload_ctrl.u_kmac_key.key_o.key_share', wave: 'x................'},
  {name: 'u_ctrl.key_o.valid',                         wave: '0................'},
  {name: 'u_ctrl.key_o.key_share',                     wave: 'x................'},
  {name: 'u_ctrl.op_start_i',                          wave: '0....1.....0.....'},
  {name: 'kmac_key_o.valid',                           wave: '0....1.....0.....'},
  {name: 'kmac_key_o.key_share*',                      wave: 'x....3.....x.....'},
  ],
}
```

The following diagram illustrates an example when there is a valid key in the KMAC sideload registers and an operation is called.
During the duration of the operation, the key is valid and shows the internal key state.
Once the operation is complete, it falls back to the sideload key state, which is valid and contains a different value.

```wavejson
{signal: [
  {name: 'u_sideload_ctrl.u_kmac_key.key_o.valid',     wave: '01...............'},
  {name: 'u_sideload_ctrl.u_kmac_key.key_o.key_share', wave: 'x4...............'},
  {name: 'u_ctrl.key_o.valid',                         wave: '0....1.....0.....'},
  {name: 'u_ctrl.key_o.key_share',                     wave: 'x................'},
  {name: 'u_ctrl.op_start_i',                          wave: '0....1.....0.....'},
  {name: 'kmac_key_o.valid',                           wave: '01...............'},
  {name: 'kmac_key_o.key_share*',                      wave: 'x4...3.....4.....'},
  ],
}
```


### Software Binding

The identities flow employs an idea called [software binding](https://docs.opentitan.org/doc/security/specs/identities_and_root_keys/#software-binding) to ensure that a particular key derivation scheme is only reproducible for a given software configuration.
The binding is created through the secure boot flow, where each stage sets the binding used for the next verified stage before advancing to it.
The software binding is used during the following state transitions only:
-  `Initialized` to `CreatorRootKey`
-  `CreatorRootKey` to `OwnerIntermedaiteKey`
-  `OwnerIntermediateKey` to `OwnerRootKey`

In order to save on storage and not have a duplicate copy per stage, the software binding registers [`SOFTWARE_BINDING`](registers.md#software_binding) are shared between key manager stages.

Software sets the appropriate values and locks it by clearing [`SOFT_BINDING_EN`](registers.md#soft_binding_en).
When later a successful `advance` call is made, the key manager then unlocks by setting [`SOFT_BINDING_EN`](registers.md#soft_binding_en) to 1.
An unsuccessful advance call (errors) does not unlock the binding.
This allows the next stage of software to re-use the binding registers.

### Custom Security Checks

The keymgr has several custom security checks.

#### One-Hot Command Check
The command received by the KMAC interface must always be in one-hot form and unchanging during the life time of a KMAC transaction.
If this check fails, an error is reflected in [`FAULT_STATUS.CMD`](registers.md#fault_status).

#### Unexpected KMAC Done
The `kmac_done` signal can only happen during the expected transaction window.
If this check fails, an error is reflected in [`FAULT_STATUS.KMAC_DONE`](registers.md#fault_status).

#### Control State Machine Check
This error checks for two things:
-  The key manager can advance to one of the key states (e.g. RootKey, OwnerIntermediateKey) only when there is a legal advanced operation.
-  The key manager can issue an advance or generate operation to the KMAC interface only if the original software request is an advanced or generate command.

If these checks fail, an error is reflected in [`FAULT_STATUS.CTRL_FSM_CHK`](registers.md#fault_status).

#### Sideload Select Check
A sideload key slot is selected for update only if the original software request targeted that key slot.

If this check fails, an error is reflected in [`FAULT_STATUS.SIDE_CTRL_SEL`](registers.md#fault_status).
