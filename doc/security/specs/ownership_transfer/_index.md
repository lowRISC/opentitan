---
title: "Ownership Transfer"
---

## Overview

The Silicon Owner is defined as a logical entity or entities allowed to sign
code for execution, as well as to sign ownership management commands[^1].
OpenTitan supports the following device life cycle states to manage the
ownership state of the device:

*   _UNOWNED_: The device is ready to be assigned to a new owner.
*   _OWNED_: The device is assigned to an owner and in operational mode.

This document defines the ownership management functions that control the
transitions between ownership states:

### Unlock Ownership {#unlock-ownership-top}

Implements transition from `OWNED` to `UNOWNED` state. The device must be in
`UNOWNED` state before it can be assigned to a new owner.

### Ownership Transfer (or Ownership Assignment) {#ownership-transfer-top}

Implements transition from `UNOWNED` to `OWNED` stage. The rest of this document
refers to this functionality as Ownership Transfer. The following keys are
provisioned as part of this flow:

Key        | Description
---------- | --------------------------------------------------------
CODE_SIGN  | Used to verify the Silicon Owner first bootloader stage.
UNLOCK     | Used to authenticate the Unlock Ownership command.
NEXT_OWNER | Used to authenticate the Ownership Transfer command.

The `UNLOCK` and `NEXT_OWNER` keys are required to ensure ownership state
transitions are only triggered by authenticated and authorized commands.
Authorization is implemented via key identification (`UNLOCK` versus
`NEXT_OWNER`).

<!-- TODO: Add link to Identities and Root Keys doc -->

Transition into `OWNED` stage results in a new device [Owner Identity](#), used
in attestation and post-ownership-transfer application provisioning flows.

There are three modes of ownership transfer supported:

*   **Silicon Creator endorses Next Owner**: The Silicon Creator signs the set
    of public keys associated with the next owner as part of the ownership
    transfer flow.
*   **Current Owner endorses Next Owner**: The Current Owner signs the set of
    keys associated with the next owner as part of the ownership transfer flow.
*   **Fixed Owner**: In this case a single owner is provisioned on the device
    and ownership transfer is disabled via manufacturing SKU configuration.

## Terminology

Boot stages:

*   `ROM`: Metal mask ROM, sometimes known as Boot ROM.
*   `ROM_EXT`: ROM Extension. Stored in flash and signed by the Silicon Creator.
*   Owner boot stages. This document uses two stages as an example. The Silicon
    Owner is free to choose other boot configurations.
    *   `BL0`: Bootloader. Signed by the Silicon Owner.
    *   `KERNEL`: Signed by the Silicon Owner.

## Key Provisioning {#key-provisioning}

As part of the Ownership Transfer flow, the Silicon Owner keys are endorsed
either by the Silicon Creator or by the Current Owner of the device. This is
done to ensure that only authenticated and authorized entities are able to take
ownership of the device.

### Key Endorsement Format

Key endorsement is implemented as a signed manifest. The rest of the document
refers to this as the Key Endorsement Manifest, or manifest for simplicity. The
following fields must be supported by the manifest implementation:

#### signature

Signature covering the signed manifest. The number of bytes depends on the
`signature_algorithm` field.

#### signature_algorithm

Must match the signature algorithm used by the secure boot configuration. The
following list is not exhaustive, and may change based on the implementation.
The implementation shall choose the appropriate signature verification scheme
based on the secure boot security level requirements.

RSA 3072:

*   `pkcs1-v1_5-with-sha-2-256`
*   `pkcs1-v1_5-with-sha-2-512`
*   `pkcs1-v1_5-with-sha-3-256`
*   `pkcs1-v1_5-with-sha-3-384`
*   `pkcs1-v1_5-with-sha-3-512`

#### public_key

Public key to verify the signature with. The number of bytes depends on the
`signature_algorithm` field. Depending on the ownership transfer model, the
public key must match one of the following requirements:

 Endorsing Entity | Public Key Requirement                                   
 ---------------- | --------------------------------------------------------
 Silicon Creator  | The public key must be stored in the ROM_EXT and  integrity protected by the ROM_EXT signature.
 Previous Owner   | The public key must be stored in the previous owner slot and labeled as the `NEXT_OWNER` in the policy field. See `owner_keys` for more details.

#### owner_keys (array)

List of public keys endorsed by the manifest. The format of the public key
descriptor depends on the `signature_algorithm` field. For example, RSA-3072
with `pkcs1-v1_5-with-sha-2-256` contains the following fields:

*   `public_key`: RSA (N|e) parameters.
*   `policy`: Key usage policy, bitmap decoded to one or more of the following:
    *   `CODE_SIGN`: Key used to verify the Silicon Owner first bootloader
        stage.
    *   `UNLOCK`: Key used to verify [unlock ownership](#unlock-ownership-top)
        commands.
    *   `NEXT_OWNER`: Used to verify
        [ownership assignment](#ownership-transfer-top) commands, using the
        proposed key endorsement manifest format.

#### Optional Parameters

The following parameters are required in the secure boot manifest
implementation, but are left as optional in the key endorsement manifest. The
Silicon Creator or previous Silicon Owner may want to implement these parameters
to restrict the deployment of the endorsed keys.

Note: If implemented, the restrictions imposed by these fields cannot be revoked
by ownership transfer once provisioned. This is to simplify the implementation
of an open samples policy.

##### otp_settings

Minimum list of fuses that must match the device configuration before committing
the endorsed keys to flash. The hash of the list of targeted fuse values is
hashed with the endorsement manifest before signing.

Note: The device identifier fuses can be added to the `otp_settings` to restrict
the keys to be used with a single device. This mode of operation is referred to
as node-locked secure boot configuration.

### Device Key Provisioning Flow

The following figure shows the sequence of operations to commit the new set of
keys once the key endorsement manifest has been verified.

Definitions:

*   `slot`: Owner slot. This implementation assumes that there are only 2 owner
    slots, so the only valid values are 0 and 1.
*   `id`: The owner assignment identifier. It is implemented as a monotonically
    increasing counter. The new owner id is equivalent to N + 1 for a previous
    owner id of N.
*   `pub_keys`: List of keys associated with the owner slot. Includes key policy
    information.
*   `digest`: Integrity of the owner slot record calculated as `MAC(Kn,
    slot|id|pub_keys)`. The key (`Kn`) requirements are described later in more
    detail.

<table>
  <tr>
    <td>
      <img src="ownership_transfer_fig1.svg" width="900" alt="fig1">
    </td>
  </tr>
  <tr>
    <td>Figure: Provisioning sequence versus owner slots.</td>
  </tr>
</table>

Detailed description:

**Step 1 (S1) Initial State**

The current owner is stored in slot 0 and the device is in unlocked ownership
state. A key stored in the current owner slot (0) is used to validate the key
endorsement manifest for the next owner.

**Step 2 (S2) Intermediate State**

The new owner keys are written into the available owner slot - in this case slot
one. The `pub_keys` and `digest` parameters are written before the `id`. Once the
`id`is written into flash, the new owner slot entry is considered to be valid.

The `id` parameter must be strictly greater than the previous owner `id`.

**Step 3 (S3) Final State**

An additional integrity check over the new owner slot is performed before
completing provisioning of the new owner keys. Upon successful verification, the
new owner is marked as the current owner by deleting the `id` of the previous
owner. The `pub_keys` of the previous owner may be deleted as well as part of
this step.

#### Integrity Key (Kn, Kn+1)

Integrity keys are used to implement integrity checks for each owner slot. The
integrity key has the following requirements:

*   IK_REQ1: The key shall be unique per owner slot and ownership configuration.
*   IK_REQ2: The key can only be computed by a trusted `ROM_EXT` boot
    configuration.
*   IK_REQ3: The key only available to the `ROM`/`ROM_EXT`.

These requirements can be achieved by a combination of physical security and
cryptographic guarantees. The following example demonstrates how to derive the
Integrity Key from a symmetric key stored in OTP and only available to
`ROM`/`ROM_EXT` software.

##### Key Step Function - MAC

This approach relies on a symmetric secret (`K`) managed by the `ROM`/`ROM_EXT`
software. It is intended to mitigate boot time issues associated with consuming
`K` directly from the key manager.

Parameters:

*   `K`: Device integrity secret provisioned at manufacturing time. Only visible
    to ROM and ROM_EXT software. Stored in OTP.
*   `slot`: Owner slot. This implementation assumes that there are only 2 owner
    slots, so the only valid values are 0 and 1. This parameter is used to make
    sure the key cannot be reused to verify the other slot.
*   `n`: The owner assignment identifier. It is implemented as a monotonically
    increasing counter. It is used here to bind the key to the owner identifier.
*   `prev_owner_digest`: (Under consideration) Digest of the previous owner
    (e.g. `id = n - 1`). Used to bind the key to the custody chain (chain of
    owners).

Function: `MAC` is an OpenTitan approved MAC function.

```
Kn = MAC(K, "OwnerSlot" | slot | n | prev_owner_digest)
```

The slot and n values are used to fulfill the IK_REQ1 requirement. The
availability of `K` is enforced by software to fulfill IK_REQ2 and IK_REQ3.
`prev_owner_digest` is under consideration to bind the key to the custody chain
(chain of ownership).

#### Additional Requirements

**Key Manager Availability**

The `ROM_EXT` is required to disable the key manager before handing over
execution to the next boot stage when the device is in device `UNLOCKED`
ownership state.

**Manufacturing Requirements**

Determine if the `prev_owner_digest` field must be initialized with non-zero
value at manufacturing time.

## OpenTitan Device Mode

A host can send unlock ownership and ownership transfer commands to OpenTitan
via any physical interface supported by the `ROM_EXT`. The details of the
command transport layer protocol, as well as the list of supported physical
devices are left to the reference software implementation.

However, there must be at least one mechanism available to perform ownership
transfer at manufacturing time using an implementation compatible with ATE[^2]
infrastructure.

### Unlock Ownership {#unlock-ownership}

This flow implements transition from `OWNED` to `UNOWNED` ownership states. It
is used by the Silicon Owner to relinquish ownership of the device and enable
ownership transfer functionality. The device must be in `UNOWNED` state before
it can be assigned to a new owner.

The unlock operation is implemented as a signed command sent from the
Kernel/Application layer to the `ROM_EXT`. The signature is required to allow
the current owner to only allow authenticated and authorized users access to the
unlock ownership flow.

The following fields must be supported by the command:

#### signature

Signature covering the command structure. The signature is verified using the
`UNLOCK` key stored in the active owner slot.

#### unlock_nonce

Ownership-unlock nonce value, which is generated at the time the current owner
first took ownership of the device.

*   The nonce is expected to be unique per device and ownership assignment.
*   The nonce is stored to make the unlock command re-triable (and fault
    tolerant).
*   The nonce may be readable from any boot stage to simplify the unlock
    operation.

#### flags

Additional flags passed to the `ROM_EXT` to configure unlock flow settings:

*   `WIPE_FLASH`: Erase owner flash contents on successful unlock operation.

<strong>Example</strong>

The following sequence diagram shows a reference implementation of the unlock
flow. Error handling is omitted for simplicity.

<table>
  <tr>
    <td>
      <img src="ownership_transfer_fig2.svg" width="900" alt="fig2" >
    </td>
  </tr>
  <tr>
    <td>Figure: Device unlock</td>
  </tr>
</table>

Detailed description:

**Step 1 (S1) Get unlock nonce and device id**: The Host queries the device
identifier and unlock nonce from the device.

**Steps 2-4 (S2, S3, S4) Request unlock command signature**: The Host requests
the Device Registry service to sign the unlock ownership command for the device
id with provided nonce. The Device Registry requests a cloud key manager service
to sign the command with a key associated with the device identifier. The
signature must be verifiable with the `UNLOCK` key stored in the active owner
slot.

**Step 5 (S5) Request device unlock**: The Host sends the unlock ownership
command to the Device. The command is first handled by the Kernel/APP layer.

**Step 6 (S6) Pre-unlock steps**: The Kernel/APP layer may verify the unlock
command and execute any pre-unlock steps, including erasing owner level secrets.

**Step 7 (S7) Request device unlock**: The Kernel copies the unlock command to a
boot services memory region shared with the `ROM_EXT`, and performs a reset to
trigger the unlock operation on the next boot.

**Step 8 (S8) Unlock steps**: The `ROM_EXT` verifies the unlock command and
updates the device state to `UNOWNED` state. The Device proceeds with the boot
flow and reports the unlock result to the kernel via shared memory.

**Step 9 (S9) Unlock result**: The unlock result is first propagated to the
Device Kernel/APP layer. The Kernel may opt to execute any post-unlock steps
before propagating the result to the Host. The Host propagates the unlock result
to the Device Registry. The Device Registry may opt to remove the device from
its allow-list.

### Ownership Transfer {#ownership-transfer-device}

An ownership transfer command sent by a host to OpenTitan, is serviced by the
ROM extension (`ROM_EXT`) allowing the Silicon Owner to take ownership of the
device at silicon manufacture, Contract Manufacturing (CM) stage or in the
field.

<table>
  <tr>
    <td>
      <img src="ownership_transfer_fig3.svg" width="300" alt="fig3" >
    </td>
  </tr>
  <tr>
    <td>Figure: Ownership Transfer supported by ROM_EXT</td>
  </tr>
</table>

<table>
  <tr>
    <td><strong>Step</strong></td>
    <td><strong>Description</strong></td>
  </tr>
  <tr>
    <td>Unowned state</td>
    <td>

Entry into the ownership transfer flow is conditional to the device being in
`UNOWNED` state. See [Unlock Flow](#unlock-ownership) for more details on how
to transition from OWNED to UNOWNED states.
    </td>
  </tr>
  <tr>
    <td>Verify payload header</td>
    <td>

The ownership transfer payload header including the key endorsement manifest is
verified by the ROM extension. The *header shall fit within available SRAM* and
be signed by an approved key as described in the
[Key Provisioning](#key-provisioning) section.
    </td>
  </tr>
  <tr>
    <td>Flash erase</td>
    <td>

Code, data and info pages available to the Silicon Owner are erased. Erase
checks are performed.
   </td>
  </tr>
  <tr>
    <td>Reset secrets</td>
    <td>
    <!-- TODO: Link to Identities and Root Keys document -->

The [OwnerRootSecret](#) is reset with a value extracted from a DRBG configured
with a security strength equivalent to one supported by the key manager.
    </td>
  </tr>
  <tr>
    <td>Rotate unlock nonce</td>
    <td>

A 64bit random value is extracted from the DRBG to be used as an unlock nonce.
See [Unlock Flow](#unlock-flow) for more details.
    </td>
  </tr>
  <tr>
    <td>Provision owner keys</td>
    <td>

Owner keys are provisioned into the device as defined in the
[Key Provisioning](#key-provisioning) section.
    </td>
  </tr>
  <tr>
    <td>Flash image</td>
    <td>Owner software is written into one of the flash partitions.</td>
  </tr>
  <tr>
    <td>Activate owner</td>
    <td>

Owner software sends a command to the `ROM_EXT` to complete ownership transfer,
which effectively sets the new owner as the current owner.
    </td>
  </tr>
</table>

## OpenTitan Host Mode

Some of the OpenTitan use cases require support for self updates in which
OpenTitan is used in host mode to scan an external device interface for update
payloads. This section describes Ownership Transfer layered on top of such self
update mechanism.

An OpenTitan implementation may support this ownership transfer model at the SKU
level.

### Unlock Ownership

The Device is initially in `OWNED` state and configured with a stack signed by
the current owner. The following steps must be implemented in a fault tolerant
way:

1.  The Device is updated to a stack able to support the ownership transfer
    implementation as described in the next section. The owner may opt for
    clearing any device secrets as part of this step.
2.  Ownership unlock is performed as described in the OpenTitan device mode
    [Unlock Flow](#unlock-flow) section.

### Ownership Transfer

In this section, SPI EEPROM is used as the target device. However, the
implementation may opt for supporting other targets.

The Device is initially in `UNOWNED` state and configured with a stack (Kernel +
APPs) able to scan an external SPI EEPROM and trigger the ownership transfer
flow. The following procedure also assumes that the Device storage follows the
internal [flash layout](#flash-layout) guidelines.

The process must be implemented in a fault tolerant manner to be able to restart
the process to recover from a failed attempt.

Detailed steps:

1.  The current owner endorses the next owner keys as described in the
    [Key Endorsement](#key-endorsement) section.
2.  The next owner writes the key endorsement manifest to the external EEPROM
    followed by an update payload. The update payload includes all the silicon
    owner boot stages.
3.  The Device kernel module or application in charge of performing ownership
    transfer, referred to as _the application_, is activated upon detecting the
    `UNOWNED` ownership state at Device boot time.
4.  The application scans the external EEPROM for a valid key endorsement
    manifest and update payload. The key endorsement manifest is validated with
    the current owner’s `NEXT_OWNER` key. The update payload is validated with
    one of the `CODE_SIGN` keys embedded in the key endorsement manifest.
5.  The application writes the inactive embedded flash code partitions with the
    ones included in the update payload.
    *   Note: In order to avoid a BL0 (bootloader) fixed flash size allocation
        across all owners, the implementation may opt to support the following:
        1.  The boot flow will give preference to the next boot stage residing
            in the same flash bank if both A and B versions are the same.
        2.  The A/B flash layout may contain two identical copies of the stack
            at the start of the process to make sure it is possible to boot from
            a single flash bank.
6.  The application loads the key endorsement manifest into the boot services
    shared memory region and triggers a reset to perform ownership transfer on
    the next boot cycle.
7.  The `ROM_EXT` executes the ownership transfer flow described in the
    [Ownership Transfer](#ownership-transfer-device) section with the following
    differences:
    1.  Flash erase and flash image stages are not executed.
    2.  The activate owner stage may be delayed and executed later depending on
        the implementation.
8.  The `ROM_EXT` attempts to boot the new owner image with the new owner
    configuration.
9.  On the first boot, the new owner image queues an activate owner command,
    which is then executed by the `ROM_EXT` on the next boot. The new owner
    becomes the current owner.
10. The previous owner code partitions can be erased at this point.
11. Device attestation can be performed after this point.

## Ownership Transfer Disabled

Ownership Transfer can be disabled at the SKU level. In this case secure boot is
implemented by storing the Silicon Owner BL0 verification keys in the `ROM_EXT`.
The `ROM_EXT` is thus not required to implement ownership transfer in this
configuration.

## Flash Layout {#flash-layout}

To simplify the implementation, the flash layout implements fixed offset and
size allocations for the `ROM_EXT` and the certificate storage regions. This
allows the flash erase and write operations to be performed at deterministic
address ranges.

The implementation may opt to store the certificates in info regions to save
data partition space.

<table>
  <tr>
    <td>
      <img src="ownership_transfer_fig4.svg" width="900" alt="fig4" >
    </td>
  </tr>
  <tr>
    <td>Figure: Flash layout</td>
  </tr>
</table>

`owner_slot_0` and `owner_slot_1` are used to store the Silicon Owner keys as
described in the [Key Provisioning](#key-provisioning) section.

## Attestation Update

<!-- TODO: Link to Attestation specification document -->

Regular attestation updates as described in the [Attestation](#) specification
are available when the device has an active owner. Devices in ownership
`UNOWNED` state may have restricted attestation capabilities, for example,
restricted to only end-to-end attestation.

## Ownership Transfer During Manufacturing

Manufacturing shall not preclude the implementation of the following default
stack configurations:

<!-- TODO: Update links to device life cycle specification doc.  -->

*   [`OWNED`](#) state with default factory image.
*   [`UNOWNED`](#) (unlocked) state with default factory image.
*   [`OWNED`](#) state with default factory image and Ownership Transfer
    disabled.

Factory software may be used to configure the ownership slots before injecting
the factory image.

<!-- Footnotes themselves at the bottom. -->

## Notes

[^1]: https://docs.opentitan.org/doc/security/logical_security_model/#silicon-owner

[^2]: Automatic Test Equipment used at package level testing.
