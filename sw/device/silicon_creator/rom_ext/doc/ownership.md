# OpenTitan Ownership Transfer

> [!NOTE]
> This document is a draft.

## Introduction

This document discusses the OpenTitan Ownership Transfer protocol, including the commands, operations, data and data structures needed for ownership transfer.
Ownership Transfer allows the owner of the chip to securely root an OpenTitan chip to their own public key infrastructure and to transfer the chip to a new owner when they no longer want or need to be the owner of the chip (e.g. reselling used equipment or transferring equipment among different security domains within the same organization).

### Definitions

- Owner Configuration: a data structure encoding the ownership information for a given owner.
  The owner configuration includes an owner key, one or more application keys and various owner configuration data.
- Owner Key: an ECDSA P-256 public/private key-pair used to authenticate the ownership block.
- Activate Key: an ECDSA P-256 public/private key-pair used to authenticate an Activate Owner command.
  This key is endorsed by the Owner key by virtue of being present in the owner configuration.
- Unlock Key: an ECDSA P-256 public/private key-pair used to authenticate an Unlock Owner command.
  This key is endorsed by the Owner key by virtue of being present in the owner configuration.
- Ownership State: The state of a chip with respect to ownership transfer.
  A chip may be in one of the following states: `LockedOwner`, `UnlockedSelf`, `UnlockedAny`, `UnlockedEndorsed`, `LockedNone`.
- Ownership Nonce: A 64-bit random integer used as a validation challenge for all ownership-related boot services requests.
- Owner Page 0 & 1: The Owner Configuration is stored by the chip in a pair of flash INFO pages.
  Normally the two pages are identical and serve as redundant backups.
  During an update or transfer, page 0 is the current configuration and page 1 is the next configuration.
- Application Key: an ECDSA public/private key-pair used to authenticate the owner’s application firmware payload.
- Tag/Length/Value (TLV): A structure encoding scheme for encoding heterogenious and variable-length data structures.

## Ownership Transfer

Ownership Transfer allows owners of OpenTitan chips to securely transfer chips and OpenTitan devices between different public key infrastructures (PKIs) without assistance (or interference) from the manufacturer of the chip.

Ownership Transfer gives each owner of a chip the ability to specify their own application firmware keys, key domains and chip configurations.

### Ownership State

The ownership state is a non-volatile chip state that controls the ownership transfer mechanism.
A chip may be in one of the following states:
- `LockedOwner`: The chip is currently owned and will not accept new owner configurations.
- `UnlockedSelf`: The chip is currently owned and is expecting an ownership block update for the same owner (ie: config change or key rotation).
- `UnlockedAny`: The chip is currently owned but will accept an ownership block for any new owner.
- `UnlockedEndorsed`: The chip is currently owned but will accept an ownership block only from a new owner endorsed by the current owner.
- `LockedNone` The chip doesn’t have an owner and is unable to accept a new owner.
  This is a nearly-fatal error state and requires intervention by *silicon\_creator* to recover the chip.

When the chip is in one of the `Unlocked` states, the ROM\_EXT will unlock Owner Page 1 allowing firmware to write a new owner configuration into that location.

The ownership state is stored in the `boot_data` record.

### Ownership Nonce

The ownership nonce is a random 64-bit integer value used as a challenge for ownership transfer operations
All ownership-related boot services commands include the nonce and a signature by either the current owner or the next owner.

Each successful ownership-related boot services request (ie: `OwnershipUnlock` and `OwnershipActivate`) will cause a new nonce to be generated
Any subsequent ownership-related request must use the new nonce value.

The ownership nonce is stored in the `boot_data` record.

### Next Owner Key

The next owner key is the public ECDSA key of the next owner when performing an endorsed ownership transfer operation.

The next owner’s public key fingerprint (ie: sha256 of the public key material) is stored in the `boot_data` record.

### Activate Key

The Activate key is used to authenticate the Activate Owner boot services command
This key is separate from the Next Owner Key to allow owners to have different security policies for the Owner and Activate keys
For example, this permits the Owner private key to be stored in an offline system and the Activate key to be stored in an online system.

The Activate Owner key is endorsed by the Owner key via the Ownership Block data structure.

### Unlock Key

The Unlock key is used to authenticate the Unlock Ownership boot services command
This key is separate from the Next Owner Key to allow owners to have different security policies for the Owner and Unlock keys.

The Unlock key is endorsed by the Owner key via the Ownership Block data structure.

### Operations

The following flows support ownership transfer operations
Each of the flows assumes the owner currently has `primary_bl0` set to SideA (the flows will also work with the `primary_bl0` set to SideB, but any reference to SideB in the flows would need to be changed to SideA).

#### Locked Update of Owner Configuration

A locked update allows an owner to update their Owner Configuration without transferring ownership to a new owner.

1. The owner prepares for the update by staging a signed boot services `OwnershipUnlock` command with the current ownership nonce and the mode set to `UnlockedSelf`.
   - After staging the command, the chip is rebooted.
   - Upon booting, the ROM\_EXT will move the chip into the `UnlockedSelf` state and will unlock Owner Page 1 to accept an Owner Configuration update.
2. The owner updates the Owner Configuration in Owner Page 1 to the new preferred settings (e.g. key rotation or configuration change).  The owner configuration must be signed with the owner key.
   - After updating the page, the chip is rebooted.
   - Upon booting, the ROM\_EXT will inspect the new configuration block.  If and only if the new owner configuration is valid, the ROM\_EXT will configure the non-primary half of the flash (i.e. Side B) as requested in the new owner configuration.
3. The owner will stage a firmware update on the non-primary half of the flash. This firmware must be signed with a valid owner application key.  The owner will stage a Boot Services `next_boot_bl0` message requesting a boot to the non-primary partition (i.e. Side B).
   - After staging the firmware and boot services request, the chip will be rebooted.
   - Upon booting, the ROM\_EXT will configure the non-primary half of the flash (i.e. Side B) as requested in the new owner configuration and then attempt to find and validate a firmware payload located in the non-primary half of the flash.
      - If there is a valid firmware in the non-primary half, it will be booted.
      - If there is no valid firmware in the non-primary half, the primary half will be booted according to the settings of the current (non-updated) Owner Configuration.
4. If the boot -
   - Succeeds:
      - The owner will stage a signed boot services `activate_owner` command with the current ownership nonce to finalize the update.  The activate owner command must be signed with the Activate key.
      - After staging the command the chip is rebooted.
      - Upon booting, the ROM\_EXT will move the chip into the `LockedOwner` state and update Owner Page 0 with the new Owner Configuration located in page 1.
   - Fails:
      - The owner can retry the update from step 2.

```mermaid
flowchart LR
subgraph container["<font size=6>Flow: Locked Configuration Update</font>"]
    subgraph flow[" "]
        direction TB
        start((<b>Start</b>))
        prepare[
            <b>Prepare</b>
            Send <code>OwnershipUnlock</code> with <code>mode=UnlockedSelf</code>.
            Reboot.
        ]
        update[<b>Update Owner Config</b>
            Store new Owner Config in Owner Page 1.
            Reboot.
        ]
        flash[<b>Flash</b>
            Flash new firmware to side B.
            Send <code>NextBootBl0</code> with <code>side=SideB</code>.
            Reboot.
        ]
        success{Success?}
        activate[<b>Activate</b>
            Send <code>OwnershipActivate</code> with <code>primary_bl0=SideB</code>.
            Reboot.
        ]
        done((<b>Done</b>))
        start --> prepare
        prepare --> update
        update --> flash
        flash --> success
        success -->|Yes| activate
        success -->|No| update
        activate --> done((<b>Done</b>))
    end

    signing[
        <span style="color:black"><b>Signing Service</b>
        Owner
        </span>
    ]

    prepare <-- "Sign command with Unlock Key" --> signing
    update <-- "Sign Owner Config with Owner Key" --> signing
    flash <-- "Sign firmware with Application Key" --> signing
    activate <-- "Sign command with Activate Key" --> signing

    style flow fill:none,stroke:none
    style signing fill:#aea,stroke:#6c6
    style container fill:none,stroke:black
end
```

#### Unlocked Ownership Transfer

An unlocked ownership transfer allows the current owner to unlock the chip so that it will accept any new owner.

1. The current owner prepares for the transfer by staging a signed boot services `OwnershipUnlock` command with the current ownership nonce and the mode set to `UnlockedAny`.
   After staging the command, the chip is rebooted.
   - Upon booting, the ROM\_EXT will move the chip into the `UnlockedAny` state and will unlock Owner Page 1 to accept an Owner Configuration update.
2. The current owner will deliver the chip (device) to the next owner.
3. The next owner updates the Owner Configuration in Owner Page 1 giving the chip the next owner’s public key material and preferred configuration settings.
   - After updating the page, the chip is rebooted.
   - Upon booting, the ROM\_EXT will inspect the next owner configuration.
     If and only if the next Owner Configuration is valid, the ROM\_EXT will configure the non-primary half of the flash (i.e. Side B) as requested in the new owner configuration.
4. The next owner will stage a firmware update on the non-primary half of the flash.
   This firmware must be signed with a valid (next) owner application key.
   The owner will stage a Boot Services `next_boot_bl0` message requesting a boot to the non-primary partition (i.e. Side B).
   - After staging the firmware and boot services request, the chip will be rebooted.
   - Upon booting, the ROM\_EXT will configure the non-primary half of the flash (i.e. Side B) as requested in the next owner configuration and then attempt to find and validate a firmware payload located in the non-primary half of the flash.
      - If there is a valid firmware in the non-primary half, it will be booted.
      - If there is no valid firmware in the non-primary half, the primary half will be booted according to the settings of the previous Owner Configuration.
5. If the boot -
   - Succeeds:
      - The next owner will stage a signed boot services `OwnershipActivate` command with the current ownership nonce to finalize the update.
The activate owner command must be signed with the Activate key.
      - After staging the command the chip is rebooted.
      - Upon booting, the ROM\_EXT will move the chip into the `LockedOwner` state and update Owner Page 0 with the new Owner Configuration located in page 1.
   - Fails:
      - The next owner can retry the update from step 3.

```mermaid
flowchart LR
subgraph container["<font size=6>Flow: Unlocked Ownership Transfer</font>"]
    subgraph flow[" "]
        direction TB
        start((<b>Start</b>))
        prepare[
            <b>Prepare</b>
            Send <code>OwnershipUnlock</code> with <code>mode=UnlockedAny</code>.
            Reboot.
        ]
        deliver((Deliver to next owner.))
        update[<b>New Owner Config</b>
            Store new Owner Config in Owner Page 1.
            Reboot.
        ]
        flash[<b>Flash</b>
            Flash new firmware to side B.
            Send <code>NextBootBl0</code> with <code>side=SideB</code>.
            Reboot.
        ]
        success{Success?}
        activate[<b>Activate</b>
            Send <code>OwnershipActivate</code> with <code>primary_bl0=SideB</code>.
            Reboot.
        ]
        done((<b>Done</b>))
        start --> prepare
        prepare --> deliver
        deliver --> update
        update --> flash
        flash --> success
        success -->|Yes| activate
        success -->|No| update
        activate --> done((<b>Done</b>))
    end

    curr_owner[
        <span style="color:black"><b>Signing Service</b>
        Current Owner
        </span>
    ]
    next_owner[
        <span style="color:black"><b>Signing Service</b>
        Next Owner
        </span>
    ]

    prepare <-- "Sign command with Unlock Key" --> curr_owner
    update <-- "Sign Owner Config with Owner Key" --> next_owner
    flash <-- "Sign firmware with Application Key" --> next_owner
    activate <-- "Sign command with Activate Key" --> next_owner
    style flow fill:none,stroke:none
    style curr_owner fill:#aea,stroke:#6c6
    style next_owner fill:#aee,stroke:#6cc
    style container fill:none,stroke:black
end
```

#### Endorsed Ownership Transfer

An endorsed ownership transfer allows the current owner to transfer ownership to a specific new owner.

1. The current owner prepares for the transfer by staging a signed boot services `OwnershipUnlock` command with the current ownership nonce, the next owner’s public key and the mode set to `UnlockedEndorsed`.  After staging the command, the chip is rebooted.
   - Upon booting, the ROM\_EXT will move the chip into the `UnlockedEndorsed` state and will unlock Owner Page 1 to accept an Owner Configuration update.
2. The current owner will deliver the chip (device) to the next owner.
3. The next owner updates the Owner Configuration in Owner Page 1 giving the chip the next owner’s public key material and preferred configuration settings.
   - After updating the page, the chip is rebooted.
   - Upon booting, the ROM\_EXT will inspect the next owner configuration.  If and only if the next Owner Configuration is valid, the ROM\_EXT will configure the non-primary half of the flash (i.e. Side B) as requested in the new owner configuration.
4. The next owner will stage a firmware update on the non-primary half of the flash.  This firmware must be signed with a valid (next) owner application key.  The owner will stage a Boot Services `next_boot_bl0` message requesting a boot to the non-primary partition (i.e. Side B).
   - After staging the firmware and boot services request, the chip will be rebooted.
   - Upon booting, the ROM\_EXT will configure the non-primary half of the flash (i.e. Side B) as requested in the next owner configuration and then attempt to find and validate a firmware payload located in the non-primary half of the flash.
      - If there is a valid firmware in the non-primary half, it will be booted.
      - If there is no valid firmware in the non-primary half, the primary half will be booted according to the settings of the previous Owner Configuration.
5. If the boot -
   - Succeeds:
      - The next owner will stage a signed boot services `OwnershipActivate` command with the current ownership nonce to finalize the update.  The activate owner command must be signed with the Activate key.
      - After staging the command the chip is rebooted.
      - Upon booting, the ROM\_EXT will move the chip into the `LockedOwner` state and update Owner Page 0 with the new Owner Configuration located in page 1.
   - Fails:
      - The next owner can retry the update from step 3.

```mermaid
flowchart LR
subgraph container["<font size=6>Flow: Endorsed Ownership Transfer</font>"]
    subgraph flow[" "]
        direction TB
        start((<b>Start</b>))
        prepare[
            <b>Prepare</b>
            Send <code>OwnershipUnlock</code> with <code>mode=UnlockedEndorsed</code>
            and next owner's public key.
            Reboot.
        ]
        deliver((Deliver to next owner.))
        update[<b>New Owner Config</b>
            Store new Owner Config in Owner Page 1.
            Reboot.
        ]
        flash[<b>Flash</b>
            Flash new firmware to side B.
            Send <code>NextBootBl0</code> with <code>side=SideB</code>.
            Reboot.
        ]
        success{Success?}
        activate[<b>Activate</b>
            Send <code>OwnershipActivate</code> with <code>primary_bl0=SideB</code>.
            Reboot.
        ]
        done((<b>Done</b>))
        start --> prepare
        prepare --> deliver
        deliver --> update
        update --> flash
        flash --> success
        success -->|Yes| activate
        success -->|No| update
        activate --> done((<b>Done</b>))
    end

    curr_owner[
        <span style="color:black"><b>Signing Service</b>
        Current Owner
        </span>
    ]
    next_owner[
        <span style="color:black"><b>Signing Service</b>
        Next Owner
        </span>
    ]

    prepare <-- "Sign command with Unlock Key" --> curr_owner
    prepare <-- "Next Owner's public key" --> next_owner
    update <-- "Sign Owner Config with Owner Key" --> next_owner
    flash <-- "Sign firmware with Application Key" --> next_owner
    activate <-- "Sign command with Activate Key" --> next_owner
    style flow fill:none,stroke:none
    style curr_owner fill:#aea,stroke:#6c6
    style next_owner fill:#aee,stroke:#6cc
    style container fill:none,stroke:black
end
```

### Boot Services Commands

All ownership operations are facilitated by boot services commands to the ROM\_EXT.
The following boot services commands are supported.

#### Ownership Unlock

The ownership unlock command prepares the chip for an ownership transfer or a non-transferring owner configuration update.
The ownership unlock command must include the current ROM\_EXT nonce and a signature with the current owner's unlock key.

```c
struct boot_svc_ownership_unlock_request {
    boot_svc_header_t header;
    uint32_t unlock_mode;           // One of UnlockedAny, UnlockedEndorsed, UnlockedSelf or Abort.
    uint32_t reserved[18];          // Reserved for future use.
    uint64_t nonce;                 // The current ownership nonce.
    uint32_t next_owner_key[16];    // The public key of the next owner (for endorsed mode).
    uint32_t signature[16];         // Signature over [unlock_mode..next_owner_key].
};
```
See the definition in [boot_svc_ownership_unlock.h](../../lib/boot_svc/boot_svc_ownership_unlock.h).

A valid ownership unlock command will prepare the chip for an ownership transfer.

When the mode is `UnlockedAny`, `UnlockedEndorsed` or `UnlockedSelf`, the ROM\_EXT will:
- Rotate the ROM\_EXT nonce value.
- Update the ownership state.
- If endorsed mode, save the next owner key into `boot_data`.

When the mode is `Abort`, the ROM\_EXT will:
- Rotate the ROM\_EXT nonce value.
- Update the ownership state to `LockedOwner`.
- Copy the owner configuration from owner page 0 to owner page 1.

#### Ownership Activate

The ownership activate command completes an ownership transfer or update and moves the chip into the `LockedOwner` state.
The ownership activate command must include the current ROM\_EXT nonce and a signature with the next owner's activate key (or the current owner's activate key in the case of a non-transferring update).

```c
struct boot_svc_ownership_activate_request {
    boot_svc_header_t header;
    uint32_t primary_bl0_slot;      // Which flash slot contains the new owner's firmware.
    uint32_t erase_previous;        // Erase the previous owner's flash (hardened_bool_t).
    uint32_t reserved[33];          // Reserved for future use.
    uint64_t nonce;                 // The current ownership nonce.
    uint32_t signature[16];         // Signature over [primary_bl0_slot..nonce].
};
```
See the definition in [boot_svc_ownership_activate.h](../../lib/boot_svc/boot_svc_ownership_activate.h).

A valid ownership activate request will:
- Rotate the ROM\_EXT nonce value.
- Update the ownership state to `LockedOwner`.
- Set the primary BL0 slot.
- Erase the previous owner's flash slot (ie: the non-primary slot).
- Copy the owner configuration from owner page 1 into owner page 0.

## Owner Configuration

### Contents

The owner configuration contains the following items:
- Owner Key:  This key is the owner's identity and is used to endorse the keys used for application verification and future owner configuration updates or transfer request.
- Activation Key:  This key is used to authenticate an `OwnershipActivate` command.
- Unlock Key:  This key is used to authenticate an `OwnershipUnlock` command.
- Owner Application Keys:  These keys are used to authenticate the owner's firmware payload.
   The keys also carry some additional metadata used to configure the OpenTitan key manager.
- EFLASH configuration.
  The EFLASH configuration sets the desired properties on ranges of flash data pages (such as access permissions and error correction properties).
- EFLASH-INFO configuration: The EFLASH-INFO configuration sets the desired properties on flash info pages.
  Some info pages are reserved for use by the `silicon_creator` and have restricted access.
  The remaining info pages are available to the owner and the owner can set specific access permissions.
- Miscellaneous settings:
   - SRAM execution: depending on the application, the owner may want to allow or forbid code execution from SRAM.
   - Rescue configuration: The ROM\_EXT supports a rescue protocol for recovering from an internal flash corruption event and querying data about the chip.
     The rescue configuration allows the owner to control interactions with the rescue protocol.

Because the Owner Configuration is composed of several sections of varying size and count (e.g. perhaps several different keys), the owner configuration utilizes tag-length-value (TLV) encoded structures.

```c
struct TLVHeader {
    uint32_t tag;
    uint32_t length;
};
```
See the definition in [datatypes.h](../../lib/ownership/datatypes.h).

### Structures

#### Owner Configuration

The Owner Configuration struct carries the required owner key materials and validation information and is a container for all of the TLV structs specifying the configuration.
- The `owner_key` Key is an ECDSA P-256 key used to authenticate the owner configuration and endorse the other keys.
- The `signature` is an ECDSA signature over the struct, excluding the `signature` and `seal` members (ie: the first 1952 bytes).
- The `seal` is a KMAC over the owner configuration binding the configuration to a particular chip.
   - During secure boot, the `seal` is used to confirm the validity of the owner configuration.
   - During ownership transfer, the `seal` is computed by the chip.

```c
struct OwnerConfig {
    uint32_t tag;                   // Tag: `OWNR`.
    uint32_t length;                // 2048 bytes.
    uint32_t version;               // The version of the struct (currently version 0).
    uint32_t sram_exec_mode;        // SRAM execution configuration (`DisabledLocked`, `Disabled` or `Enabled`).
    uint32_t ownership_key_alg;     // Ownership key algorithm (ECDSA, SPX or SPXq20).
    uint32_t reserved[3];           // Reserved for future use.
    owner_key_t owner_key;          // Owner's public key.
    owner_key_t activate_key;       // Owner's activate key.
    owner_key_t unlock_key;         // Owner's unlock key.
    uint8_t data[1728];             // Data region to hold additional TLV configuration structs.
    owner_signature_t signature;    // Signature over [tag..data] with owner's private key.
    uint32_t seal[8];               // A KMAC over the configuration to bind the struct to a chap.
};
```
See the definition in [datatypes.h](../../lib/ownership/datatypes.h).

#### Application Keys

The Application Keys verify owner firmware payloads during the secure boot process.
- The `key_algorithm` refers to the key algorithm to be used with this key (ECDSA, SPX or SPXq20).
- The `key_domain` refers to the application-level key domain: `prod`, `dev` or `test`.
  These values have no relationship with the chip's lifecycle state.
  This value is used to diversify the key manager's key derivations.
- The `key_diversifier` is an arbitrary owner-selected value to further diversify key derivation.
  This allows the owner to create additional key domains within each of the `prod`, `dev` or `test` categories.
  The 8 words of `key_domain || key_diversifier` are programmed into the key manager sealing binding registers.
- The `usage_constraint` is a bitmask that is combined (bitwise OR-ed) with the firmware manifest's `usage_constraint.selector` bits.
  This can be used to create application keys that required class- or node-locked firmware.
- The `data` field contains the key material itself.

```c
struct OwnerApplicationKey {
    tlv_header_t header;            // Tag: `APPK`.  Length: 48 + sizeof(key).
    uint32_t key_algorithm;         // Key algorithm (ECDSA, SPX or SPXq20).
    uint32_t key_domain;            // Key domain (prod, dev or test).
    uint32_t key_diversifier[7];    // Key diversifier.
    uint32_t usage_constraint;      // Usage constraint must match manifest header's constraint.
    uint32_t data[];                // Key material.
};

```
See the definition in [datatypes.h](../../lib/ownership/datatypes.h).

#### EFLASH Configuration

The EFLASH configuration describes the owner's desired flash configuration.
- The flash region `start` and `size` are expressed in pages.
- No flash region should span over the A and B halves of the flash.
  This is to allow configuring the A and B havles differently during an ownership transfer operation.

```c
enum Properties {
  Read =               0x00000001,  // Allow read access to the region.
  Program =            0x00000002,  // Allow program access to the region.
  Erase =              0x00000004,  // Allow erase access to the region.
  Scramble =           0x00000008,  // Turn on data scrambling in the region.
  Ecc =                0x00000010,  // Turn on ECC error correction in the region.
  HighEndurance =      0x00000020,  // Turn on High Endurance mode for the region.
  ProtectWhenPrimary = 0x40000000,  // Protect region when on the primary side (ie: disable program and erase).
  Lock =               0x80000000,  // Lock the region configuration register for this region.
};

struct FlashRegion {
    uint16_t start;                 // Flash region starting page number.
    uint16_t size;                  // Size of the region in pages.
    uint32_t properties;            // Bitmap describing the requested properties.
};

struct OwnerFlashConfig {
    tlv_header_t header;            // Tag: `FLSH`.  Length: 8 + 8 * count(config).
    struct FlashRegion config[];    // Variable length.
};
```
See the definition in [datatypes.h](../../lib/ownership/datatypes.h).


#### FLASH_INFO Configuration

The FLASH-INFO configuration describes the owner's desired configuration for flash info pages.

Info page configurations apply only to pages accessible to the owner.
Upon ingestion of a new owner configuration, the ROM\_EXT will reject a configuration that attempts to use info pages reserved for `silicon_creator`.

```c
struct InfoPage {
    uint8_t bank;                   // Flash bank.
    uint8_t page;                   // Page number
    uint8_t _padding[2];
    uint32_t properties;            // Bitmap describing the requested properties.
};

struct OwnerFlashInfoConfig {
    tlv_header_t header;            // Tag: `INFO`.  Length: 8 + 8 * count(config).
    struct FlashInfo config[];      // Variable length.
};
```
See the definition in [datatypes.h](../../lib/ownership/datatypes.h).

#### Rescue Configuration

The rescue configuration describes the owner's desired configuration of the ROM\_EXT rescue protocol.
- The owner may configure the region of flash to be erased and reprogrammed during firmware rescue.
- The owner may configure the allowed interactions with the rescue protocol.
   - Allowed rescue modes permit whether the rescue client can upload firmware or interact with the boot log and boot services.
   - Allowed boot services commands determine whether or not a boot services request from the rescue protocol will be accepted or rejected.

```c
struct OwnerRescueConfig {
    tlv_header_t header;            // Tag: `RSCU`.  Length: 16 + sizeof(command_allow).
    uint32_t rescue_type;           // Currently, only Xmodem is supported.
    uint16_t region_start;                        // Start page of the rescue region in flash.
    uint16_t region_size;           // Size of of the rescue region in pages.
    uint32_t command_allow[];       // List of FourCC tags of allowed rescue modes and boot services commands.
}
```
