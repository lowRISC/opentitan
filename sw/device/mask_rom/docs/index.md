---
title: "Reference Mask ROM: Secure Boot Description"
aliases:
- /sw/device/mask_rom/boot
---

<p style="text-align: right">
Contributors(s):
  <a href="https://github.com/lenary">Sam Elliott</a>,
  <a href="https://github.com/gkelly">Garret Kelly</a>,
  <a href="https://github.com/moidx">Miguel Osorio</a>
</p>

<p style="color: red; text-align: right;">
  Status: Draft
</p>

This describes how Mask ROM has chosen to implement the initial parts of the OpenTitan Secure Boot specification.

This should be read in conjunction with the [Secure Boot specification][csm-secure-boot].
References to that document are included.

The Mask ROM is the first boot stage in the Reference Secure Boot implementation, and starts executing at device reset.
The Mask ROM is programmed into the chip's ROM during manufacturing, and cannot be changed.
The Mask ROM needs to prepare the OpenTitan chip for executing a ROM_EXT, including ensuring the loaded ROM_EXT is allowed to be executed on this chip.

# Secure Boot Process

1.  Power on (entirely in hardware)

    **Open Q:** Whether SW has to configure PMP initial region.

2.  Execution Begins with Mask ROM stage:

    *   CRT Startup Code (Written in Assembly)

        *   Disable Interrupts and set well-defined exception handler.
            This should keep initial execution deterministic.

        *   [Clean Device State Part 1](#clean-device-state-p1).
            This includes enabling SRAM Scrambling.

        *   Setup structures for C execution ([CRT](#crt-init): `.data`, `.bss` sections, stack).

        *   Jump into C code

    *   Main Mask ROM Secure Boot Software (Written in C)

        *   Orchestrated from `boot`:

```c
void boot(void) {
  boot_reason = read_boot_reason(); // Boot Policy Module

  // Clean Device State Part 2.
  // See "Cleaning Device State" Below.
  clean_device_state_part_2(boot_reason); // Chip-Specific Startup Module

  // Enable Memory Protection
  // - PMP Initial Region (if not done in power on)
  enable_memory_protection();  // Lockdown Module

  // Chip-specific startup functionality
  // **Open Q:** Proprietary Software Strategy.
  // - Clocks
  // - AST / Entropy.
  // - Flash
  // - Fuses
  chip_specific_startup(); // Chip-Specific Startup Module

  // Manufacturing boot-strapping intervention.
  // **Open Q:** How does the Mask ROM deal with chip recovery?
  // **Open Q:** Pin Strapping Configuration.
  manufacturing_boot_strap(boot_policy, boot_reason); // Bootstrap Module

  // Read Boot Policy for ROM_EXTs from flash (2.b)
  boot_policy = read_boot_policy(boot_reason); // Boot Policy Module

  // Determine which ROM_EXT slot is prioritised (2.b, 2.c.i)
  for ( current_rom_ext_manifest in rom_ext_manifests_to_try(boot_policy) ) { // Boot Policy Module

    // Check ROM_EXT Manifest (2.c.ii)
    // **Open Q:** Integration with Secure Boot Hardware
    // - Header Format (ROM_EXT Manifest Module)
    // - Plausible Key (??)
    // - Initial Digest Checks (Keys + Signature Module)
    // - **Open Q**: ROM_EXT Anti-rollback (??)
    if (!check_rom_ext_manifest(current_rom_ext_manifest)) {
      // Manifest Failure (check Boot Policy)
      if (try_next_on_manifest_failed(boot_policy)) // Boot Policy Module
        continue
      else
        break
    }

    // Find Public Key for ROM_EXT Image Signature (2.c.iii)
    // **Open Q:** Key Selection method/mechanism.
    rom_ext_pub_key = read_pub_key(current_rom_ext_manifest); // ROM_EXT Manifest Module
    rom_ext_pub_key_id = calculate_key_id(rom_ext_pub_key); // Keys + Signature Module
    if (!check_pub_key_id_valid(rom_ext_pub_key_id)) { // Keys + Signature Module
      // Manifest failure (Check Boot Policy)
      if (try_next_on_manifest_failed(boot_policy))  // Boot Policy Module
        continue
      else
        break
    }

    // Verify ROM_EXT Image Signature (2.c.iii)
    // **Open Q:** Integration with Secure Boot Hardware, OTBN
    if (!verify_rom_ext_signature(rom_ext_pub_key,
                                  current_rom_ext_manifest)) { // Hardened Jump Module
      // Manifest Failure (check Boot Policy)
      // **Open Q:** Does this need different logic to the check after
      //   `check_rom_ext_manifest`?
      if (try_next_on_manifest_failed(boot_policy)) // Boot Policy Module
        continue
      else
        break
    }

    // Update Boot Policy on Successful Signature
    // **Open Q:** Does this ensure ROM_EXT Anti-rollback is updated?
    update_next_boot_policy(boot_policy, current_rom_ext_manifest); // Boot Policy Module

    // Beyond this point, you know `current_rom_ext_manifest` is valid and the
    // signature has been authenticated.
    //
    // The Mask ROM now has to do various things to prepare to execute the
    // current ROM_EXT. Most of this is initializing identities, keys, and
    // potentially locking down some hardware, before jumping to ROM_EXT.
    //
    // If any of these steps fail, we've probably left the hardware in an
    // invalid state and should just reboot (because it may not be possible to
    // undo the changes, for instance to write-enable bits).

    // System State Measurements (2.c.iv)
    measurements = perform_system_state_measurements(); // System State Module
    if (!boot_allowed_with_state(measurements)) { // System State Module
      // Lifecycle failure (no policy check)
      break
    }

    // CreatorRootKey (2.c.iv)
    // - This is only allowed to be done if we have verified the signature on
    //   the current ROM_EXT.
    // **Open Q:** Does Mask ROM just lock down key manager inputs, and let the
    //             ROM_EXT load the key?
    derive_and_lock_creator_root_key_inputs(measurements); // System State Module

    // Lock down Peripherals based on descriptors in ROM_EXT manifest.
    // - This does not cover key-related lockdown, which is done in
    //   `derive_and_lock_creator_root_key_inputs`.
    peripheral_lockdown(current_rom_ext_manifest); // Lockdown Module

    // PMP Region for ROM_EXT (2.c.v)
    // **Open Q:** Integration with Secure Boot Hardware
    // **Open Q:** Do we need to prevent access to Mask ROM after final jump?
    pmp_unlock_rom_ext(); // Hardened Jump Module.

    // Transfer Execution to ROM_EXT (2.c.vi)
    // **Open Q:** Integration with Secure Boot Hardware
    // **Open Q:** Accumulated measurements to tie manifest to hardware config.
    if (!final_jump_to_rom_ext(current_rom_ext_manifest)) { // Hardened Jump Module
      // Boot Failure (no policy check)
      // - Because we may have locked some write-enable bits that any following
      //   manifest cannot change if it needs to, we have to just reboot here.
      boot_failed(boot_policy, current_rom_ext_manifest); // Boot Policy Module
    }
  }

  // Boot failed for all ROM_EXTs allowed by boot policy
  boot_failed(boot_policy); // Boot Policy Module
}
```

3.  Execution Enters ROM_EXT stage.

    Not covered by this document. Refer to [Secure Boot][csm-secure-boot] document instead.

# Modules

We've tried to divide the Mask ROM into self-contained modules that can be
tested separately, rather than having to test the whole boot system at once.

The module descriptions below also include descriptions of: the DIFs that are
required for that module to be implemented fully; the functionality expected at
various milestones of the Mask ROM's development; and, optionally, pseudo-code
for any subroutines that make up their implementation.

## Boot Policy

This manages reading the boot policy, updating the boot policy
if required, and making decisions based on that policy. Most Boot Policy
choices also depend on the Boot Reason, so reading and acting on that is
part of this module's responsibility too.

DIFs Needed:

*   Flash Controller
*   Reset Manager

Milestone Expectations:

*   *v0.5:* Reading/Updating Boot Policy
*   *v0.9:* Reading Boot Reason

## Read Boot Policy

```c
read_boot_policy() {
  // Parameters:
  // - initilized flash_ctrl DIF (for accessing flash info page)
  // Returns:
  // - Boot Policy Structure (see below)

  // 1. Uses dif_flash_ctrl to issue read of boot info page.
  // 2. Pull this into a struct to return.
}
```

## ROM_EXT Manifest

This manages reading and parsing ROM_EXT manifests.

The manifest format is defined in [ROM_EXT Manifest Format][rom-ext-manifest]

DIFs Needed:

*   None. This is read out of flash using ibex loads/stores.

Milestone Expectations:

*   *v0.5:* Initial Manifest Format, Initial Parser, Simple Tooling for
    assembling ROM_EXT Slot A images.
*   *v0.7:* Tooling to ensure ROM_EXT is loaded at boot. Tooling for assembling
    Slot B images.
*   v0.9: Nothing more (Bootstrap should work in v0.9).

## Bootstrap

This manages boot-strapping, chip recovery, and manufacturer loading of ROM_EXT
images.

DIFs Needed:

*   GPIO
*   Pinmux
*   Padctrl
*   SPI Device / I2C Device
*   Flash Controller
*   Lifecycle Manager

Milestone Expectations

*   *v0.5:* Nothing (images pre-loaded into Memory)
*   *v0.9:* Full Strapping (ROM_EXT images loaded over SPI)

### Manufacturing boot-strapping intervention

This is where, depending on lifecycle state, new flash images may be loaded onto
the device (usually during manufacturing).

**Open Q:** Do we want hardware hardening for this?
  There are suggestions around having the hardware return `nop` when reading
  this memory if we're not in the correct lifecycle state.

```c
manufacturing_boot_strap() {
  // 1. Read lifecycle state to establish whether bootstrapping is allowed.
  // 2. Determine what kind of bootstrapping is being requested.
  // 3. Clear Flash (Both Banks) and SRAM (Retention)
  //    **Open Q:** How much is cleared? Is the Creator Certificate cleared?
  // 4. Load ROM_EXT image into flash if allowed.
  // 5. Reboot device (causing loaded ROM_EXT to be verified then executed).
}
```

## Signature Verification

This manages public key selection (for ROM_EXT validation), and calculating the
digest and signature of the ROM_EXT image itself.

DIFs Needed:

*   OTBN
*   HMAC
*   Key Manager
*   Lifecycle Manager

Milestone Expectations:

*   *v0.5:* HMAC Digests, Software Implementations of RSA Verify
*   *v0.9:* OTBN Implementations of RSA Verify

## Chip-specific Startup

This deals with how to initialize and clear any chip-specific hardware.

DIFs Needed:

*   Flash
*   OTP / Fuses
*   AST?
*   Entropy?
*   Clocks

## Lockdown

This is responsible for managing memory protection regions as well as
disallowing reconfiguration of peripherals. Some memory protection regions are
also handled by the Hardened Jump module.

DIFs Needed:

*   "PMP" (Not actually a DIF, but something similar will be required)
*   Flash Controller
*   SRAM Scrambling Sequence (Not a DIF, but will need to be shared with DV)
*   Pinmux / Padctrl / Alert Handler

Milestone Expectations:

*   *v0.5:* PMP, Flash Controller
*   *v0.9:* SRAM Scrambling, Lockdown Profiles Defined

### Locking Down Peripherals

```c
peripheral_lockdown() {
  // Parameters:
  // - ROM_EXT manifest
  // - Handles for Peripheral DIFs

  // **Open Q:** When and How do we lock down peripheral configuration?
  // - We configure based on ROM_EXT manifest (signed)
  // - Only locks down these peripherals if info is provided.

  // What do we want to allow lockdown of?
  // - Alert Manager
  // - Pinmux / Padctrl
  // - Entropy Configuration
  // - Anything Else?

  // This is explicitly a separate step from locking the key manager inputs. In
  // particular, this depends on the ROM_EXT's choices, whereas the key manager
  // inputs getting locked is not something the ROM_EXT can choose.
}
```

## Hardened Jump

This module is responsible for managing the state associated with the hardware
support for the jump into ROM_EXT.

DIFs Needed:

*   Secure Boot (which implements Hardened Jump)

Milestone Expectations:

*   *v0.5:* Unhardened Jump (entirely in SW)
*   *v0.9:* HW-support Hardened Jump

## System State

This deals with taking the system state measurements which are used to derive
the `CreatorRootKey`. Some of these measurements may cause boot to be halted.

DIFs Needed:

*   Key Manager
*   Lifecycle Manager
*   Flash Controller
*   OTP
*   **Open Q:** ROM Integrity Measurement?

Milestone Expectations:

*   *v0.5:* Software Binding Properties, OTP Bits.
*   *v0.9:* Full `CreatorRootKey` derivation.

### Cleaning Device State {#clean-device-state-p1}

Part of this process is done before we can execute any C code. In particular, we
have to clear all registers and all of the main RAM before we setup the CRT
(which allows us to execute any C code). This has to be done in assembly, as we
cannot execute C without setting up the CRT.

We want to do as little as possible in the hand-written assembly, because it is
so hard to verify and to test. Additionally, we want to use the DIFs (which are
written in C) because we have verified them, rather than duplicating their
functionality in assembly, if at all possible. So this means we wait until we
are executing C to do the final parts of chip reset, especially parts that may
depend on reading or writing any device state.

Unfortunately, it looks like we will have to enable SRAM scrambling (which
requires entropy and the AST) from assembly.

**Open Q:** Can we zero all of SRAM before enabling scrambling? Should we?
  We certainly cannot zero it all after we have enabled scrambling.

```c
// Will actually be implemented in assembly, as executed too early for C.
clean_device_state_part_1() {

  // - Zero all ISA Registers

  // Depending on boot reason:
  // - Clear Main SRAM
  //   This can either be done by overwriting all of SRAM, or by enabling SRAM
  //   Scrambling. If we do both, we have to be careful about the order (see
  //   above).
  //   **Open Q:** Can we always do the same thing here, regardless of the boot
  //   reason?
}

clean_device_state_part_2() {
  // Parameters:
  // - Boot Reason

  // Depending on boot reason:
  // - Clear Power Manager Scratch Registers
  // - Clear Retention SRAM
  // These clears *must* be done by Mask ROM.

  // - Reset most devices
  //   **Open Q:** Which Devices are we leaving with state for ROM_EXT?
}
```

## CRT (C Runtime)

This sets up execution so we can run C functions. We cannot execute any C code
until we have setup the CRT.

DIFs Needed: None

Milestone Expectations:

*   *v0.5:* Can Execute C functions.
*   *v0.9:* SRAM Scrambling.

### CRT Initialization {#crt-init}

Setting up the CRT involves: loading the `.data` and `.bss` sections, and
setting up the stack and `gp` (`gp` may be used for referencing some data).

```c
// Will actually be written in assembly
crt_init() {
  // - Load `.data` initial image into SRAM.
  // - Zero `.bss` section.
  // - Zero stack.
  // - Load `sp`, `gp`.
  //   **Open Q:** These are used by exception and interrupt handlers if written
  //   in C. Should they be initialized as early as possible? We can turn off
  //   the use of `gp` fairly easily, `sp` is an ABI issue.
}
```

# Interface Data

There is some data that is accessed by more than just the Mask ROM:

*   The Boot Policy structure, used to choose a ROM_EXT to boot.
*   The ROM_EXT manifest, used to contain information about a specific ROM_EXT.
*   The Key Management data, used to validate Root Keys.

In order to keep the Mask ROM simple, a particular Mask ROM version will only
support one version each of the following structures. This means they must be
carefully designed to be extensible if the other systems accessing them may
require additional data in these formats.

## Key Management Data

This is the storage for the IDs of keys that are used to sign a ROM_EXT. The
ROM_EXT image contains the full key, this stores only the key id (which can be
computed from the full key), and uses OTPs to decide whether a key is allowed to
be used to validate a ROM_EXT.

Accessed by:

*   Mask ROM (to identify public key is Valid).
*   ROM_EXT (to prevent use of public key).

Needs to contain:

*   Read-only list of public key ids.
*   OTP fuses to say whether a key id is revoked or not (keys start not revoked).

Stored In: OTP and ROM

Extensibility: None. A ROM_EXT can disable the use of a key, but cannot add new
valid root key IDs. There will be a fixed set of root key IDs as part of a given
Mask ROM version.

## Boot Policy Structure

This is the in-flash structure that defines which ROM_EXT should be booted next,
whether it should fall back to the other ROM_EXT if it fails to boot, and/or
whether it should be marked as the primary ROM_EXT if it succeeds to validate.

This structure merely controls which ROM_EXT is validated and executed -- it
does not contain any executable code. This means it does not need to be
protected as securely as the ROM_EXT images, which contain code and are signed
and validated before execution.

Accessed by:

*   Mask ROM (to choose ROM_EXT, and during bootstrapping to bless new ROM_EXT).
*   ROM_EXT (during firmware update).

Needs to contain:

*   Identifier (so we know we're reading the right thing)

    This also acts like a version number, because the Mask ROM code that parses
    the boot policy can never be updated. Conversely, any changes to this
    structure require new Mask ROM parsing code, which should be denoted with a
    new identifier.

*   Which ROM_EXT slot should be chosen first (2.b, 2.c.i).
*   What to do if ROM_EXT does not validate (2.c.ii, 2.c.iii):
    *   Try Alternate ROM_EXT; or
    *   Fail to Boot
*   What to do if ROM_EXT validates successfully, just before jumping to ROM_EXT:
    *   Do nothing; or
    *   Set current ROM_EXT as Primary if not already.
*   Checksum (of everything else).

Stored in: Flash (Info Partition)

Extensibility: None. This info only controls the actions of the Mask ROM. You
cannot add functionality to the Mask ROM of a given chip, so there's no way to
add other information to this structure.

The in-RAM representation also contains the boot reason (reset manager), because
it needs to be checked most times the boot policy is also read.

## ROM_EXT Manifest Structure

Accessed by:

*   Mask ROM (to validate ROM_EXT).
*   ROM_EXT (potentially).
*   BL0 Kernel (during firmware update).

The manifest format is defined in [ROM_EXT Manifest Format][rom-ext-manifest].

Stored in: Flash (at one of two fixed, memory-mapped, addresses)

Extensibility:

*   Mask ROM: None
*   ROM_EXT/BL0:
    *   Uses the Extension fields for additional read-only data if required.
        This is not interpreted by the Mask ROM, but may be used by ROM_EXT or
        BL0 if required.


<!-- Links -->
[csm-secure-boot]: {{< relref "doc/security/specs/secure_boot" >}}
[rom-ext-manifest]: {{< relref "sw/device/rom_exts/docs/manifest" >}}
