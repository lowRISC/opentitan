# ROM

<p style="color: red; text-align: right;">
  Status: Draft
</p>

This describes how ROM has chosen to implement the initial parts of the OpenTitan Secure Boot specification.

This should be read in conjunction with the [Secure Boot specification][csm-secure-boot].
References to that document are included.

The ROM is the first boot stage in the Reference Secure Boot implementation, and starts executing at device reset.
The ROM is programmed into the chip's ROM during manufacturing, and cannot be changed.
The ROM needs to prepare the OpenTitan chip for executing a ROM_EXT, including ensuring the loaded ROM_EXT is allowed to be executed on this chip.

# Secure Boot Process

1.  Power on (entirely in hardware)

    **Open Q:** Whether SW has to configure PMP initial region.

2.  Execution Begins with ROM stage:

    *   CRT Startup Code (Written in Assembly)

        *   Disable Interrupts and set well-defined exception handler.
            This should keep initial execution deterministic.

        *   [Clean Device State Part 1](#cleaning-device-state).
            This includes enabling SRAM Scrambling.

        *   Setup structures for C execution ([CRT](#crt-initialization): `.data`, `.bss` sections, stack).

        *   Jump into C code

    *   Main ROM Secure Boot Software (Written in C)

3.  Execution Enters ROM_EXT stage.

    Not covered by this document. Refer to [Secure Boot][csm-secure-boot] document instead.

# Modules

We've tried to divide the ROM into self-contained modules that can be
tested separately, rather than having to test the whole boot system at once.

The module descriptions below also include descriptions of: the dependencies
that are required for that module to be implemented fully; the functionality
expected at various stages of the ROM's development; and, optionally,
pseudo-code for any subroutines that make up their implementation.

## Boot Policy

This manages reading the boot policy, updating the boot policy
if required, and making decisions based on that policy. Most Boot Policy
choices also depend on the Boot Reason, so reading and acting on that is
part of this module's responsibility too.

Dependencies:

*   Flash Controller
*   Reset Manager

## ROM_EXT Manifest

This manages reading and parsing ROM_EXT manifests.

The manifest format is defined in [ROM_EXT Manifest Format][rom-ext-manifest]

Dependencies:

*   None. This is read out of flash using ibex loads/stores.

## Bootstrap

This manages boot-strapping, chip recovery, and manufacturer loading of ROM_EXT
images.

Dependencies:

*   GPIO
*   Pinmux
*   Padctrl
*   SPI Device / I2C Device
*   Flash Controller
*   Lifecycle Manager

### Manufacturing boot-strapping intervention

This is where, depending on lifecycle state, new flash images may be loaded onto
the device (usually during manufacturing).

## Signature Verification

This manages public key selection (for ROM_EXT validation), and calculating the
digest and signature of the ROM_EXT image itself.

Dependencies:

*   OTBN
*   HMAC
*   Key Manager
*   Lifecycle Manager

## Chip-specific Startup

This deals with how to initialize and clear any chip-specific hardware.

Dependencies:

*   Flash
*   OTP / Fuses
*   AST?
*   Entropy?
*   Clocks

## Memory Protection

This is responsible for managing the read (R), write (W) and execute (X)
permissions for memory regions.

Dependencies:

*   [Enhanced Physical Memory Protection (ePMP)](https://ibex-core.readthedocs.io/en/latest/03_reference/pmp.html)

## System State

This deals with taking the system state measurements which are used to derive
the `CreatorRootKey`. Some of these measurements may cause boot to be halted.

Dependencies:

*   Key Manager
*   Lifecycle Manager
*   Flash Controller
*   OTP
*   ROM Integrity Measurement

### Cleaning Device State

Part of this process is done before we can execute any C code. In particular, we
have to clear all registers and all of the main RAM before we setup the CRT
(which allows us to execute any C code). This has to be done in assembly, as we
cannot execute C without setting up the CRT.

We want to do as little as possible in the hand-written assembly, because it is
so hard to verify and to test. Additionally, we want to use drivers written in
C because we have verified them, rather than duplicating their functionality
in assembly, if at all possible. So this means we wait until we are executing
C to do the final parts of chip reset, especially parts that may depend on
reading or writing any device state.

Unfortunately, it looks like we will have to enable SRAM scrambling (which
requires entropy and the AST) from assembly.

## CRT (C Runtime)

This sets up execution so we can run C functions. We cannot execute any C code
until we have setup the CRT.

Dependencies: None

### CRT Initialization

Setting up the CRT involves: loading the `.data` and `.bss` sections, and
setting up the stack and `gp` (`gp` may be used for referencing some data).


# Interface Data

There is some data that is accessed by more than just the ROM:

*   The Boot Policy structure, used to choose a ROM_EXT to boot.
*   The ROM_EXT manifest, used to contain information about a specific ROM_EXT.
*   The Key Management data, used to validate Root Keys.

In order to keep the ROM simple, a particular ROM version will only
support one version each of the following structures. This means they must be
carefully designed to be extensible if the other systems accessing them may
require additional data in these formats.

## Key Management Data

This is the storage for the IDs of keys that are used to sign a ROM_EXT. The
ROM_EXT image contains the full key, this stores only the key id (which can be
computed from the full key), and uses OTPs to decide whether a key is allowed to
be used to validate a ROM_EXT.

Accessed by:

*   ROM (to identify public key is Valid).
*   ROM_EXT (to prevent use of public key).

Needs to contain:

*   Read-only list of public key ids.
*   OTP fuses to say whether a key id is revoked or not (keys start not revoked).

Stored In: OTP and ROM

Extensibility: None. A ROM_EXT can disable the use of a key, but cannot add new
valid root key IDs. There will be a fixed set of root key IDs as part of a given
ROM version.

## Boot Policy Structure

This is the in-flash structure that defines which ROM_EXT should be booted next,
whether it should fall back to the other ROM_EXT if it fails to boot, and/or
whether it should be marked as the primary ROM_EXT if it succeeds to validate.

This structure merely controls which ROM_EXT is validated and executed -- it
does not contain any executable code. This means it does not need to be
protected as securely as the ROM_EXT images, which contain code and are signed
and validated before execution.

Accessed by:

*   ROM (to choose ROM_EXT, and during bootstrapping to bless new ROM_EXT).
*   ROM_EXT (during firmware update).

Needs to contain:

*   Identifier (so we know we're reading the right thing)

    This also acts like a version number, because the ROM code that parses
    the boot policy can never be updated. Conversely, any changes to this
    structure require new ROM parsing code, which should be denoted with a
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

Extensibility: None. This info only controls the actions of the ROM. You
cannot add functionality to the ROM of a given chip, so there's no way to
add other information to this structure.

The in-RAM representation also contains the boot reason (reset manager), because
it needs to be checked most times the boot policy is also read.

## ROM_EXT Manifest Structure

Accessed by:

*   ROM (to validate ROM_EXT).
*   ROM_EXT (potentially).
*   BL0 Kernel (during firmware update).

The manifest format is defined in [ROM_EXT Manifest Format][rom-ext-manifest].

Stored in: Flash (at one of two fixed, memory-mapped, addresses)

Extensibility:

*   ROM: None
*   ROM_EXT/BL0:
    *   Uses the Extension fields for additional read-only data if required.
        This is not interpreted by the ROM, but may be used by ROM_EXT or
        BL0 if required.


<!-- Links -->
[csm-secure-boot]: ../../../../doc/security/specs/secure_boot/README.md
[rom-ext-manifest]: ../rom_ext/doc/manifest.md
