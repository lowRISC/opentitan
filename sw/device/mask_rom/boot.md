# Pseudo-code for Mask ROM Secure Boot Process

This file should be read in conjunction with secure boot specification.
References to that document are included.

Sub-procedures are documented below the main `boot` function.

1. Power on (entirely in hardware)

   **Open Q:** Whether SW has to configure PMP initial region.

2. Execution Begins with Mask ROM stage:
   *   CRT Startup Code (Written in Assembly)

       *   Disable Interrupts and set well-defined exception handler.
           This should keep initial execution deterministic.

       *   Clean Device State Part 1. (See "Cleaning Device State" below)
           This includes enabling SRAM Scrambling.

       *   Setup structures for C execution (CRT: `.data`, `.bss` sections, stack).

       *   Jump into C code

   *   Main Mask ROM Secure Boot Software (Written in C)
       *   Orchestrated from `boot`:

```c
void boot(void) {
  boot_reason = read_boot_reason();

  // Clean Device State Part 2.
  // See "Cleaning Device State" Below.
  clean_device_state_part_2(boot_reason);

  // Enable Memory Protection
  // - PMP Initial Region (if not done in power on)
  enable_memory_protection();

  // Chip-specific startup functionality
  // **Open Q:** Proprietary Software Strategy.
  // - Clocks
  // - AST / Entropy.
  // - Flash
  // - Fuses
  chip_specific_startup();

  // Manufacturing boot-strapping intervention.
  // **Open Q:** How does the Mask ROM deal with chip recovery?
  // **Open Q:** Pin Strapping Configuration.
  manufacturing_boot_strap();

  // Read Boot Policy for ROM_EXTs from flash (2.b)
  // **Open Q:** How is this protected beyond being stored in flash?
  boot_policy = read_boot_policy();

  // Determine which ROM_EXT slot is prioritised (2.b, 2.c.i)
  for ( current_rom_ext_manifest in rom_ext_manifests_to_try(boot_policy) ) {

    // Sanity Check ROM_EXT Manifest (2.c.ii)
    // **Open Q:** Integration with Secure Boot Hardware
    // - Header Format
    // - Plausible Key
    // - Initial Digest Checks
    if (!check_rom_ext_manifest(current_rom_ext_manifest)) {
      // Boot Failure (check policy)
      if (try_next_on_manifest_failed(boot_policy))
        continue
      else
        break
    }

    // Verify ROM_EXT Image Signature (2.c.iii)
    // **Open Q:** Integration with Secure Boot Hardware, OTBN
    // **Open Q:** Key Selection method/mechanism.
    verified = verify_rom_ext_signature_start(pub_key_selector(...),
                                              current_rom_ext_manifest);
    if (!verified) {
      // Signature Failure (check policy)
      if (try_next_on_signature_failed(boot_policy))
        continue
      else
        break
    }

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
    measurements = perform_system_state_measurements();
    if (!boot_allowed(boot_policy, measurements)) {
      // Lifecycle failure (no policy check)
      break
    }

    // CreatorRootKey (2.c.iv)
    // - This is only allowed to be done if we have verified the signature on
    //   the current ROM_EXT.
    root_key_identity = derive_and_lock_creator_root_key_inputs(measurements);

    // **Open Q:** Does Mask ROM just lock down key manager inputs, and let the
    //             ROM_EXT load the key?
    load_root_key(root_key_identity);

    // Lock down Peripherals based on descriptors in ROM_EXT manifest.
    // - This does not cover key-related lockdown, which is done in
    //   `derive_creator_root_key`.
    peripheral_lockdown(current_rom_ext_manifest);

    // PMP Region for ROM_EXT (2.c.v)
    // **Open Q:** Integration with Secure Boot Hardware
    // **Open Q:** Do we need to prevent access to Mask ROM after final jump?
    pmp_unlock_rom_ext();

    // Transfer Execution to ROM_EXT (2.c.vi)
    // **Open Q:** Integration with Secure Boot Hardware
    // **Open Q:** Accumulated measurements to tie manifest to hardware config.
    if (!final_jump_to_rom_ext(current_rom_ext_manifest)) {
      // Boot Failure (no policy check)
      // - Because we may have locked some write-enable bits that any following
      //   manifest cannot change if it needs to, we have to just reboot here.
      boot_failed(boot_policy, current_rom_ext_manifest);
    }
  }

  // Boot failed for all ROM_EXTs allowed by boot policy
  boot_failed(boot_policy);
}
```

3. Execution Enters ROM_EXT stage.

   Not covered by this document. Refer to Secure Boot document instead.

## Cleaning Device State

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

We cannot execute any C code until we have set up the CRT.

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

## Manufacturing boot-strapping intervention

This is where, depending on lifecycle state, new flash images may be loaded onto
the device (usually during manufacturing).

**Open Q:** Do we want hardware hardening for this?
  There are suggestions around having the hardware return `nop` when reading
  this memory if we're not in the correct lifecycle state.

```c
manufacturing_boot_strap() {
  // 1. Read lifecycle state to establish whether bootstrapping is allowed.
  // 2. Determine what kind of bootstrapping is being requested.
  // 3. Load ROM_EXT image into flash if allowed.
  // 4. Reboot device (causing loaded ROM_EXT to be verified then executed).
}
```

## Boot Info Policy

```c
read_boot_policy() {
  // Parameters:
  // - initilized flash_ctrl DIF (for accessing flash info page)
  // Returns:
  // - boot policy struct
  //   **Open Q:** What boot policies do we allow?
  //   - Active ROM_EXT selector (there are only two ROM_EXT slots) (2.b, 2.c.i)
  //   - What to do if digest doesn't match (2.c.ii)
  //   - What to do if signature doesn't verify (2.c.iii)
  //   - What to do if system measurements are not right (2.c.iv)

  // 1. Uses dif_flash_ctrl to issue read of boot info page.
  // 2. Pull this into a struct to return.
}
```

## Lock Down Peripherals

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
