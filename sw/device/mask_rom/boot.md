# Pseudo-code for Secure Boot Process.

This file should be read in conjunction with secure boot specification. Some
references to that document are included.


1. Power on (entirely in hardware) Open Q: Whether SW has to configure PMP
  initial region.

2. Execution Begins
  - CRT Startup Code (ASM)
    - Clean Slate (SRAM, Registers)
    - Well-defined interrupt/exception handler
        Open Q: Do we want to enable interrupts in mask rom?
    - Jump into C code (`boot`):

```c
void boot(void) {
  // - Clean all other hardware state (using DIF Reset functions)
  clean_device_state();

  // - Chip-specific startup functionality
  //   - Clocks
  //   - AST
  //   - Flash
  //   - Entropy
  //   Open Q: Proprietary Software Strategy.
  chip_specific_startup();

  // - Read Boot Policy for ROM_EXT from Flash (2.b)
  //   Open Q: How is this protected beyond being in flash?
  boot_policy = read_boot_policy();

  // - Determine which rom_ext slot is in use (2.b,2.c.i)
  rom_ext_manifest = read_rom_ext_slot(boot_policy);

  // Verify ROM_EXT Image Digest (2.c.ii)
  if (!verify_rom_ext_hash(rom_ext_manifest)) {
    // Boot Failure (check policy)
  }

  // Verify Signature (2.c.iii)
  valid, signature = verify_rom_ext_signature(rom_ext_manifest);
  if (!valid) {
    // Boot Failure (check policy)
  }

  // System State Measurements (2.c.iv)
  measurements = perform_system_state_measurements();
  if (!boot_allowed(measurements)) {
    // Lifecycle failure (no policy check)
  }

  // CreatorRootKey (2.c.iv)
  root_key_identity = derive_creator_root_key(measurements);
  load_root_key(root_key_identity);

  // PMP Region for ROM_EXT (2.c.v)
  //   Open Q: Do we need to lock down Boot ROM at final jump?
  pmp_unlock_rom_ext();

  // Lock down Peripherals based on descriptors in rom_ext
  peripheral_lockdown(rom_ext_manifest);

  // Transfer Execution to ROM_EXT (2.c.vi)
  if (!final_jump_to_rom_ext(rom_ext_manifest, signature)) {
    // Boot Failure (check_policy)
  }
}
```

## Boot Info Policy

```c
read_boot_policy() {
  // Parameters:
  // - initilized flash_ctrl DIF (for accessing flash info page)
  // Returns:
  // - boot policy struct
  //   Open Qs: What boot policies do we allow?
  //   - What to do if hash doesn't match (2.c.ii)
  //   - What to do if signature doesn't verify
  //   - What to do if final jump does not succeed
  //   - rom_ext selector (there will only be two)

  // 1. Uses dif_flash_ctrl to issue read of boot info page.
  // 2. pull this into a struct to return.
}
```

## Lockdown Peripherals

```c
peripheral_lockdown() {
  // Parameters:
  // - rom_ext manifest
  // - Handles for Peripheral DIFs


  // When and How do we lock down peripheral configuration?
  // - We configure based on rom_ext manifest (signed)
  // - mask_rom only locks down these peripherals if info is provided.

  // What do we want to allow lockdown of?
  // - Alert Manager
  // - Pinmux / Padctrl
  // - Entropy Configuration
  // - anything else?
}
```
