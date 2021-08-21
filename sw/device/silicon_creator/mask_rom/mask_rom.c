// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/mask_rom.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify.h"
#include "sw/device/silicon_creator/mask_rom/boot_policy.h"
#include "sw/device/silicon_creator/mask_rom/mask_rom_epmp.h"
#include "sw/device/silicon_creator/mask_rom/sigverify_keys.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// TODO(#7325): Defined here for now to be able to use the OTP driver since
// sec_mmio requires this symbol. For the actual target, we need to define a
// memory region to share the data with ROM_EXT.
sec_mmio_ctx_t sec_mmio_ctx;

static inline rom_error_t mask_rom_irq_error(void) {
  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);
  // Shuffle the mcause bits into the uppermost byte of the word and report
  // the cause as kErrorInterrupt.
  // Based on the ibex verilog, it appears that the most significant bit
  // indicates whether the cause is an exception (0) or external interrupt (1),
  // and the 5 least significant bits indicate which exception/interrupt.
  //
  // Preserve the MSB and shift the 7 LSBs into the upper byte.
  // (we preserve 7 instead of 5 because the verilog hardcodes the unused bits
  // as zero and those would be the next bits used should the number of
  // interrupt causes increase).
  mcause = (mcause & 0x80000000) | ((mcause & 0x7f) << 24);
  return kErrorInterrupt + mcause;
}

void mask_rom_interrupt_handler(void) {
  shutdown_finalize(mask_rom_irq_error());
}

// We only need a single handler for all mask ROM interrupts, but we want to
// keep distinct symbols to make writing tests easier.  In the mask ROM,
// alias all interrupt handler symbols to the single handler.
void mask_rom_exception_handler(void)
    __attribute__((alias("mask_rom_interrupt_handler")));

void mask_rom_nmi_handler(void)
    __attribute__((alias("mask_rom_interrupt_handler")));

rom_error_t mask_rom_boot(void) {
  // Initialize the shutdown policy according to lifecycle state.
  lifecycle_state_t lc_state = lifecycle_state_get();
  shutdown_init(lc_state);

  // Initiaize shadow copy of the ePMP register configuration.
  epmp_state_t epmp;
  mask_rom_epmp_state_init(&epmp);

  // Initialize pinmux configuration so we can use the UART.
  pinmux_init();

  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);
  base_set_stdout((buffer_sink_t){
      .data = NULL,
      .sink = uart_sink,
  });

  // FIXME: what (if anything) should we print at startup?
  base_printf("OpenTitan: \"version-tag\"\r\n");
  base_printf("lc_state: %s\r\n", lifecycle_state_name[lc_state]);

  // boot_reason = read_boot_reason(); // Boot Policy Module

  // Clean Device State Part 2.
  // See "Cleaning Device State" Below.
  // clean_device_state_part_2(boot_reason); // Chip-Specific Startup Module

  // Chip-specific startup functionality (NOTE: we expect this portion of
  // initialization to be done in assembly before C runtime init.  Delete
  // this segment of comments & pseudo-code when done).
  // **Open Q:** Proprietary Software Strategy.
  // - Clocks
  // - AST / Entropy.
  // - Flash
  // - Fuses
  // chip_specific_startup(); // Chip-Specific Startup Module

  // Manufacturing boot-strapping intervention.
  // **Open Q:** How does the Mask ROM deal with chip recovery?
  // Tentative answer: recovery is performed by ROM_EXT.
  // **Open Q:** Pin Strapping Configuration.
  // manufacturing_boot_strap(boot_policy, boot_reason); // Bootstrap Module

  // Read Boot Policy for ROM_EXTs from flash (2.b)
  // boot_policy = read_boot_policy(boot_reason); // Boot Policy Module

  // Determine which ROM_EXT slot is prioritised (2.b, 2.c.i)
  // for ( current_rom_ext_manifest in rom_ext_manifests_to_try(boot_policy) ) {
  // // Boot Policy Module
  while (true) {
    // Check ROM_EXT Manifest (2.c.ii)
    // **Open Q:** Integration with Secure Boot Hardware
    // - Header Format (ROM_EXT Manifest Module)
    // - **Open Q**: ROM_EXT Anti-rollback (??)
    // if (!check_rom_ext_manifest(current_rom_ext_manifest)) {
    //  // Manifest Failure (check Boot Policy)
    //  if (try_next_on_manifest_failed(boot_policy)) // Boot Policy Module
    //    continue
    //  else
    //    break
    //}

    const manifest_t *manifest = boot_policy_manifests_get().ordered[0];
    const sigverify_rsa_key_t *key;
    RETURN_IF_ERROR(boot_policy_manifest_check(manifest));
    manifest_signed_region_t signed_region =
        manifest_signed_region_get(manifest);
    RETURN_IF_ERROR(sigverify_rsa_key_get(
        sigverify_rsa_key_id_get(&manifest->modulus), lc_state, &key));
    RETURN_IF_ERROR(sigverify_rsa_verify(signed_region.start,
                                         signed_region.length,
                                         &manifest->signature, key, lc_state));

    //  // Manifest Failure (check Boot Policy)
    //  // **Open Q:** Does this need different logic to the check after
    //  //   `check_rom_ext_manifest`?
    //  if (try_next_on_manifest_failed(boot_policy)) // Boot Policy Module
    //    continue
    //  else
    //    break
    //}

    // Update Boot Policy on Successful Signature
    // **Open Q:** Does this ensure ROM_EXT Anti-rollback is updated?
    // update_next_boot_policy(boot_policy, current_rom_ext_manifest); // Boot
    // Policy Module

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

    // CreatorRootKey (2.c.iv)
    // - This is only allowed to be done if we have verified the signature on
    //   the current ROM_EXT.
    RETURN_IF_ERROR(keymgr_check_state(kKeymgrStateReset));
    keymgr_set_next_stage_inputs(&manifest->binding_value,
                                 manifest->max_key_version);

    // Lock down Peripherals based on descriptors in ROM_EXT manifest.
    // - This does not cover key-related lockdown, which is done in
    //   `derive_and_lock_creator_root_key_inputs`.
    // peripheral_lockdown(current_rom_ext_manifest); // Lockdown Module

    // PMP Region for ROM_EXT (2.c.v)
    // **Open Q:** Integration with Secure Boot Hardware
    // **Open Q:** Do we need to prevent access to Mask ROM after final jump?
    // pmp_unlock_rom_ext(); // Hardened Jump Module.

    // Transfer Execution to ROM_EXT (2.c.vi)
    // **Open Q:** Integration with Secure Boot Hardware
    // **Open Q:** Accumulated measurements to tie manifest to hardware config.
    // if (!final_jump_to_rom_ext(current_rom_ext_manifest)) { // Hardened Jump
    // Module
    if (true) {
      // Unlock execution of ROM_EXT executable code (text) sections.
      RETURN_IF_ERROR(epmp_state_check(&epmp));
      mask_rom_epmp_unlock_rom_ext_rx(&epmp,
                                      manifest_code_region_get(manifest));
      RETURN_IF_ERROR(epmp_state_check(&epmp));

      // Jump to ROM_EXT entry point.
      uintptr_t entry_point = manifest_entry_point_get(manifest);
      base_printf("rom_ext_entry: %p\r\n", entry_point);
      ((rom_ext_entry_point *)entry_point)();
      // NOTE: never expecting a return, but if something were to go wrong
      // in the real `jump` implementation, we need to enter a failure case.

      // Boot Failure (no policy check)
      // - Because we may have locked some write-enable bits that any following
      //   manifest cannot change if it needs to, we have to just reboot here.
      // boot_failed(boot_policy, current_rom_ext_manifest); // Boot Policy
      // Module
    }
  }

  return kErrorMaskRomBootFailed;
}

void mask_rom_main(void) {
  sec_mmio_init(shutdown_finalize);
  rom_error_t error = mask_rom_boot();
  shutdown_finalize(error);
}
