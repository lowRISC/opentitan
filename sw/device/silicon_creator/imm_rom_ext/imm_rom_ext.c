// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/imm_rom_ext/imm_rom_ext.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/cert/dice_chain.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_manifest.h"

OT_WARN_UNUSED_RESULT
static rom_error_t imm_rom_ext_start(void) {
  // Check the ePMP state.
  HARDENED_RETURN_IF_ERROR(epmp_state_check());
  // Check sec_mmio expectations.
  // We don't check the counters since we don't want to tie ROM_EXT to a
  // specific ROM version.
  sec_mmio_check_values(rnd_uint32());

  // Initialize Immutable ROM EXT.
  sec_mmio_next_stage_init();
  // Configure UART0 as stdout.
  pinmux_init_uart0_tx();
  uart_init(kUartNCOValue);

  dbg_printf("IMM_ROM_EXT:0.1\r\n");

  // Establish our identity.
  const manifest_t *rom_ext = rom_ext_manifest();
  HARDENED_RETURN_IF_ERROR(dice_chain_init());
  // TODO: Move UDS cert check to mutable ROM_EXT.
  HARDENED_RETURN_IF_ERROR(dice_chain_attestation_silicon());

  // Sideload sealing key to KMAC hw keyslot.
  HARDENED_RETURN_IF_ERROR(ownership_seal_init());

  HARDENED_RETURN_IF_ERROR(
      dice_chain_attestation_creator(&boot_measurements.rom_ext, rom_ext));

  // Write the DICE certs to flash if they have been updated.
  HARDENED_RETURN_IF_ERROR(dice_chain_flush_flash());

  return kErrorOk;
}

void imm_rom_ext_main(void) {
  rom_error_t error = imm_rom_ext_start();
  if (launder32(error) != kErrorOk) {
    shutdown_finalize(error);
  }
  HARDENED_CHECK_EQ(error, kErrorOk);

  // Go back to ROM / Mutable ROM_EXT.
  return;
}
