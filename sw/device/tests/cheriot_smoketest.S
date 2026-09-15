// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Checks that a CHERIoT binary can be built, booted and executed on the chip.
 *
 * Emits a marker straight to UART0 and parks the core. Whatever booted it has
 * already configured UART0 for its own logging, so no driver setup is needed.
 */

#include "hw/top/rv_core_ibex_regs.h"  // Generated.
#include "hw/top/uart_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "sw/device/tests/cheriot_manifest.h"

// kMuBi4True. Spelled out rather than included, because `multibits.h` pulls in
// the wider base library, which does not yet build for CHERIoT.
#define MUBI4_TRUE 6

// The link-dependent `manifest_t` fields, which `manifest_def.c` would emit if
// it built for CHERIoT. `opentitantool` fills in the rest at signing time.

  .section .manifest, "a", @progbits
  .balign 4
  .globl kManifest
  .type kManifest, @object
kManifest:
  .org MANIFEST_ADDRESS_TRANSLATION_OFFSET
  .word _manifest_address_translation

  .org MANIFEST_VERSION_MINOR_OFFSET
  .short MANIFEST_VERSION_MINOR_1
  .org MANIFEST_VERSION_MAJOR_OFFSET
  .short MANIFEST_VERSION_MAJOR_2

  .org MANIFEST_CODE_START_OFFSET
  .word _manifest_code_start
  .org MANIFEST_CODE_END_OFFSET
  .word _manifest_code_end
  .org MANIFEST_ENTRY_POINT_OFFSET
  .word _manifest_entry_point

  .org MANIFEST_SIZE
  .size kManifest, . - kManifest

// -----------------------------------------------------------------------------

/**
 * Trap handler, for diagnostics only.
 *
 * Without this every failure looks identical from the console - output simply
 * stops - whether the mode switch never took effect or the core faulted after
 * it did. This emits one of
 *
 *   RTRAP <mcause>    entered in RV32 mode - the mode switch did not take
 *   CTRAP <mcause>    entered in CHERIoT mode - the switch worked, something
 *                     after it faulted
 *
 * telling the two apart by MISA.E, which reads as set only while CHERIoT mode
 * is active; see `misa_value_masked` in ibex_cs_registers.sv.
 *
 * `mtvec` is installed in direct mode before the mode switch, while a plain
 * `csrw` to it is still legal, so no vector table is needed. It stays valid
 * afterwards: an RV32-mode write only updates the address half, leaving
 * `mtvec_cap` at the executable root, so in CHERIoT mode `mtcc` still points
 * here with a PCC that covers it.
 *
 * Only the base register setup differs between the two paths; the shared body
 * must stick to instructions that encode identically in both modes, which
 * rules out advancing a pointer through the string.
 */
  .section .vectors, "ax", @progbits
  .option push
  .option norvc
  .option norelax

  // mtvec direct mode requires the address to be 4-byte aligned; the 256-byte
  // alignment is the Ibex convention for this section.
  .balign 256
  .globl _trap_handler
  .type _trap_handler, @function
_trap_handler:
  csrr t0, misa
  andi t0, t0, (1 << 4)
  bnez t0, .L_trap_cheriot

  // RV32: an integer base is all the store needs.
  lui  t1, %hi(TOP_EARLGREY_UART0_BASE_ADDR)
  addi t2, x0, 'R'
  j    .L_trap_mark

.L_trap_cheriot:
  // CHERIoT: the store needs a capability. `mtdc` is still the memory root, so
  // narrow a copy of it onto the UART register window.
  cspecialr t1, mtdc
  lui       t2, %hi(TOP_EARLGREY_UART0_BASE_ADDR)
  csetaddr  t1, t1, t2
  csetboundsimm t1, t1, 0x40
  addi      t2, x0, 'C'

.L_trap_mark:
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, 'T'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, 'R'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, 'A'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, 'P'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, ' '
  sw   t2, UART_WDATA_REG_OFFSET(t1)

  // `mcause` as eight hex digits, most significant first.
  csrr s0, mcause
  addi s1, x0, 8
.L_trap_nibble:
  srli a0, s0, 28
  slli s0, s0, 4
  addi a1, x0, 10
  blt  a0, a1, .L_trap_digit
  addi a0, a0, ('a' - 10 - '0')
.L_trap_digit:
  addi a0, a0, '0'
  sw   a0, UART_WDATA_REG_OFFSET(t1)
  addi s1, s1, -1
  bnez s1, .L_trap_nibble

  addi t2, x0, '\r'
  sw   t2, UART_WDATA_REG_OFFSET(t1)
  addi t2, x0, '\n'
  sw   t2, UART_WDATA_REG_OFFSET(t1)

.L_trap_park:
  wfi
  j    .L_trap_park
  .size _trap_handler, . - _trap_handler

  .option pop

// -----------------------------------------------------------------------------

  .section .crt, "ax", @progbits
  .balign 4
  .globl _start_boot
  .type _start_boot, @function
_start_boot:
  // Whatever booted this hands over with the core still in RV32 mode, so
  // everything up to the switch below executes as RV32 despite being assembled
  // for CHERIoT. That works because CHERIoT reuses the standard load/store
  // encodings, so `sw t1, off(t0)` and `csw t1, off(ct0)` are the same four
  // bytes; expect the disassembly to show the stores as `ct.csw`.
  //
  // Compression and relaxation are off so the encodings cannot depend on
  // assembler choices.
  .option push
  .option norvc
  .option norelax

  // Install the diagnostic trap handler first, in direct mode, so that it is
  // already armed if the switch itself faults.
  //
  // The absolute `%hi`/`%lo` form works because both variants are linked for
  // a physical slot, with address translation off.
  lui  t0, %hi(_trap_handler)
  addi t0, t0, %lo(_trap_handler)
  csrw mtvec, t0

  // Switch to CHERIoT. `CHERIOT_ENA` is only sampled when `CHERIOT_LOCK` is
  // written, and that write is once-only: any lock value other than kMuBi4True
  // parks the switch FSM in a terminal error state and raises the fatal alert.
  lui  t0, %hi(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR)
  addi t1, x0, MUBI4_TRUE
  sw   t1, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(t0)
  sw   t1, RV_CORE_IBEX_CHERIOT_LOCK_REG_OFFSET(t0)
  fence.i
  .option pop

  // Everything from here on both is and executes as CHERIoT.

  // Derive an MMIO capability for UART0 and emit the marker before doing
  // anything else, so that a fault later on cannot swallow the evidence that
  // the mode switch worked.
  //
  // `mtdc` holds the memory root capability: it resets to ROOT_CAP_TM and is
  // only ever written by software, so it survives RV32 execution untouched.
  // PCC cannot be used for this - the executable root has SD=0, no store
  // permission.
  cspecialr ct1, mtdc
  li        t2, TOP_EARLGREY_UART0_BASE_ADDR
  csetaddr  ct1, ct1, t2
  csetboundsimm ct1, ct1, 0x40

  // Walk the NUL-terminated marker string.
  cllc     ca2, kBootMsg

.L_tx_next:
  clbu     a4, 0(ca2)
  beqz     a4, .L_done
  cincoffsetimm ca2, ca2, 1

  // Spin while the transmit FIFO is full, then push the byte.
.L_tx_wait:
  clw      a5, UART_STATUS_REG_OFFSET(ct1)
  andi     a5, a5, (1 << UART_STATUS_TXFULL_BIT)
  bnez     a5, .L_tx_wait
  csw      a4, UART_WDATA_REG_OFFSET(ct1)
  j        .L_tx_next

.L_done:
  wfi
  j        .L_done
  .size _start_boot, . - _start_boot

  .section .rodata, "a", @progbits
  .balign 4
kBootMsg:
  .asciz "CHERIoT PASS!\r\n"
