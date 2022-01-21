// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/top_earlgrey/sw/autogen/top_earlgrey_memory.h"
#include "rv_core_ibex_regs.h"
#include "sw/device/silicon_creator/lib/epmp_defs.h"

/**
 * ROM_EXT Interrupt Vector
 */
  .section .vectors, "ax"
  .option push

  // Disable RISC-V instruction compression: we need all instructions to
  // be exactly word wide in the interrupt vector.
  .option norvc

  // Disable RISC-V linker relaxation, as it can compress instructions at
  // link-time, which we also really don't want.
  .option norelax

/**
 * `_rom_ext_interrupt_vector` is an ibex-compatible interrupt vector.
 *
 * Interrupt vectors in Ibex have 32 4-byte entries for 32 possible interrupts. The
 * vector must be 256-byte aligned, as Ibex's vectoring mechanism requires that.
 *
 * Only the following will be used by Ibex:
 * - Exception Handler (Entry 0)
 * - Machine Software Interrupt Handler (Entry 3)
 * - Machine Timer Interrupt Handler (Entry 7)
 * - Machine External Interrupt Handler (Entry 11)
 * - Vendor Interrupt Handlers (Entries 16-31)
 *
 * More information about Ibex's interrupts can be found here:
 *   https://ibex-core.readthedocs.io/en/latest/03_reference/exception_interrupts.html
 */
  .balign 256
  .globl _rom_ext_interrupt_vector
  .type _rom_ext_interrupt_vector, @function
_rom_ext_interrupt_vector:

  // RISC-V Standard (Vectored) Interrupt Handlers:

  // Exception and User Software Interrupt Handler.
  unimp
  // Supervisor Software Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Software Interrupt Handler.
  unimp

  // User Timer Interrupt Handler.
  unimp
  // Supervisor Timer Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine Timer Interrupt Handler.
  unimp

  // User External Interrupt Handler.
  unimp
  // Supervisor External Interrupt Handler.
  unimp
  // Reserved.
  unimp
  // Machine External Interrupt Handler.
  unimp

  // Reserved.
  unimp
  unimp
  unimp
  unimp

  // Vendor Interrupt Handlers:

  // On Ibex interrupt ids 16-30 are for "fast" interrupts.
  .rept 15
  unimp
  .endr

  // On Ibex interrupt id 31 is for non-maskable interrupts.
  unimp

  // Set size so this vector can be disassembled.
  .size _rom_ext_interrupt_vector, .-_rom_ext_interrupt_vector

  // Re-enable compressed instructions, linker relaxation.
  .option pop


/**
 * ROM_EXT runtime initialization code.
 */

  /**
   * NOTE: The "ax" flag below is necessary to ensure that this section
   * is allocated executable space in ROM by the linker.
   */
  .section .crt, "ax"

  /**
   * Linker Relaxation is disabled until `__global_pointer$` is setup, below,
   * because otherwise some sequences may be turned into gp-relative sequences,
   * which is incorrect when `gp` is not initialized.
   */
  .option push
  .option norelax

/**
 * Entry point.
 *
 * This symbol is jumped to from `mask_rom_boot` using the `entry_point` field
 * of the manifest.
 */
  .globl _rom_ext_start_boot
  .type _rom_ext_start_boot, @function
_rom_ext_start_boot:
  // Store the first address to compute the current slot being used.
  // `a0 = pc`
  auipc a0, 0

  /**
   * Disable Interrupts.
   *
   * We cannot disable exceptions, or Ibex's non-maskable interrupts (interrupt
   * 31), so we still need to be careful.
   */

  // Clear `MIE` field of `mstatus` (disable interrupts globally).
  csrci mstatus, 0x8

  /**
   * Clear all the machine-defined interrupts, `MEIE`, `MTIE`, and `MSIE` fields
   * of `mie`.
   */
  li   t0, 0xFFFF0888
  csrc mie, t0

  /**
   * Initialize the Ibex simple address translation to run position dependent
   * code in the virtual flash space.
   * 
   * Before the setup of the address translation the assembly code shall be 
   * position independent, however we don't want to use the `.option pic` 
   * directive as it requires a `got` (Global Offset Table) section. 
   * Therefore pseudoinstructions such as `la` must be avoided because it is
   * expanded differently for`pic` and `nopic` code.
   * i.e:
   *   `la rd, symbol` expands to: `pic`   -> `auipc rd, offsetHi`
   *                                          `lw rd, offsetLo(rd)`
   *
   *                               `nopic` -> `auipc rd, offsetHi`
   *                                          `addi rd, offsetLo`
   *
   * The `pic` expansion will use the GOT whilst the `nopic` expansion will
   * assume we can generate the address as an offset from the PC. As
   * this code is not yet executing in the target address space the PC value
   * will not match what the linker expects and so an incorrect value will be
   * loaded into `rd`.
   * 
   * Then the alternative to load an absolute address as a constant determined
   * at link time (`my_symbol`) is:
   *   `lui rd, %hi(my_symbol)`
   *   `addi rd, rd, %lo(my_symbol)`
   * rather than: 
   *   `la rd, my_symbol`
   */

  // Compute the physical address of this image.
  // `addr = pc - _addr_translation_crt_offset`
  lui t0, %hi(_addr_translation_crt_offset)
  addi t0, t0, %lo(_addr_translation_crt_offset)
  sub a0, a0, t0 
  
  // Compute the matching NAPOT region.
  // `a1 = virtual_addr | ((size - 1) >> 1);`
  lui a1, %hi(_vflash_address)
  addi a1, a1, %lo(_vflash_address)
  lui t0, %hi(_vflash_size - 1)
  addi t0, t0, %lo(_vflash_size - 1)
  srli t0, t0, 1
  or a1, a1,t0 

  // Load ibex config base address.
  li t0, TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR 

  // Set ibus and dbus address matching.
  sw a1, RV_CORE_IBEX_IBUS_ADDR_MATCHING_0_REG_OFFSET(t0)
  sw a1, RV_CORE_IBEX_DBUS_ADDR_MATCHING_0_REG_OFFSET(t0)

  // Set ibus and dbus address remap.
  sw a0, RV_CORE_IBEX_IBUS_REMAP_ADDR_0_REG_OFFSET(t0)
  sw a0, RV_CORE_IBEX_DBUS_REMAP_ADDR_0_REG_OFFSET(t0)

  // Enable address translation.
  li t1, 0x01
  sw t1, RV_CORE_IBEX_IBUS_ADDR_EN_0_REG_OFFSET(t0)
  sw t1, RV_CORE_IBEX_DBUS_ADDR_EN_0_REG_OFFSET(t0) 

  #define EPMP_CFG_PMPCFG_MASK    (0XFF) 
  #define EPMP_CFG_PMPCFG7_OFFSET ((7 * 8) % 32) 
  #define EPMP_CFG_PMPCFG7_MASK   (EPMP_CFG_PMPCFG_MASK << EPMP_CFG_PMPCFG7_OFFSET)
  #define EPMP_CFG_PMPCFG8_OFFSET ((8 * 8) % 32) 
  #define EPMP_CFG_PMPCFG8_MASK   (EPMP_CFG_PMPCFG_MASK << EPMP_CFG_PMPCFG8_OFFSET)
  #define EPMP_CFG_PMPCFG9_OFFSET ((9 * 8) % 32)
  #define EPMP_CFG_PMPCFG9_MASK   (EPMP_CFG_PMPCFG_MASK << EPMP_CFG_PMPCFG9_OFFSET)
  /**
   * Asserting that the epmp entries as free by checking that the registers pmpaddr7,
   * pmpaddr8, pmpaddr9, pmpcfg7, pmpcfg8 and  pmpcfg9 are all zeros.
   *  ``` 
   *  if ((pmpaddr7 | pmpaddr8 | pmpaddr9 | pmpcfg7 | pmpcfg8 | pmpcfg9) != 0){
   *     _rom_ext_epmp_error();
   *  }
   *  ``` 
   */
  csrr t1, pmpaddr7
  csrr t0, pmpaddr8
  or t1, t1, t0
  csrr t0, pmpaddr9
  or t1, t1, t0
  csrr t0, pmpcfg1
  li t2, EPMP_CFG_PMPCFG7_MASK
  and t0, t0, t2
  or t1, t1, t0
  csrr t0, pmpcfg2
  li t2, (EPMP_CFG_PMPCFG8_MASK | EPMP_CFG_PMPCFG9_MASK)
  and t0, t0, t2
  or t1, t1, t0
  bnez t1, _rom_ext_epmp_error 
  /**
   * Configure the epmp to enable execution in the text space only and
   * read in the whole vFlash space.
   *   | Entry | Description                   | Permissions | Addressing Mode |
   *   |-------|-------------------------------|-------------|-----------------|
   *   | 7     | vflash `ROM_EXT` text start   | RX          | OFF             |
   *   | 8     | vflash `ROM_EXT` text end     | RX          | TOR             | 
   *   | 9     | vFlash                        | R           | NAPOT           |
   */
_rom_ext_start_boot_set_epmp_:  
  // `pmpaddr7 = (_text_start >> 2)` 
  lui t0, %hi(_text_start)
  addi t0, t0, %lo(_text_start) 
  srli t0, t0, 2
  csrw pmpaddr7,t0
  
  // `pmpaddr8 = (_text_end >> 2)`
  lui t0, %hi(_text_end)
  addi t0, t0, %lo(_text_end) 
  srli t0, t0, 2
  csrw pmpaddr8,t0
  
  // Set the bits for the 8th epmp config entry.
  li t0, ((EPMP_CFG_A_TOR | EPMP_CFG_L | EPMP_CFG_R | EPMP_CFG_X) << EPMP_CFG_PMPCFG8_OFFSET)
  csrs pmpcfg2, t0

  lui a0, %hi(_vflash_address)
  addi a0, a0, %lo(_vflash_address) 
  lui a1, %hi(_vflash_size)
  addi a1, a1, %lo(_vflash_size) 

  // `pmpaddr9 = (_vflash_address >> 2) | ((_vflash_size - 1) >> 3)`
  addi t0, a1, -1
  srli t0, t0, 3
  srli t1, a0, 2
  or t1, t1, t0
  csrw pmpaddr9,t1
  
  // Set the bits for the 9th pmp config entry.
  li t0, ((EPMP_CFG_A_NAPOT | EPMP_CFG_L | EPMP_CFG_R) << EPMP_CFG_PMPCFG9_OFFSET)
  csrs pmpcfg2, t0

  /**
   * Jump to the virtual address.
   */
  lui t0, %hi(_rom_ext_start_c)
  addi t0, t0, %lo(_rom_ext_start_c) 
  jr t0
  // Set size so this function can be disassembled.
  .size _rom_ext_start_boot, .-_rom_ext_start_boot


_rom_ext_epmp_error:
  unimp
/**
 * This subroutine initialize the C Runtime and jump to the `main`.
 */
  .globl _rom_ext_start_c
  .type _rom_ext_start_c, @function
_rom_ext_start_c:

  /**
   * Set up the stack pointer.
   *
   * In RISC-V, the stack grows downwards, so we load the address of the highest
   * word in the stack into sp. We don't load in `_stack_end`, as that points
   * beyond the end of RAM, and we always want it to be valid to dereference
   * `sp`, and we need this to be 128-bit (16-byte) aligned to meet the psABI.
   *
   * If an exception fires, the handler is conventionaly only allowed to clobber
   * memory at addresses below `sp`.
   */
  
  la sp, (_stack_end - 16)

  /**
   * Setup C Runtime.
   */

  /**
   * Initialize the `.data` section in RAM from ROM.
   */
  la   a0, _data_start
  la   a1, _data_end
  la   a2, _data_init_start
  .extern crt_section_copy
  call crt_section_copy

  /**
   * Initialize the `.bss` section.
   *
   * We do this despite zeroing all of SRAM above, so that we still zero `.bss`
   * once we've enabled SRAM scrambling.
   */
  la   a0, _bss_start
  la   a1, _bss_end
  .extern crt_section_clear
  call crt_section_clear

  // Re-clobber all of the temporary registers.
  li t0, 0x0
  li t1, 0x0
  li t2, 0x0
  li t3, 0x0
  li t4, 0x0
  li t5, 0x0
  li t6, 0x0

  // Re-clobber all of the argument registers.
  li a0, 0x0
  li a1, 0x0
  li a2, 0x0
  li a3, 0x0
  li a4, 0x0
  li a5, 0x0
  li a6, 0x0
  li a7, 0x0

  /**
   * Setup global pointer.
   *
   * This requires that we disable linker relaxations, or it will be relaxed to
   * `mv gp, gp`, so we disabled relaxations for all of `_mask_rom_start_boot`.
   */
  la gp, __global_pointer$

  /**
   * Set well-defined interrupt/exception handlers.
   *
   * The lowest two bits should be `0b01` to ensure we use vectored interrupts.
   */
  la   t0, (_rom_ext_interrupt_vector + 1)
  csrw mtvec, t0

  // Re-enable linker relaxation.
  .option pop

  /**
   * Jump to C Code
   */
  .extern rom_ext_main
  tail rom_ext_main

  // Set size so this function can be disassembled.
  .size _rom_ext_start_c, .-_rom_ext_start_c

