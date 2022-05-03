/* Layout file for Tock process binaries that use libtock-rs. This currently
 * implements static linking, because we do not have a working
 * position-independent relocation solution. This layout works for all
 * platforms libtock-rs supports (ARM and RISC-V).
 *
 * This layout should be included by a script that defines the FLASH and RAM
 * regions for the board as well as TBF_HEADER_SIZE. Here is a an example
 * process binary linker script to get started:
 *     MEMORY {
 *         FLASH (X) : ORIGIN = 0x10000, LENGTH = 0x10000
 *         RAM   (W) : ORIGIN = 0x20000, LENGTH = 0x10000
 *     }
 *     TBF_HEADER_SIZE = 0x48;
 *     INCLUDE ../libtock-rs/layout.ld
 *
 * FLASH refers to the area the process binary occupies in flash, including TBF
 * headers. RAM refers to the area the process will have access to in memory.
 * STACK_SIZE is the size of the process' stack (this layout file may round the
 * stack size up for alignment purposes). TBF_HEADER_SIZE must correspond to the
 * --protected-region-size flag passed to elf2tab.
 *
 * This places the flash sections in the following order:
 *     1. .rt_header -- Constants used by runtime initialization.
 *     2. .text      -- Executable code.
 *     3. .rodata    -- Read-only global data (e.g. most string constants).
 *     4. .data      -- Read-write data, copied to RAM at runtime.
 *
 * This places the RAM sections in the following order:
 *     1. .stack -- The stack grows downward. Putting it first gives us
 *                  MPU-based overflow detection.
 *     2. .data  -- Read-write data, initialized by copying from flash.
 *     3. .bss   -- Zero-initialized read-write global data.
 *     4. Heap   -- The heap (optional) comes after .bss and grows upwards to
 *                  the process break.
 */

/* TODO: Should TBF_HEADER_SIZE be configured via a similar mechanism to the
 * stack size? We should see if that is possible.
 */

/* GNU LD looks for `start` as an entry point by default, while LLVM's LLD looks
 * for `_start`. To be compatible with both, we manually specify an entry point.
 */
ENTRY(start)

SECTIONS {
    /* Sections located in FLASH at runtime.
     */

    /* Add a section where elf2tab will place the TBF headers, so that the rest
     * of the FLASH sections are in the right locations. */


    .tbf_header (NOLOAD) : {
        . = . + TBF_HEADER_SIZE;
    } > FLASH



    /* Runtime header. Contains values the linker knows that the runtime needs
     * to look up.
     */
    .start ALIGN(4) : {
        /* We combine rt_header and _start into a single section. If we don't,
         * elf2tab does not parse the ELF file correctly for unknown reasons.
         */
        rt_header = .;
        LONG(start & 0xFFFFFFFE);        /* .start w/ Thumb bit unset */
        LONG(ADDR(.bss) + SIZEOF(.bss)); /* Initial process break */
        LONG(_stack_top);
        LONG(SIZEOF(.data));
        LONG(LOADADDR(.data));
        LONG(ADDR(.data));
        LONG(SIZEOF(.bss));
        LONG(ADDR(.bss));

        *(.start)
    } > FLASH

    /* Text section -- the application's code. */
    .text ALIGN(4) : {
        *(.text.*)
    } > FLASH

    /* Read-only data section. Contains strings and other global constants. */
    .rodata ALIGN(4) : {
        *(.rodata.*)
        /* .data is placed after .rodata in flash. data_flash_start is used by
         * AT() to place .data in flash as well as in rt_header.
         */
        _data_flash_start = .;
    } > FLASH

    /* Sections located in RAM at runtime.
     */

    /* Reserve space for the stack. Aligned to a multiple of 16 bytes for the
     * RISC-V calling convention:
     * https://riscv.org/wp-content/uploads/2015/01/riscv-calling.pdf
     */
    .stack (NOLOAD) : {
	/* _sram_origin is used by elf2tab:
	 * https://github.com/tock/elf2tab/blob/master/src/main.rs#L301
	 */
        _sram_origin = .;
        KEEP(*(.stack_buffer))
        . = ALIGN(16);
        _stack_top = .;  /* Used in rt_header */
    } > RAM

    /* Read-write data section. This is deployed as part of FLASH but is copied
     * into RAM at runtime.
     */
    .data ALIGN(4) : AT(_data_flash_start) {
        data_ram_start = .;
        /* .sdata is the RISC-V small data section */
        *(.sdata .data)
        /* Pad to word alignment so the relocation loop can use word-sized
         * copies.
         */
        . = ALIGN(4);
    } > RAM

    /* BSS section. These are zero-initialized static variables. This section is
     * not copied from FLASH into RAM but rather directly initialized, and is
     * mainly put in this linker script so that we get an error if it overflows
     * the RAM region.
     */
    .bss ALIGN(4) (NOLOAD) : {
        /* .sbss is the RISC-V small data section */
        *(.sbss .bss.*)
    } > RAM

    _heap_start = ADDR(.bss) + SIZEOF(.bss);  /* Used by rt_header */

    /* Sections we do not need. */
    /DISCARD/ :
    {
      *(.ARM.exidx .eh_frame)
    }
}
