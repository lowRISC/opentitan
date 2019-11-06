/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

OUTPUT_ARCH(riscv)

GROUP( -lgcc )

SEARCH_DIR(.)
__DYNAMIC  =  0;

MEMORY
{
    rom (rx)     : ORIGIN = 0x00008000, LENGTH = 0x2000
    ram (w)      : ORIGIN = 0x10000000, LENGTH = 0x10000
    flash (rx)   : ORIGIN = 0x20000000, LENGTH = 0x100000
}

/* Memory Allocation */
_heap_size = 0xe000;
_stack_size = 0x2000;
_stack_start = ORIGIN(ram) + _heap_size + _stack_size;
_flash_start = ORIGIN(flash);
_chip_info_size = 128;
_chip_info_start = ORIGIN(rom) + LENGTH(rom) - _chip_info_size;

/* We have to align each sector to word boundaries as our current s19->slm
 * conversion scripts are not able to handle non-word aligned sections. */

SECTIONS
{
    .vectors :
    {
        . = ALIGN(4);
        KEEP(*(.vectors))
    } > rom

    .text : {
        . = ALIGN(4);
        _stext = .;
        *(.text.startup)
        *(.text)
        _etext  =  .;
        __CTOR_LIST__ = .;
        LONG((__CTOR_END__ - __CTOR_LIST__) / 4 - 2)
        *(.ctors)
        LONG(0)
        __CTOR_END__ = .;
        __DTOR_LIST__ = .;
        LONG((__DTOR_END__ - __DTOR_LIST__) / 4 - 2)
        *(.dtors)
        LONG(0)
        __DTOR_END__ = .;
        *(.lit)
        *(.shdata)
        _endtext = .;
    }  > rom

    .rodata : {
        . = ALIGN(4);
        *(.rodata);
        *(.rodata.*)
    } > rom

    .shbss :
    {
        . = ALIGN(4);
        *(.shbss)
    } > rom

    .data : {
        . = ALIGN(4);
        sdata  =  .;
        _sdata  =  .;
        *(.data);
        *(.data.*)
        edata  =  .;
        _edata  =  .;
    } > rom

    .chip_info _chip_info_start : {
        . = ALIGN(4);
        *(.chip_info)
    } > rom

    .bss :
    {
        . = ALIGN(4);
        _bss_start = .;
        *(.bss)
        *(.bss.*)
        *(.sbss)
        *(.sbss.*)
        *(COMMON)
        _bss_end = .;
    } > ram

    .stab  0 (NOLOAD) :
    {
        [ .stab ]
    }

    .stabstr  0 (NOLOAD) :
    {
        [ .stabstr ]
    }

    /* Discard the remaining sections */
    /DISCARD/ : { *(*) }
}
