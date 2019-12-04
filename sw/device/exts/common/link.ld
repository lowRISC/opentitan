/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

OUTPUT_ARCH(riscv)

GROUP( -lgcc )

SEARCH_DIR(.)
__DYNAMIC  =  0;

MEMORY
{
    flash (rx)  : ORIGIN = 0x20000000, LENGTH = 0x100000
    ram   (!rx) : ORIGIN = 0x10000000, LENGTH = 0x10000
}

_stack_start = ORIGIN(ram) + LENGTH(ram);

/* We have to align each sector to word boundaries as our current s19->slm
 * conversion scripts are not able to handle non-word aligned sections. */


SECTIONS
{
    .crt : { *(.crt) } > flash

    /* the 256 byte alignment is required by the machine trap vector table */
    .vectors : {
        . = ALIGN(0x100);
        _svectors = .;
        *(.vectors)
        _evectors = .;
    } > flash

    .text : {
        . = ALIGN(0x100);
        _stext = .;
        *(.text.startup)
        *(.text)
        *(.text.unlikely)
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
    }  > flash

    .rodata : {
        . = ALIGN(4);
        *(.rodata);
        *(.rodata.*)
    } > flash

    .shbss :
    {
        . = ALIGN(4);
        *(.shbss)
    } > flash

    /* idata stores the static variable data that will be loaded in ram below */
    .idata :
    {
        . = ALIGN(4);
        _idata = .;
    } > flash

    /* Static variable LMA at end of program
       VMA at start of RAM.  Stack is at end of RAM */
    .data 0x10000000 : AT ( _idata ){
        . = ALIGN(4);
        _sdata  =  .; /* start of data */
        *(.data);
        *(.data.*)
        *(.sdata);
        _edata  =  .; /* end of data */
    } > ram

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
}

ENTRY(main)
