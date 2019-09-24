OUTPUT_ARCH(riscv)

/* required to correctly link newlib */
GROUP( -lc -lgloss -lgcc -lsupc++ )

SEARCH_DIR(.)
__DYNAMIC  =  0;

_rom_size = 0x2000;
_rom_start = 0x00008000;
_rom_end = _rom_start + _rom_size;

_ram_size = 0x10000;
_ram_start = 0x10000000;
_ram_end = _ram_start + _ram_size;

_flash_size = 0x100000;
_flash_start = 0x20000000;
_flash_end = _flash_start + _flash_size;

#if MSG_FLOW == elf

#ifdef MSG_MEM_START
_msg_mem_start = MSG_MEM_START;
#else
_msg_mem_start = 0xe0000000;
#endif

#ifdef MSG_MEM_SIZE
_msg_mem_size = MSG_MEM_SIZE;
#else
_msg_mem_size = 256M;
#endif

#endif

MEMORY
{
    rom    (rx)     : ORIGIN = _rom_start, LENGTH = _rom_size
    ram    (w)      : ORIGIN = _ram_start, LENGTH = _ram_size
    flash  (rx)     : ORIGIN = _flash_start, LENGTH = _flash_end
#if MSG_FLOW == elf
    /* Fake memory for extracting messages from print strings from elf */
    msg_mem(!r!w!x) : ORIGIN = _msg_mem_start, LENGTH = _msg_mem_size
#endif
}

/* Memory Allocation */
_heap_size = 0xe000;
#if MSG_FLOW == elf
/* Reserve upper 32 bytes of ram for DV */
_dv_rsvd_ram_size = 0x20;
#else
_dv_rsvd_ram_size = 0x0;
#endif
_stack_size = _ram_size - _heap_size - _dv_rsvd_ram_size;

/* Reserving upper 32 bytes of ram for DV */
_stack_start = _ram_start + _heap_size + _stack_size;
_chip_info_size = 128;
_chip_info_start = _rom_end - _chip_info_size;

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

#if MSG_FLOW == elf
    .msg_data _msg_mem_start : {
        KEEP(*(.msg_data))
    } > msg_mem
#endif
}
