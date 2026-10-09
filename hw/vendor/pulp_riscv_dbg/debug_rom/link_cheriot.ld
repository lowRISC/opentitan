/* See LICENSE.SiFive for license details. */
OUTPUT_ARCH( "riscv" )
ENTRY( entry )

SECTIONS
{
    . = 0x800;
    .text    : { *(.text)    }
    whereto = 0x300;
    _end = .;
}
 
