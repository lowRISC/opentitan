MEMORY
{
  rom   (rx)  : ORIGIN = 0x20000000, LENGTH = 0x40000
  /* Support up to 0x2009_0000 for apps
   * and 0x2009_0000 to 0x2010_0000 is for flash storage.
   */
  prog  (rx)  : ORIGIN = 0x20040000, LENGTH = 0x60000
  ram   (!rx) : ORIGIN = 0x10000000, LENGTH = 0x20000
}

MPU_MIN_ALIGN = 1K;
SECTIONS {
    /*
     * The flash header needs to match what the boot ROM for OpenTitan is
     * expecting.  At the moment, it contains only the entry point, but it
     * will eventually contain the signature -- and (hopefully?!) some
     * versioning information to make it slightly easier to debug when the
     * boot ROM and Tock are out of sync with respect to the definition...
     */
    .flash_header : {
        . = . + 0x37C;
        LONG(_stext - ORIGIN(rom))
        . = . + 0x80;
    } > rom
}

INCLUDE sw/device/silicon_owner/tock/kernel/kernel_layout.ld
