/* Layout for the RISC-V 32 boards, used by the examples in this repository. */

MEMORY {
  /* Note that the SRAM address may need to be changed depending on
   * the kernel binary, check for the actual address of APP_MEMORY!
   */
  FLASH (X) : ORIGIN = 0x20040000, LENGTH = 32M
  RAM   (W) : ORIGIN = 0x10004400, LENGTH = 512K
}

TBF_HEADER_SIZE = 0x40;
INCLUDE sw/device/silicon_owner/tock/apps/hello/libtock_layout.ld
