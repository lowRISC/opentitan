# ROM_EXT end-to-end tests

## ROM_EXT bootstrap

Properties to test:

* ROM_EXT drops down to bootstrap mode iff bootstrap is enabled by OTP (`OWNER_SW_CFG_ROM_EXT_BOOTSTRAP_EN`) and it cannot find a bootable silicon owner image.
  The full truth table:

    | # | Enabled in OTP | Bootable silicon owner image | Expect bootstrap |
    |---|----------------|------------------------------|------------------|
    | 1 | No             | None                         | No               |
    | 2 | No             | Slot A                       | No               |
    | 3 | No             | Slot B                       | No               |
    | 4 | No             | Slot A and B                 | No               |
    | 5 | Yes            | None                         | Yes              |
    | 6 | Yes            | Slot A                       | No               |
    | 7 | Yes            | Slot B                       | No               |
    | 8 | Yes            | Slot A and B                 | No               |

* ROM_EXT bootstrap will not erase the chip until it receives a `CHIP_ERASE` or `SECTOR_ERASE` SPI command.

* ROM_EXT bootstrap will neither erase nor program the ROM_EXT region of slot A.

* ROM_EXT bootstrap will erase and program the owner/BL0 region of slot A.

* ROM_EXT bootstrap will neither erase nor program the ROM_EXT region of slot B.

* ROM_EXT bootstrap will erase, but will not program the owner/BL0 region of slot A.
