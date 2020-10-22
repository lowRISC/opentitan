| Index | Partition                       | Size [B]    | Access Granule | Item                                     | Byte Address | Size [B]
|-------|---------------------------------|-------------|----------------|------------------------------------------|--------------|------------
| 0     | {{< regref "CREATOR_SW_CFG" >}} | 768         | 32bit          | {{< regref "CREATOR_SW_CFG" >}}          | 0x0          | 760
|       |                                 |             |                | {{< regref "CREATOR_SW_CFG_DIGEST_0" >}} | 0x2F8        | 8
| 1     | {{< regref "OWNER_SW_CFG" >}}   | 768         | 32bit          | {{< regref "OWNER_SW_CFG" >}}            | 0x300        | 760
|       |                                 |             |                | {{< regref "OWNER_SW_CFG_DIGEST_0" >}}   | 0x5F8        | 8
| 2     | HW_CFG                          | 176         | 32bit          | **TODO: TBD**                            | 0x600        | 168
|       |                                 |             |                | {{< regref "HW_CFG_DIGEST_0" >}}         | 0x6A8        | 8
| 3     | SECRET0                         | 40          | 64bit          | TEST_UNLOCK_TOKEN                        | 0x6B0        | 16
|       |                                 |             |                | TEST_EXIT_TOKEN                          | 0x6C0        | 16
|       |                                 |             |                | {{< regref "SECRET0_DIGEST_0" >}}        | 0x6D0        | 8
| 4     | SECRET1                         | 88          | 64bit          | FLASH_ADDR_KEY_SEED                      | 0x6D8        | 32
|       |                                 |             |                | FLASH_DATA_KEY_SEED                      | 0x6F8        | 32
|       |                                 |             |                | SRAM_DATA_KEY_SEED                       | 0x718        | 16
|       |                                 |             |                | {{< regref "SECRET1_DIGEST_0" >}}        | 0x728        | 8
| 5     | SECRET2                         | 120         | 64bit          | RMA_TOKEN                                | 0x730        | 16
|       |                                 |             |                | CREATOR_ROOT_KEY_SHARE0                  | 0x740        | 32
|       |                                 |             |                | CREATOR_ROOT_KEY_SHARE1                  | 0x760        | 32
|       |                                 |             |                | {{< regref "SECRET2_DIGEST_0" >}}        | 0x7A0        | 8
| 6     | LIFE_CYCLE                      | 88          | 32bit          | LC_STATE                                 | 0x7A8        | 24
|       |                                 |             |                | LC_TRANSITION_CNT                        | 0x7C0        | 64
