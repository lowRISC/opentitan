Partititon     | Secret | Buffered | WR Lockable  | RD Lockable  | Description
---------------|--------|----------|--------------|--------------|----------------------------------------------------------------
CREATOR_SW_CFG | no     | no       | yes (digest) |   yes (CSR)  | Software configuration partition for device-specific calibration data (Clock, LDO, RNG, device identity).
OWNER_SW_CFG   | no     | no       | yes (digest) |   yes (CSR)  | Software configuration partition for data that changes software behavior, specifically in the ROM. <br> E.g., enabling defensive features in ROM or selecting failure modes if verification fails.
HW_CFG         | no     | yes      | yes (digest) |      no      | Hardware configuration bits used to hardwire specific hardware functionality. <br> E.g., raw entropy accessibility or FLASH scrambling bypass range.
SECRET0        | yes    | yes      | yes (digest) | yes (digest) | Test unlock tokens.
SECRET1        | yes    | yes      | yes (digest) | yes (digest) | SRAM and FLASH scrambling key roots used for scrambling key derivation.
SECRET2        | yes    | yes      | yes (digest) | yes (digest) | RMA unlock token and creator root key.
LIFE_CYCLE     | no     | yes      |     no       |      no      | [Life-cycle]({{< relref "hw/ip/lc_ctrl/doc" >}}) related bits. **Note**, this partition cannot be locked as the life cycle state needs to be able to advance to RMA in-field.
