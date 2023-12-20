# SiVal `ROM_EXT`

## Lockdowns

The following lockdowns are provided by the SiVal `ROM_EXT`.

### AST

Access to the AST configuration registers is disabled by the ePMP
configuration. The manufacturer may also configure the ROM to lockdown AST in
the ROM stage by configuring the AST initialization sequence in OTP.

### ePMP

The ePMP will allow access to the FLASH, to the MMIO region and to SRAM.

An example of how the SiVal `ROM_EXT` will configure the ePMP:

```console
 0: 20010400 ----- ---- sz=00000000     ; OWNER code start.
 1: 20013d24   TOR LX-R sz=00003924     ; OWNER code end.
 2: 00008000 NAPOT L--R sz=00008000     ; OWNER data (if using remap window, else ROM data region)
 3: 20000400 ----- ---- sz=00000000     ; ROM_EXT code start.
 4: 20004fe8   TOR LX-R sz=00004be8     ; ROM_EXT code end.
 5: 20000000 NAPOT L--R sz=00100000     ; FLASH data (1 MB).
 6: 40130000 NAPOT L--- sz=00001000     ; OTP MMIO lockout.
 7: 40480000 NAPOT L--- sz=00000400     ; AST MMIO lockout.
 8: 00000000 ----- ---- sz=00000000
 9: 00000000 ----- ---- sz=00000000
10: 00000000 ----- ---- sz=00000000
11: 40000000 NAPOT L-WR sz=10000000     ; MMIO region.
12: 00000000 ----- ---- sz=00000000
13: 00010000 NAPOT LXWR sz=00001000     ; RvDM region (not PROD, RMA/DEV only).
14: 1001c000   NA4 L--- sz=00000004     ; Stack guard.
15: 10000000 NAPOT L-WR sz=00020000     ; RAM region.
mseccfg = 00000002                      ; RLB=0, MMWP=1, MML=0.
```

### OTP

- The OTP creator partition memory window is locked and is unreadable.
- The OTP owner partition memory window is readable.
- The OTP direct access interface is not available due to the ePMP lockout of
  the OTP register region.

### SRAM

SRAM execution is forbidden to force all PROD SiVal configurations to enforce
signature verification of programs loaded into the flash owner partitions.

Both the ePMP and SRAM controller will forbid execution from SRAM. The SRAM
controller configuration is locked by the `ROM_EXT`.

### FLASH

The FLASH info pages designed for `silicon_creator` use are locked as
no-access.

Page ID                               | Bank | Page
--------------------------------------|------|------
kFlashCtrlInfoPageFactoryId           | 0    | 0
kFlashCtrlInfoPageCreatorSecret       | 0    | 1
kFlashCtrlInfoPageOwnerSecret         | 0    | 2
kFlashCtrlInfoPageWaferAuthSecret     | 0    | 3
kFlashCtrlInfoPageAttestationKeySeeds | 0    | 4
kFlashCtrlInfoPageBootData0           | 1    | 0
kFlashCtrlInfoPageBootData1           | 1    | 1
kFlashCtrlInfoPageOwnerSlot0          | 1    | 2
kFlashCtrlInfoPageOwnerSlot1          | 1    | 3

The canonical info flash reference used by the ROM and the ROM\_EXT is available
in the `sw/device/silicon_creator/lib/drivers/flash_ctrl.h` module.

### Key Manager

The key manager will be moved to the final state so that no creator or
intermediate stages may be accessed by owner code.

The end state of the key manager is `kKeymgrStateOwnerKey` for this
configuration.
