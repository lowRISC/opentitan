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
 0: 40130000 NAPOT L--- sz=00001000     ; OTP MMIO lockout.
 1: 40480000 NAPOT L--- sz=00000400     ; AST MMIO lockout.
 2: 20010400 ----- ---- sz=00000000     ; OWNER code start.
 3: 20013cac   TOR -X-R sz=000038ac     ; OWNER code end.
 4: 00000000 ----- ---- sz=00000000     ; OWNER data (if using remap window, else unused).
 5: 00000000 ----- ---- sz=00000000
 6: 00000000 ----- ---- sz=00000000
 7: 00000000 ----- ---- sz=00000000
 8: 00000000 ----- ---- sz=00000000
 9: 00000000 ----- ---- sz=00000000
10: 20000400 ----- ---- sz=00000000     ; ROM_EXT code start.
11: 20005bc8   TOR -X-R sz=000057c8     ; ROM_EXT code end.
12: 20000000 NAPOT ---R sz=00100000     ; FLASH data (1 MB).
13: 00010000 NAPOT -XWR sz=00001000     ; RvDM region (not PROD, RMA/DEV only).
14: 40000000 NAPOT --WR sz=10000000     ; MMIO region.
15: 10000000 NAPOT --WR sz=00020000     ; RAM region.
mseccfg = 00000002                      ; RLB=0, MMWP=1, MML=0.
```

In this configuration, the owner stage can re-arrange ePMP entries
2-11 as needed.  Applications that require machine/user mode isolation can set
the MML bit after arranging the ePMP to the preferred configuration.

NOTE: if the ROM\_EXT stage is booted in the virtual slot, then ePMP entries
9/10/11 will be used to map the virtual window's code/data segments.  Since
these entries are unlocked _and_ since the ROM\_EXT is no longer requred
after owner code boots, these entries can be reclaimed for owner use.

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

The end state of the key manager is `kScKeymgrStateOwnerKey` for this
configuration.
