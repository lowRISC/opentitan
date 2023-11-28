# SiVal ROM\_EXT

## Lockdowns

The following lockdowns are provided by the SiVal ROM\_EXT.

### AST

TODO: Lockdown the AST.

### ePMP

The ePMP will allow access to the FLASH, to the MMIO region and to SRAM.

An example of how the SiVal ROM\_EXT will configure the ePMP:
```
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
- The OTP direct access interface is not available due to the ePMP lockout of the OTP register region.

### SRAM

SRAM execution is forbidden.
Both the ePMP and SRAM controller will forbid execution from SRAM.

TODO: Re-evaluate this if needed.

### FLASH

The FLASH info pages designeded for `silicon_creator` use will be locked as no-access.

### Key Manager

The key manager will be moved to the final state so that no creator or intermediate stages may be accessed by owner code.

TODO: Currently we stop at OwnerIntermediateKey.
