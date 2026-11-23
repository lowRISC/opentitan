# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/sram_ctrl/data/sram_ctrl.hjson -->
## Summary

| Name                                                        | Offset   |   Length | Description                                                              |
|:------------------------------------------------------------|:---------|---------:|:-------------------------------------------------------------------------|
| sram_ctrl.[`ALERT_TEST`](#alert_test)                       | 0x0      |        4 | Alert Test Register                                                      |
| sram_ctrl.[`STATUS`](#status)                               | 0x4      |        4 | SRAM status register.                                                    |
| sram_ctrl.[`EXEC_REGWEN`](#exec_regwen)                     | 0x8      |        4 | Lock register for execution enable register.                             |
| sram_ctrl.[`EXEC`](#exec)                                   | 0xc      |        4 | Sram execution enable.                                                   |
| sram_ctrl.[`CTRL_REGWEN`](#ctrl_regwen)                     | 0x10     |        4 | Lock register for control register.                                      |
| sram_ctrl.[`CTRL`](#ctrl)                                   | 0x14     |        4 | SRAM ctrl register.                                                      |
| sram_ctrl.[`SCR_KEY_ROTATED`](#scr_key_rotated)             | 0x18     |        4 | Clearable SRAM key request status.                                       |
| sram_ctrl.[`READBACK_REGWEN`](#readback_regwen)             | 0x1c     |        4 | Lock register for readback enable register.                              |
| sram_ctrl.[`READBACK`](#readback)                           | 0x20     |        4 | readback enable.                                                         |
| sram_ctrl.[`RMW_INTG_CHECK_REGWEN`](#rmw_intg_check_regwen) | 0x24     |        4 | Lock register for the read-modify-write integrity check enable register. |
| sram_ctrl.[`RMW_INTG_CHECK`](#rmw_intg_check)               | 0x28     |        4 | Read-modify-write integrity check enable.                                |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
- Reset default: `0x80000000`
- Reset mask: `0x80000001`

### Fields

```wavejson
{"reg": [{"name": "fatal_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}, {"name": "regwen", "bits": 1, "attr": ["rw0c"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                            |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------------|
|   31   |  rw0c  |   0x1   | regwen      | Write 0 to disable alert testing until the next reset. |
|  30:1  |        |         |             | Reserved                                               |
|   0    |   wo   |   0x0   | fatal_error | Write 1 to trigger one alert event of this kind.       |

## STATUS
SRAM status register.
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1ff`

### Fields

```wavejson
{"reg": [{"name": "BUS_INTEG_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "INIT_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ESCALATED", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SCR_KEY_VALID", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SCR_KEY_SEED_VALID", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "INIT_DONE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "READBACK_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SRAM_ALERT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RMW_INTG_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
|  31:9  |        |         | Reserved                                          |
|   8    |   ro   |   0x0   | [RMW_INTG_ERROR](#status--rmw_intg_error)         |
|   7    |   ro   |   0x0   | [SRAM_ALERT](#status--sram_alert)                 |
|   6    |   ro   |   0x0   | [READBACK_ERROR](#status--readback_error)         |
|   5    |   ro   |   0x0   | [INIT_DONE](#status--init_done)                   |
|   4    |   ro   |   0x0   | [SCR_KEY_SEED_VALID](#status--scr_key_seed_valid) |
|   3    |   ro   |   0x0   | [SCR_KEY_VALID](#status--scr_key_valid)           |
|   2    |   ro   |   0x0   | [ESCALATED](#status--escalated)                   |
|   1    |   ro   |   0x0   | [INIT_ERROR](#status--init_error)                 |
|   0    |   ro   |   0x0   | [BUS_INTEG_ERROR](#status--bus_integ_error)       |

### STATUS . RMW_INTG_ERROR
This bit is set to 1 if the integrity check of the read data in a
read-modify-write transaction failed (see [`RMW_INTG_CHECK`](#rmw_intg_check)).
This error triggers a fatal_error alert.
This condition is terminal.

### STATUS . SRAM_ALERT
This bit is set to 1 if a multi bit encoding error has been detected inside the RAM modules.
This error triggers a fatal_error alert.
This condition is terminal.

### STATUS . READBACK_ERROR
This bit is set to 1 if a SRAM readback check failed.
This error triggers a fatal_error alert.
This condition is terminal.

### STATUS . INIT_DONE
Set to 1 if the hardware initialization triggered via [`CTRL.INIT`](#ctrl) has completed.

### STATUS . SCR_KEY_SEED_VALID
Set to 1 if the scrambling key has been derived from a valid key seed in OTP.
If [`STATUS.SCR_KEY_VALID`](#status) is set to 1, [`STATUS.SCR_KEY_SEED_VALID`](#status) should be 1
except for cases where the scrambling key seeds have not yet been provisioned to
OTP. In such a case, the scrambling key is still ephemeral (i.e., it is derived
using entropy from CSRNG), but a default all-zero value is used as the key seed.

### STATUS . SCR_KEY_VALID
Set to 1 if a new scrambling key has been successfully obtained from OTP.
Note that if this is set to 0, the SRAM contents are still scrambled, but a
default all-zero key and nonce are used to do so.

### STATUS . ESCALATED
Set to 1 if the sram controller has received an escalate request.
If this is set to 1, the scrambling keys have been reset to the default values
and all subsequent memory requests will be blocked.
This condition is terminal.

### STATUS . INIT_ERROR
This bit is set to 1 if a the initialization counter has reached an invalid state.
This error triggers a fatal_error alert.
This condition is terminal.

### STATUS . BUS_INTEG_ERROR
This bit is set to 1 if a fatal bus integrity fault is detected.
This error triggers a fatal_error alert.
This condition is terminal.

## EXEC_REGWEN
Lock register for execution enable register.
- Offset: `0x8`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "EXEC_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                       |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------------|
|  31:1  |        |         |             | Reserved                                                          |
|   0    |  rw0c  |   0x1   | EXEC_REGWEN | When cleared to zero, [`EXEC`](#exec) can not be written anymore. |

## EXEC
Sram execution enable.
- Offset: `0xc`
- Reset default: `0x9`
- Reset mask: `0xf`
- Register enable: [`EXEC_REGWEN`](#exec_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name            |
|:------:|:------:|:-------:|:----------------|
|  31:4  |        |         | Reserved        |
|  3:0   |   rw   |   0x9   | [EN](#exec--en) |

### EXEC . EN
This register only has any effect if the value of the incoming
otp_en_sram_ifetch_i signal is set to kMultiBitBool8True (in
Earlgrey, this comes from the OTP HW_CFG1 partition).

If so, execution from SRAM requires this register to contain
kMultiBitBool4True.

If otp_en_sram_ifetch_i is not kMultiBitBool8True, execution
from SRAM is instead controlled by a signal from lc_ctrl. See
"Theory of Operation" for more details.

## CTRL_REGWEN
Lock register for control register.
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "CTRL_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                       |
|:------:|:------:|:-------:|:------------|:------------------------------------------------------------------|
|  31:1  |        |         |             | Reserved                                                          |
|   0    |  rw0c  |   0x1   | CTRL_REGWEN | When cleared to zero, [`CTRL`](#ctrl) can not be written anymore. |

## CTRL
SRAM ctrl register.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x3`
- Register enable: [`CTRL_REGWEN`](#ctrl_regwen)

### Fields

```wavejson
{"reg": [{"name": "RENEW_SCR_KEY", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "INIT", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                  |
|:------:|:------:|:-------:|:--------------------------------------|
|  31:2  |        |         | Reserved                              |
|   1    |   wo   |   0x0   | [INIT](#ctrl--init)                   |
|   0    |   wo   |   0x0   | [RENEW_SCR_KEY](#ctrl--renew_scr_key) |

### CTRL . INIT
Write 1 to request memory init.
The init mechanism uses an LFSR that is seeded with a part of the nonce supplied when requesting a scrambling key.
Once seeded, the memory is initialized with pseudo-random data pulled from the LFSR.
Note that [`CTRL.RENEW_SCR_KEY`](#ctrl) takes priority when writing 1 to both [`CTRL.RENEW_SCR_KEY`](#ctrl) and [`CTRL.INIT`](#ctrl) with the same write transaction.
This means that the key request will complete first, followed by SRAM initialization. Note that writing 1 to this register while
an init request is already pending has no effect.

### CTRL . RENEW_SCR_KEY
Write 1 to request a new scrambling key from OTP. After writing to this register, SRAM transactions will
be blocked until [`STATUS.SCR_KEY_VALID`](#status) has been set to 1. If [`STATUS.SCR_KEY_VALID`](#status) was already 1
before triggering a key renewal, hardware will automatically clear that status bit such that software
can poll its status. Note that requesting a new scrambling key takes ~200 OTP cycles, which translates
to ~800 CPU cycles (OTP runs at 24MHz, CPU runs at 100MHz). Note that writing 1 to this register while
a key request or a memory initialization request is already pending has no effect.

## SCR_KEY_ROTATED
Clearable SRAM key request status.
- Offset: `0x18`
- Reset default: `0x9`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "SUCCESS", "bits": 4, "attr": ["rw1c"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
|  31:4  |        |         | Reserved                             |
|  3:0   |  rw1c  |   0x9   | [SUCCESS](#scr_key_rotated--success) |

### SCR_KEY_ROTATED . SUCCESS
This status register is similar to [`SCR_KEY_VALID`](#scr_key_valid) with the difference that the status is multibit encoded,
SW clearable and sticky (i.e., HW does not auto-clear the register except during escalation). That way,
SW can use this for a hardened acknowledgement mechanism where it clears the register before requesting a key.

kMultiBitBool4True indicates that a valid scrambling key has been obtained from OTP.
Write kMultiBitBool4True to clear.

## READBACK_REGWEN
Lock register for readback enable register.
- Offset: `0x1c`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "READBACK_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                               |
|:------:|:------:|:-------:|:----------------|:--------------------------------------------------------------------------|
|  31:1  |        |         |                 | Reserved                                                                  |
|   0    |  rw0c  |   0x1   | READBACK_REGWEN | When cleared to zero, [`READBACK`](#readback) can not be written anymore. |

## READBACK
readback enable.
- Offset: `0x20`
- Reset default: `0x9`
- Reset mask: `0xf`
- Register enable: [`READBACK_REGWEN`](#readback_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                |
|:------:|:------:|:-------:|:--------------------|
|  31:4  |        |         | Reserved            |
|  3:0   |   rw   |   0x9   | [EN](#readback--en) |

### READBACK . EN
Write kMultiBitBool4True to this field to enable the readback security feature for the SRAM.
A readback of each memory write or read request will be performed and a comparison happens.
Any other value than kMultiBitBool4False written to this field is interpreted as kMultiBitBool4True.

## RMW_INTG_CHECK_REGWEN
Lock register for the read-modify-write integrity check enable register.
- Offset: `0x24`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "RMW_INTG_CHECK_REGWEN", "bits": 1, "attr": ["rw0c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                           |
|:------:|:------:|:-------:|:----------------------|:--------------------------------------------------------------------------------------|
|  31:1  |        |         |                       | Reserved                                                                              |
|   0    |  rw0c  |   0x1   | RMW_INTG_CHECK_REGWEN | When cleared to zero, [`RMW_INTG_CHECK`](#rmw_intg_check) can not be written anymore. |

## RMW_INTG_CHECK
Read-modify-write integrity check enable.
- Offset: `0x28`
- Reset default: `0x9`
- Reset mask: `0xf`
- Register enable: [`RMW_INTG_CHECK_REGWEN`](#rmw_intg_check_regwen)

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                      |
|:------:|:------:|:-------:|:--------------------------|
|  31:4  |        |         | Reserved                  |
|  3:0   |   rw   |   0x9   | [EN](#rmw_intg_check--en) |

### RMW_INTG_CHECK . EN
Write kMultiBitBool4True to this field to enable the integrity check of the data
read from the SRAM during a read-modify-write transaction (i.e., a sub-word write).
If the check fails, the write is not performed, [`STATUS.RMW_INTG_ERROR`](#status) is set and
a fatal_error alert is triggered.

This check is disabled by default, as a sub-word write to a memory location that
has not been initialized would otherwise trigger an integrity error.
Software should only enable this check once the SRAM has been fully initialized
(e.g., via [`CTRL.INIT`](#ctrl)) and should then lock it using [`RMW_INTG_CHECK_REGWEN.`](#rmw_intg_check_regwen)

Any other value than kMultiBitBool4False written to this field is interpreted as kMultiBitBool4True.


<!-- END CMDGEN -->
