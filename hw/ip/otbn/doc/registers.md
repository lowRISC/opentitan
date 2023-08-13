# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/otbn/data/otbn.hjson -->
## Summary

| Name                                           | Offset   |   Length | Description                                     |
|:-----------------------------------------------|:---------|---------:|:------------------------------------------------|
| otbn.[`INTR_STATE`](#intr_state)               | 0x0      |        4 | Interrupt State Register                        |
| otbn.[`INTR_ENABLE`](#intr_enable)             | 0x4      |        4 | Interrupt Enable Register                       |
| otbn.[`INTR_TEST`](#intr_test)                 | 0x8      |        4 | Interrupt Test Register                         |
| otbn.[`ALERT_TEST`](#alert_test)               | 0xc      |        4 | Alert Test Register                             |
| otbn.[`CMD`](#cmd)                             | 0x10     |        4 | Command Register                                |
| otbn.[`CTRL`](#ctrl)                           | 0x14     |        4 | Control Register                                |
| otbn.[`STATUS`](#status)                       | 0x18     |        4 | Status Register                                 |
| otbn.[`ERR_BITS`](#err_bits)                   | 0x1c     |        4 | Operation Result Register                       |
| otbn.[`FATAL_ALERT_CAUSE`](#fatal_alert_cause) | 0x20     |        4 | Fatal Alert Cause Register                      |
| otbn.[`INSN_CNT`](#insn_cnt)                   | 0x24     |        4 | Instruction Count Register                      |
| otbn.[`LOAD_CHECKSUM`](#load_checksum)         | 0x28     |        4 | A 32-bit CRC checksum of data written to memory |
| otbn.[`IMEM`](#imem)                           | 0x4000   |     4096 | Instruction Memory Access                       |
| otbn.[`DMEM`](#dmem)                           | 0x8000   |     3072 | Data Memory Access                              |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                       |
|:------:|:------:|:-------:|:-------|:----------------------------------|
|  31:1  |        |         |        | Reserved                          |
|   0    |  rw1c  |   0x0   | done   | OTBN has completed the operation. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                    |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                       |
|   0    |   rw   |   0x0   | done   | Enable interrupt when [`INTR_STATE.done`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                             |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                |
|   0    |   wo   |   0x0   | done   | Write 1 to force [`INTR_STATE.done`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "fatal", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "recov", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:2  |        |         |        | Reserved                                         |
|   1    |   wo   |   0x0   | recov  | Write 1 to trigger one alert event of this kind. |
|   0    |   wo   |   0x0   | fatal  | Write 1 to trigger one alert event of this kind. |

## CMD
Command Register

A command initiates an OTBN operation. While performing the operation,
OTBN is busy; the [`STATUS`](#status) register reflects that.

All operations signal their completion by raising the done
interrupt; alternatively, software may poll the [`STATUS`](#status) register.

Writes are ignored if OTBN is not idle.
Unrecognized commands are ignored.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "cmd", "bits": 8, "attr": ["wo"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name             |
|:------:|:------:|:-------:|:-----------------|
|  31:8  |        |         | Reserved         |
|  7:0   |   wo   |   0x0   | [cmd](#cmd--cmd) |

### CMD . cmd
The operation to perform.

| Value | Name          | Description |
|:------|:--------------|:------------|
| 0xd8  | EXECUTE       | Starts the execution of the program stored in the instruction memory, starting at address zero. |
| 0xc3  | SEC_WIPE_DMEM | Securely removes all contents from the data memory. |
| 0x1e  | SEC_WIPE_IMEM | Securely removes all contents from the instruction  memory. |

## CTRL
Control Register
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "software_errs_fatal", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                                                                                                                                        |
|:------:|:------:|:-------:|:--------------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |                     | Reserved                                                                                                                                                           |
|   0    |   rw   |   0x0   | software_errs_fatal | Controls the reaction to software errors.  When set software errors produce fatal errors, rather than recoverable errors.  Writes are ignored if OTBN is not idle. |

## STATUS
Status Register
- Offset: `0x18`
- Reset default: `0x4`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "status", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                      |
|:------:|:------:|:-------:|:--------------------------|
|  31:8  |        |         | Reserved                  |
|  7:0   |   ro   |   0x4   | [status](#status--status) |

### STATUS . status
Indicates the current operational state OTBN is in.

All BUSY values represent an operation started by a write to the
[`CMD`](#cmd) register.

| Value | Name               | Description                                           |
|:------|:-------------------|:------------------------------------------------------|
| 0x00  | IDLE               | OTBN is idle: it is not performing any action.        |
| 0x01  | BUSY_EXECUTE       | OTBN is busy executing software.                      |
| 0x02  | BUSY_SEC_WIPE_DMEM | OTBN is busy securely wiping the data memory.         |
| 0x03  | BUSY_SEC_WIPE_IMEM | OTBN is busy securely wiping the instruction memory.  |
| 0x04  | BUSY_SEC_WIPE_INT  | OTBN is busy securely wiping the internal state.      |
| 0xFF  | LOCKED             | OTBN is locked as reaction to a fatal error, and must be reset to unlock it again. See also the section "Reaction to Fatal Errors". |


## ERR_BITS
Operation Result Register

Describes the errors detected during an operation.

Refer to the "List of Errors" section for a detailed description of the
errors.

The host CPU can clear this register when OTBN is not running,
by writing any value. Write attempts while OTBN is running are ignored.
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xff00ff`

### Fields

```wavejson
{"reg": [{"name": "bad_data_addr", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "bad_insn_addr", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "call_stack", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "illegal_insn", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "loop", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "key_invalid", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rnd_rep_chk_fail", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "rnd_fips_chk_fail", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 8}, {"name": "imem_intg_violation", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "dmem_intg_violation", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "reg_intg_violation", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "bus_intg_violation", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "bad_internal_state", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "illegal_bus_access", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "lifecycle_escalation", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "fatal_software", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                  |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------|
| 31:24  |        |         |                      | Reserved                                     |
|   23   |   rw   |   0x0   | fatal_software       | A `FATAL_SOFTWARE` error was observed.       |
|   22   |   rw   |   0x0   | lifecycle_escalation | A `LIFECYCLE_ESCALATION` error was observed. |
|   21   |   rw   |   0x0   | illegal_bus_access   | An `ILLEGAL_BUS_ACCESS` error was observed.  |
|   20   |   rw   |   0x0   | bad_internal_state   | A `BAD_INTERNAL_STATE` error was observed.   |
|   19   |   rw   |   0x0   | bus_intg_violation   | A `BUS_INTG_VIOLATION` error was observed.   |
|   18   |   rw   |   0x0   | reg_intg_violation   | A `REG_INTG_VIOLATION` error was observed.   |
|   17   |   rw   |   0x0   | dmem_intg_violation  | A `DMEM_INTG_VIOLATION` error was observed.  |
|   16   |   rw   |   0x0   | imem_intg_violation  | A `IMEM_INTG_VIOLATION` error was observed.  |
|  15:8  |        |         |                      | Reserved                                     |
|   7    |   rw   |   0x0   | rnd_fips_chk_fail    | An `RND_FIPS_CHK_FAIL` error was observed.   |
|   6    |   rw   |   0x0   | rnd_rep_chk_fail     | An `RND_REP_CHK_FAIL` error was observed.    |
|   5    |   rw   |   0x0   | key_invalid          | A `KEY_INVALID` error was observed.          |
|   4    |   rw   |   0x0   | loop                 | A `LOOP` error was observed.                 |
|   3    |   rw   |   0x0   | illegal_insn         | An `ILLEGAL_INSN` error was observed.        |
|   2    |   rw   |   0x0   | call_stack           | A `CALL_STACK` error was observed.           |
|   1    |   rw   |   0x0   | bad_insn_addr        | A `BAD_INSN_ADDR` error was observed.        |
|   0    |   rw   |   0x0   | bad_data_addr        | A `BAD_DATA_ADDR` error was observed.        |

## FATAL_ALERT_CAUSE
Fatal Alert Cause Register

Describes any errors that led to a fatal alert.
A fatal error puts OTBN in locked state; the value of this register
does not change until OTBN is reset.

Refer to the "List of Errors" section for a detailed description of the
errors.
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "imem_intg_violation", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "dmem_intg_violation", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "reg_intg_violation", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "bus_intg_violation", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "bad_internal_state", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "illegal_bus_access", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "lifecycle_escalation", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "fatal_software", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                  |
|:------:|:------:|:-------:|:---------------------|:---------------------------------------------|
|  31:8  |        |         |                      | Reserved                                     |
|   7    |   ro   |   0x0   | fatal_software       | A `FATAL_SOFTWARE` error was observed.       |
|   6    |   ro   |   0x0   | lifecycle_escalation | A `LIFECYCLE_ESCALATION` error was observed. |
|   5    |   ro   |   0x0   | illegal_bus_access   | A `ILLEGAL_BUS_ACCESS` error was observed.   |
|   4    |   ro   |   0x0   | bad_internal_state   | A `BAD_INTERNAL_STATE` error was observed.   |
|   3    |   ro   |   0x0   | bus_intg_violation   | A `BUS_INTG_VIOLATION` error was observed.   |
|   2    |   ro   |   0x0   | reg_intg_violation   | A `REG_INTG_VIOLATION` error was observed.   |
|   1    |   ro   |   0x0   | dmem_intg_violation  | A `DMEM_INTG_VIOLATION` error was observed.  |
|   0    |   ro   |   0x0   | imem_intg_violation  | A `IMEM_INTG_VIOLATION` error was observed.  |

## INSN_CNT
Instruction Count Register

Returns the number of instructions executed in the current or last
operation. The counter saturates at 2^32-1 and is reset to 0 at the
start of a new operation.

Only the EXECUTE operation counts instructions; for all other operations
this register remains at 0. Instructions triggering an error do not
count towards the total.

Always reads as 0 if OTBN is locked.

The host CPU can clear this register when OTBN is not running,
by writing any value. Write attempts while OTBN is running are ignored.
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "insn_cnt", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                          |
|:------:|:------:|:-------:|:---------|:-------------------------------------|
|  31:0  |   rw   |   0x0   | insn_cnt | The number of executed instructions. |

## LOAD_CHECKSUM
A 32-bit CRC checksum of data written to memory

See the "Memory Load Integrity" section of the manual for full details.
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "checksum", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description          |
|:------:|:------:|:-------:|:---------|:---------------------|
|  31:0  |   rw   |   0x0   | checksum | Checksum accumulator |

## IMEM
Instruction Memory Access

The instruction memory may only be accessed through this window
while OTBN is idle.

If OTBN is busy or locked, read accesses return 0 and write accesses
are ignored.
If OTBN is busy, any access additionally triggers an
ILLEGAL_BUS_ACCESS fatal error.

- Word Aligned Offset Range: `0x4000`to`0x4ffc`
- Size (words): `1024`
- Access: `rw`
- Byte writes are *not* supported.

## DMEM
Data Memory Access

The data memory may only be accessed through this window while OTBN
is idle.

If OTBN is busy or locked, read accesses return 0 and write accesses
are ignored.
If OTBN is busy, any access additionally triggers an
ILLEGAL_BUS_ACCESS fatal error.

Note that DMEM is actually 4kiB in size, but only the first 3kiB of
the memory is visible through this register interface.

- Word Aligned Offset Range: `0x8000`to`0x8bfc`
- Size (words): `768`
- Access: `rw`
- Byte writes are *not* supported.


<!-- END CMDGEN -->
