# Registers

The revocation bitmap is not a register but a memory window on the `revbm` interface; see the
[Theory of Operation](theory_of_operation.md#meta-sram-address-map).

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/cheriot_mem_sys/data/cheriot_mem_sys.hjson -->
## Summary

| Name                                                | Offset   |   Length | Description                                                                                                              |
|:----------------------------------------------------|:---------|---------:|:-------------------------------------------------------------------------------------------------------------------------|
| cheriot_mem_sys.[`INTR_STATE`](#intr_state)         | 0x0      |        4 | Interrupt State Register                                                                                                 |
| cheriot_mem_sys.[`INTR_ENABLE`](#intr_enable)       | 0x4      |        4 | Interrupt Enable Register                                                                                                |
| cheriot_mem_sys.[`INTR_TEST`](#intr_test)           | 0x8      |        4 | Interrupt Test Register                                                                                                  |
| cheriot_mem_sys.[`ALERT_TEST`](#alert_test)         | 0xc      |        4 | Alert Test Register                                                                                                      |
| cheriot_mem_sys.[`TBRE_REGWEN`](#tbre_regwen)       | 0x10     |        4 | Write enable for the revocation engine registers.                                                                        |
| cheriot_mem_sys.[`TBRE_BASE_ADDR`](#tbre_base_addr) | 0x14     |        4 | Address of the first capability the revocation engine sweeps.                                                            |
| cheriot_mem_sys.[`TBRE_NUM_CAPS`](#tbre_num_caps)   | 0x18     |        4 | Number of capabilities the revocation engine sweeps, each of them two 32-bit words.                                      |
| cheriot_mem_sys.[`TBRE_START`](#tbre_start)         | 0x1c     |        4 | Starts a sweep over the capabilities [`TBRE_BASE_ADDR`](#tbre_base_addr) and [`TBRE_NUM_CAPS`](#tbre_num_caps) describe. |
| cheriot_mem_sys.[`TBRE_STATUS`](#tbre_status)       | 0x20     |        4 | Status of the revocation engine.                                                                                         |
| cheriot_mem_sys.[`TBRE_EPOCH`](#tbre_epoch)         | 0x24     |        4 | Sweep epoch, twice the number of sweeps that ended without an error, plus one while the                                  |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "tbre_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                 |
|:------:|:------:|:-------:|:----------|:----------------------------------------------------------------------------|
|  31:1  |        |         |           | Reserved                                                                    |
|   0    |  rw1c  |   0x0   | tbre_done | Raised when the revocation engine has resolved every capability of a sweep. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "tbre_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                         |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------------|
|  31:1  |        |         |           | Reserved                                                            |
|   0    |   rw   |   0x0   | tbre_done | Enable interrupt when [`INTR_STATE.tbre_done`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "tbre_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                  |
|:------:|:------:|:-------:|:----------|:-------------------------------------------------------------|
|  31:1  |        |         |           | Reserved                                                     |
|   0    |   wo   |   0x0   | tbre_done | Write 1 to force [`INTR_STATE.tbre_done`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x80000000`
- Reset mask: `0x80000001`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}, {"name": "regwen", "bits": 1, "attr": ["rw0c"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                            |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------------|
|   31   |  rw0c  |   0x1   | regwen      | Write 0 to disable alert testing until the next reset. |
|  30:1  |        |         |             | Reserved                                               |
|   0    |   wo   |   0x0   | fatal_fault | Write 1 to trigger one alert event of this kind.       |

## TBRE_REGWEN
Write enable for the revocation engine registers.
- Offset: `0x10`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "en", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                           |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                                                                                              |
|   0    |   ro   |   0x1   | en     | Low while the revocation engine is active, locking [`TBRE_BASE_ADDR`](#tbre_base_addr), [`TBRE_NUM_CAPS`](#tbre_num_caps) and [`TBRE_START.`](#tbre_start) [`TBRE_STATUS.busy`](#tbre_status) follows the same state one cycle later. |

## TBRE_BASE_ADDR
Address of the first capability the revocation engine sweeps.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xfffffff8`
- Register enable: [`TBRE_REGWEN`](#tbre_regwen)

### Fields

```wavejson
{"reg": [{"bits": 3}, {"name": "addr", "bits": 29, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                               |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:3  |   rw   |   0x0   | addr   | Bits 31:3 of the address. The sweep starts at a capability boundary; bits 2:0 read as zero. The address must lie in a tagged region, the main SRAM or the NVM; the sweep stops at the top of that region. |
|  2:0   |        |         |        | Reserved                                                                                                                                                                                                  |

## TBRE_NUM_CAPS
Number of capabilities the revocation engine sweeps, each of them two 32-bit words.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0x7fffffff`
- Register enable: [`TBRE_REGWEN`](#tbre_regwen)

### Fields

```wavejson
{"reg": [{"name": "num", "bits": 31, "attr": ["rw"], "rotate": 0}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                       |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------|
|   31   |        |         |        | Reserved                                                                                                                          |
|  30:0  |   rw   |   0x0   | num    | Number of capabilities. A sweep reaching past the top of its tagged region ends at its top; the register keeps the value written. |

## TBRE_START
Starts a sweep over the capabilities [`TBRE_BASE_ADDR`](#tbre_base_addr) and [`TBRE_NUM_CAPS`](#tbre_num_caps) describe.
[`TBRE_STATUS.busy`](#tbre_status) reflects the sweep in progress. A start outside CHERIoT mode, with
[`TBRE_NUM_CAPS`](#tbre_num_caps) zero, or with [`TBRE_BASE_ADDR`](#tbre_base_addr) outside the tagged regions, is ignored and
sets [`TBRE_STATUS.start_err.`](#tbre_status)
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`TBRE_REGWEN`](#tbre_regwen)

### Fields

```wavejson
{"reg": [{"name": "start", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description               |
|:------:|:------:|:-------:|:-------|:--------------------------|
|  31:1  |        |         |        | Reserved                  |
|   0    |   wo   |   0x0   | start  | Write 1 to start a sweep. |

## TBRE_STATUS
Status of the revocation engine.
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x301`

### Fields

```wavejson
{"reg": [{"name": "busy", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 7}, {"name": "start_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sweep_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
| 31:10  |        |         | Reserved                             |
|   9    |  rw1c  |   0x0   | [sweep_err](#tbre_status--sweep_err) |
|   8    |  rw1c  |   0x0   | [start_err](#tbre_status--start_err) |
|  7:1   |        |         | Reserved                             |
|   0    |   ro   |   0x0   | [busy](#tbre_status--busy)           |

### TBRE_STATUS . sweep_err
A response to the revocation engine was an error, failed its integrity check or was
malformed, or the RMW filter reported a fault, during a sweep. Except for an error
response to a read of the swept memory, the fatal_fault alert is raised as well. Stays
set until software writes 1 to it.

### TBRE_STATUS . start_err
A start was ignored because the subsystem was not in CHERIoT mode, [`TBRE_NUM_CAPS`](#tbre_num_caps) was
zero or [`TBRE_BASE_ADDR`](#tbre_base_addr) was outside the tagged regions. Stays set until software
writes 1 to it.

### TBRE_STATUS . busy
The revocation engine is sweeping; it is low once every capability of the sweep is
resolved.

## TBRE_EPOCH
Sweep epoch, twice the number of sweeps that ended without an error, plus one while the
revocation engine is active. It is odd from the cycle a start is taken, when [`TBRE_REGWEN`](#tbre_regwen)
falls, until the engine is inactive again, and even otherwise. A sweep that ends with an
error (see [`TBRE_STATUS.sweep_err`](#tbre_status)) is not counted, so the epoch returns to the even value
it had before that start, and no software waiting for a completed sweep proceeds on it.
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "active", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "count", "bits": 31, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                             |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------|
|  31:1  |   ro   |   0x0   | count  | Sweeps that ended without an error, modulo 2^31; a sweep counts in the cycle [`TBRE_EPOCH.active`](#tbre_epoch) clears. |
|   0    |   ro   |   0x0   | active | The revocation engine is active; the inverse of [`TBRE_REGWEN.`](#tbre_regwen)                                          |


<!-- END CMDGEN -->
