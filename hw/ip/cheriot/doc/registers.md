# Registers

The revocation bitmap is not a register but a memory window on the `revbm` interface; see the
[Theory of Operation](theory_of_operation.md#meta-sram-address-map).

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/cheriot/data/cheriot.hjson -->
## Summary

| Name                                        | Offset   |   Length | Description                                                                                                              |
|:--------------------------------------------|:---------|---------:|:-------------------------------------------------------------------------------------------------------------------------|
| cheriot.[`INTR_STATE`](#intr_state)         | 0x0      |        4 | Interrupt State Register                                                                                                 |
| cheriot.[`INTR_ENABLE`](#intr_enable)       | 0x4      |        4 | Interrupt Enable Register                                                                                                |
| cheriot.[`INTR_TEST`](#intr_test)           | 0x8      |        4 | Interrupt Test Register                                                                                                  |
| cheriot.[`ALERT_TEST`](#alert_test)         | 0xc      |        4 | Alert Test Register                                                                                                      |
| cheriot.[`TRBE_REGWEN`](#trbe_regwen)       | 0x10     |        4 | Write enable for the revocation engine registers.                                                                        |
| cheriot.[`TRBE_BASE_ADDR`](#trbe_base_addr) | 0x14     |        4 | Address of the first capability the revocation engine sweeps.                                                            |
| cheriot.[`TRBE_NUM_CAPS`](#trbe_num_caps)   | 0x18     |        4 | Number of capabilities the revocation engine sweeps, each of them two 32-bit words.                                      |
| cheriot.[`TRBE_START`](#trbe_start)         | 0x1c     |        4 | Starts a sweep over the capabilities [`TRBE_BASE_ADDR`](#trbe_base_addr) and [`TRBE_NUM_CAPS`](#trbe_num_caps) describe. |
| cheriot.[`TRBE_STATUS`](#trbe_status)       | 0x20     |        4 | Status of the revocation engine.                                                                                         |
| cheriot.[`TRBE_EPOCH`](#trbe_epoch)         | 0x24     |        4 | Sweep epoch, twice the number of sweeps that ended without an error, plus one while the                                  |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "trbe_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                 |
|:------:|:------:|:-------:|:----------|:----------------------------------------------------------------------------|
|  31:1  |        |         |           | Reserved                                                                    |
|   0    |  rw1c  |   0x0   | trbe_done | Raised when the revocation engine has resolved every capability of a sweep. |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "trbe_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                         |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------------|
|  31:1  |        |         |           | Reserved                                                            |
|   0    |   rw   |   0x0   | trbe_done | Enable interrupt when [`INTR_STATE.trbe_done`](#intr_state) is set. |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "trbe_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                  |
|:------:|:------:|:-------:|:----------|:-------------------------------------------------------------|
|  31:1  |        |         |           | Reserved                                                     |
|   0    |   wo   |   0x0   | trbe_done | Write 1 to force [`INTR_STATE.trbe_done`](#intr_state) to 1. |

## ALERT_TEST
Alert Test Register
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "fatal_fault", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                      |
|:------:|:------:|:-------:|:------------|:-------------------------------------------------|
|  31:1  |        |         |             | Reserved                                         |
|   0    |   wo   |   0x0   | fatal_fault | Write 1 to trigger one alert event of this kind. |

## TRBE_REGWEN
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
|   0    |   ro   |   0x1   | en     | Low while the revocation engine is active, locking [`TRBE_BASE_ADDR`](#trbe_base_addr), [`TRBE_NUM_CAPS`](#trbe_num_caps) and [`TRBE_START.`](#trbe_start) [`TRBE_STATUS.busy`](#trbe_status) follows the same state one cycle later. |

## TRBE_BASE_ADDR
Address of the first capability the revocation engine sweeps.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xfffffff8`
- Register enable: [`TRBE_REGWEN`](#trbe_regwen)

### Fields

```wavejson
{"reg": [{"bits": 3}, {"name": "addr", "bits": 29, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                               |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:3  |   rw   |   0x0   | addr   | Bits 31:3 of the address. The sweep starts at a capability boundary; bits 2:0 read as zero. The address must lie in a tagged region, the main SRAM or the NVM; the sweep stops at the top of that region. |
|  2:0   |        |         |        | Reserved                                                                                                                                                                                                  |

## TRBE_NUM_CAPS
Number of capabilities the revocation engine sweeps, each of them two 32-bit words.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0x7fffffff`
- Register enable: [`TRBE_REGWEN`](#trbe_regwen)

### Fields

```wavejson
{"reg": [{"name": "num", "bits": 31, "attr": ["rw"], "rotate": 0}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                       |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------|
|   31   |        |         |        | Reserved                                                                                                                          |
|  30:0  |   rw   |   0x0   | num    | Number of capabilities. A sweep reaching past the top of its tagged region ends at its top; the register keeps the value written. |

## TRBE_START
Starts a sweep over the capabilities [`TRBE_BASE_ADDR`](#trbe_base_addr) and [`TRBE_NUM_CAPS`](#trbe_num_caps) describe.
[`TRBE_STATUS.busy`](#trbe_status) reflects the sweep in progress. A start outside CHERIoT mode, with
[`TRBE_NUM_CAPS`](#trbe_num_caps) zero, or with [`TRBE_BASE_ADDR`](#trbe_base_addr) outside the tagged regions, is ignored and
sets [`TRBE_STATUS.start_err.`](#trbe_status)
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`TRBE_REGWEN`](#trbe_regwen)

### Fields

```wavejson
{"reg": [{"name": "start", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description               |
|:------:|:------:|:-------:|:-------|:--------------------------|
|  31:1  |        |         |        | Reserved                  |
|   0    |   wo   |   0x0   | start  | Write 1 to start a sweep. |

## TRBE_STATUS
Status of the revocation engine.
- Offset: `0x20`
- Reset default: `0x0`
- Reset mask: `0x301`

### Fields

```wavejson
{"reg": [{"name": "busy", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 7}, {"name": "start_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sweep_err", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                                                                                          |
|:------:|:------:|:-------:|:----------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:10  |        |         |           | Reserved                                                                                                                                                                                                                             |
|   9    |  rw1c  |   0x0   | sweep_err | A response to the revocation engine was an error, failed its integrity check or was malformed, or the RMW filter reported a fault, during a sweep; the fatal_fault alert is raised as well. Stays set until software writes 1 to it. |
|   8    |  rw1c  |   0x0   | start_err | A start was ignored because the subsystem was not in CHERIoT mode, [`TRBE_NUM_CAPS`](#trbe_num_caps) was zero or [`TRBE_BASE_ADDR`](#trbe_base_addr) was outside the tagged regions. Stays set until software writes 1 to it.        |
|  7:1   |        |         |           | Reserved                                                                                                                                                                                                                             |
|   0    |   ro   |   0x0   | busy      | The revocation engine is sweeping; it is low once every capability of the sweep is resolved.                                                                                                                                         |

## TRBE_EPOCH
Sweep epoch, twice the number of sweeps that ended without an error, plus one while the
revocation engine is active. It is odd from the cycle a start is taken, when [`TRBE_REGWEN`](#trbe_regwen)
falls, until the engine is inactive again, and even otherwise. A sweep that ends with an
error (see [`TRBE_STATUS.sweep_err`](#trbe_status)) is not counted, so the epoch returns to the even value
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
|  31:1  |   ro   |   0x0   | count  | Sweeps that ended without an error, modulo 2^31; a sweep counts in the cycle [`TRBE_EPOCH.active`](#trbe_epoch) clears. |
|   0    |   ro   |   0x0   | active | The revocation engine is active; the inverse of [`TRBE_REGWEN.`](#trbe_regwen)                                          |


<!-- END CMDGEN -->
