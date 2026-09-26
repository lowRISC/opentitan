# Registers

The revocation bitmap is not a register but a memory window on the `revbm` interface; see the
[Theory of Operation](theory_of_operation.md#meta-sram-address-map).

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/cheriot/data/cheriot.hjson -->
## Summary

| Name                                        | Offset   |   Length | Description                                                                                                              |
|:--------------------------------------------|:---------|---------:|:-------------------------------------------------------------------------------------------------------------------------|
| cheriot.[`ALERT_TEST`](#alert_test)         | 0x0      |        4 | Alert Test Register                                                                                                      |
| cheriot.[`TRBE_REGWEN`](#trbe_regwen)       | 0x4      |        4 | Write enable for the revocation engine registers.                                                                        |
| cheriot.[`TRBE_BASE_ADDR`](#trbe_base_addr) | 0x8      |        4 | Address of the first capability the revocation engine sweeps.                                                            |
| cheriot.[`TRBE_NUM_CAPS`](#trbe_num_caps)   | 0xc      |        4 | Number of capabilities the revocation engine sweeps, each of them two 32-bit words.                                      |
| cheriot.[`TRBE_START`](#trbe_start)         | 0x10     |        4 | Starts a sweep over the capabilities [`TRBE_BASE_ADDR`](#trbe_base_addr) and [`TRBE_NUM_CAPS`](#trbe_num_caps) describe. |
| cheriot.[`TRBE_BUSY`](#trbe_busy)           | 0x14     |        4 | Status of the revocation engine.                                                                                         |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
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
- Offset: `0x4`
- Reset default: `0x1`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "en", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                 |
|:------:|:------:|:-------:|:-------|:------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                                                                                    |
|   0    |   ro   |   0x1   | en     | Low while [`TRBE_BUSY`](#trbe_busy) is set, locking [`TRBE_BASE_ADDR`](#trbe_base_addr), [`TRBE_NUM_CAPS`](#trbe_num_caps) and [`TRBE_START.`](#trbe_start) |

## TRBE_BASE_ADDR
Address of the first capability the revocation engine sweeps.
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xfffffff8`
- Register enable: [`TRBE_REGWEN`](#trbe_regwen)

### Fields

```wavejson
{"reg": [{"bits": 3}, {"name": "addr", "bits": 29, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                  |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:3  |   rw   |   0x0   | addr   | Bits 31:3 of the address. The sweep starts at a capability boundary; bits 2:0 read as zero. The address must lie in the tagged SRAM range; the sweep stops at the top of it. |
|  2:0   |        |         |        | Reserved                                                                                                                                                                     |

## TRBE_NUM_CAPS
Number of capabilities the revocation engine sweeps, each of them two 32-bit words.
- Offset: `0xc`
- Reset default: `0x0`
- Reset mask: `0x7fffffff`
- Register enable: [`TRBE_REGWEN`](#trbe_regwen)

### Fields

```wavejson
{"reg": [{"name": "num", "bits": 31, "attr": ["rw"], "rotate": 0}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                           |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------------------------------------------------------------------------------|
|   31   |        |         |        | Reserved                                                                                                                              |
|  30:0  |   rw   |   0x0   | num    | Number of capabilities. A sweep reaching past the top of the tagged SRAM range ends at its top; the register keeps the value written. |

## TRBE_START
Starts a sweep over the capabilities [`TRBE_BASE_ADDR`](#trbe_base_addr) and [`TRBE_NUM_CAPS`](#trbe_num_caps) describe.
[`TRBE_BUSY`](#trbe_busy) reflects the sweep in progress. A start outside CHERIoT mode, with
[`TRBE_NUM_CAPS`](#trbe_num_caps) zero, or with [`TRBE_BASE_ADDR`](#trbe_base_addr) outside the tagged SRAM range, is ignored.
- Offset: `0x10`
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

## TRBE_BUSY
Status of the revocation engine.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "busy", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                  |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------|
|  31:1  |        |         |        | Reserved                                                                                     |
|   0    |   ro   |   0x0   | busy   | The revocation engine is sweeping; it is low once every capability of the sweep is resolved. |


<!-- END CMDGEN -->
