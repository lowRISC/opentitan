# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/bkdr_loader/data/bkdr_loader.hjson -->
## Summary

| Name                                                                  | Offset   |   Length | Description                                                                       |
|:----------------------------------------------------------------------|:---------|---------:|:----------------------------------------------------------------------------------|
| bkdr_loader.[`STATUS`](#status)                                       | 0x0      |        4 | Status register                                                                   |
| bkdr_loader.[`CONTROL`](#control)                                     | 0x4      |        4 | Control register                                                                  |
| bkdr_loader.[`NUM_BKDR_TARGETS`](#num_bkdr_targets)                   | 0x8      |        4 | Number of bkdr targets available.                                                 |
| bkdr_loader.[`MISSION_MODE_SWITCH_DELAY`](#mission_mode_switch_delay) | 0xc      |        4 | Number of SoC clock cycles to wait before executing switch to mission mode        |
| bkdr_loader.[`USR_ACCESS_TIMESTAMP`](#usr_access_timestamp)           | 0x10     |        4 | TIMESTAMP value written to the USR_ACCESS register during bitstream generation.   |
| bkdr_loader.[`TARGET_INFO_0`](#target_info)                           | 0x100    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_1`](#target_info)                           | 0x104    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_2`](#target_info)                           | 0x108    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_3`](#target_info)                           | 0x10c    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_4`](#target_info)                           | 0x110    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_5`](#target_info)                           | 0x114    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_6`](#target_info)                           | 0x118    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_7`](#target_info)                           | 0x11c    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_8`](#target_info)                           | 0x120    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_9`](#target_info)                           | 0x124    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_10`](#target_info)                          | 0x128    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`TARGET_INFO_11`](#target_info)                          | 0x12c    |        4 | ASCII 4-character string values (big endian) identifying each bkdr target memory. |
| bkdr_loader.[`WIDTH_INFO_0`](#width_info)                             | 0x200    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_1`](#width_info)                             | 0x204    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_2`](#width_info)                             | 0x208    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_3`](#width_info)                             | 0x20c    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_4`](#width_info)                             | 0x210    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_5`](#width_info)                             | 0x214    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_6`](#width_info)                             | 0x218    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_7`](#width_info)                             | 0x21c    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_8`](#width_info)                             | 0x220    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_9`](#width_info)                             | 0x224    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_10`](#width_info)                            | 0x228    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`WIDTH_INFO_11`](#width_info)                            | 0x22c    |        4 | The SRAM word width of a given bkdr target memory.                                |
| bkdr_loader.[`DEPTH_INFO_0`](#depth_info)                             | 0x300    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_1`](#depth_info)                             | 0x304    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_2`](#depth_info)                             | 0x308    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_3`](#depth_info)                             | 0x30c    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_4`](#depth_info)                             | 0x310    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_5`](#depth_info)                             | 0x314    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_6`](#depth_info)                             | 0x318    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_7`](#depth_info)                             | 0x31c    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_8`](#depth_info)                             | 0x320    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_9`](#depth_info)                             | 0x324    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_10`](#depth_info)                            | 0x328    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`DEPTH_INFO_11`](#depth_info)                            | 0x32c    |        4 | The number of SRAM words of a given bkdr target memory.                           |
| bkdr_loader.[`READ_DATA_0`](#read_data)                               | 0x400    |        4 | Value to be read from the target memory.                                          |
| bkdr_loader.[`READ_DATA_1`](#read_data)                               | 0x404    |        4 | Value to be read from the target memory.                                          |
| bkdr_loader.[`READ_DATA_2`](#read_data)                               | 0x408    |        4 | Value to be read from the target memory.                                          |
| bkdr_loader.[`READ_DATA_3`](#read_data)                               | 0x40c    |        4 | Value to be read from the target memory.                                          |
| bkdr_loader.[`READ_DATA_4`](#read_data)                               | 0x410    |        4 | Value to be read from the target memory.                                          |
| bkdr_loader.[`READ_DATA_5`](#read_data)                               | 0x414    |        4 | Value to be read from the target memory.                                          |
| bkdr_loader.[`READ_DATA_6`](#read_data)                               | 0x418    |        4 | Value to be read from the target memory.                                          |
| bkdr_loader.[`READ_DATA_7`](#read_data)                               | 0x41c    |        4 | Value to be read from the target memory.                                          |
| bkdr_loader.[`WRITE_DATA_0`](#write_data)                             | 0x500    |        4 | Value to be written to the target memory.                                         |
| bkdr_loader.[`WRITE_DATA_1`](#write_data)                             | 0x504    |        4 | Value to be written to the target memory.                                         |
| bkdr_loader.[`WRITE_DATA_2`](#write_data)                             | 0x508    |        4 | Value to be written to the target memory.                                         |
| bkdr_loader.[`WRITE_DATA_3`](#write_data)                             | 0x50c    |        4 | Value to be written to the target memory.                                         |
| bkdr_loader.[`WRITE_DATA_4`](#write_data)                             | 0x510    |        4 | Value to be written to the target memory.                                         |
| bkdr_loader.[`WRITE_DATA_5`](#write_data)                             | 0x514    |        4 | Value to be written to the target memory.                                         |
| bkdr_loader.[`WRITE_DATA_6`](#write_data)                             | 0x518    |        4 | Value to be written to the target memory.                                         |
| bkdr_loader.[`WRITE_DATA_7`](#write_data)                             | 0x51c    |        4 | Value to be written to the target memory.                                         |
| bkdr_loader.[`INDEX`](#index)                                         | 0x600    |        4 | Index address of the SRAM word to be accessed.                                    |

## STATUS
Status register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "TARGET_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "CLEAR_IDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                              |
|:------:|:------:|:-------:|:-------------|:-----------------------------------------|
|  31:2  |        |         |              | Reserved                                 |
|   1    |   ro   |    x    | CLEAR_IDLE   | Read 1 if no clear operation is ongoing. |
|   0    |   ro   |    x    | TARGET_ERROR | Target index is currently misconfigured. |

## CONTROL
Control register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0xff07`

### Fields

```wavejson
{"reg": [{"name": "DONE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "WRITE_ENA", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CLEAR_START", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "TARGET_IDX", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
| 31:16  |        |         | Reserved                             |
|  15:8  |   rw   |   0x0   | [TARGET_IDX](#control--target_idx)   |
|  7:3   |        |         | Reserved                             |
|   2    |   rw   |   0x0   | [CLEAR_START](#control--clear_start) |
|   1    |   rw   |   0x0   | [WRITE_ENA](#control--write_ena)     |
|   0    |   rw   |   0x0   | [DONE](#control--done)               |

### CONTROL . TARGET_IDX
The bkdr memory index to write to.

### CONTROL . CLEAR_START
Write 1 to trigger the bkdr_loader to clear the entire target memory
that is currently selected by `TARGET_IDX`.
The word that is cleared with is selected by `WRITE_DATA`.
Clear operation is completed if `STATUS.CLEAR_IDLE` becomes 1.
bkdr writes will not have any effects during an active clear operation.

### CONTROL . WRITE_ENA
If set, a bkdr write is launched when writing to the index register.

### CONTROL . DONE
Write 1 to trigger the bkdr_loader to switch to mission mode.
After this, the bkdr_loader cannot be used until the next reset.

## NUM_BKDR_TARGETS
Number of bkdr targets available.
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   ro   |    x    | VAL    |               |

## MISSION_MODE_SWITCH_DELAY
Number of SoC clock cycles to wait before executing switch to mission mode
after writing CONTROL.DONE register.
- Offset: `0xc`
- Reset default: `0x61a8`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   rw   | 0x61a8  | VAL    |               |

## USR_ACCESS_TIMESTAMP
TIMESTAMP value written to the USR_ACCESS register during bitstream generation.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   ro   |    x    | VAL    |               |

## TARGET_INFO
ASCII 4-character string values (big endian) identifying each bkdr target memory.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| TARGET_INFO_0  | 0x100    |
| TARGET_INFO_1  | 0x104    |
| TARGET_INFO_2  | 0x108    |
| TARGET_INFO_3  | 0x10c    |
| TARGET_INFO_4  | 0x110    |
| TARGET_INFO_5  | 0x114    |
| TARGET_INFO_6  | 0x118    |
| TARGET_INFO_7  | 0x11c    |
| TARGET_INFO_8  | 0x120    |
| TARGET_INFO_9  | 0x124    |
| TARGET_INFO_10 | 0x128    |
| TARGET_INFO_11 | 0x12c    |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   ro   |    x    | VAL    |               |

## WIDTH_INFO
The SRAM word width of a given bkdr target memory.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| WIDTH_INFO_0  | 0x200    |
| WIDTH_INFO_1  | 0x204    |
| WIDTH_INFO_2  | 0x208    |
| WIDTH_INFO_3  | 0x20c    |
| WIDTH_INFO_4  | 0x210    |
| WIDTH_INFO_5  | 0x214    |
| WIDTH_INFO_6  | 0x218    |
| WIDTH_INFO_7  | 0x21c    |
| WIDTH_INFO_8  | 0x220    |
| WIDTH_INFO_9  | 0x224    |
| WIDTH_INFO_10 | 0x228    |
| WIDTH_INFO_11 | 0x22c    |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   ro   |    x    | VAL    |               |

## DEPTH_INFO
The number of SRAM words of a given bkdr target memory.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| DEPTH_INFO_0  | 0x300    |
| DEPTH_INFO_1  | 0x304    |
| DEPTH_INFO_2  | 0x308    |
| DEPTH_INFO_3  | 0x30c    |
| DEPTH_INFO_4  | 0x310    |
| DEPTH_INFO_5  | 0x314    |
| DEPTH_INFO_6  | 0x318    |
| DEPTH_INFO_7  | 0x31c    |
| DEPTH_INFO_8  | 0x320    |
| DEPTH_INFO_9  | 0x324    |
| DEPTH_INFO_10 | 0x328    |
| DEPTH_INFO_11 | 0x32c    |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   ro   |    x    | VAL    |               |

## READ_DATA
Value to be read from the target memory.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name        | Offset   |
|:------------|:---------|
| READ_DATA_0 | 0x400    |
| READ_DATA_1 | 0x404    |
| READ_DATA_2 | 0x408    |
| READ_DATA_3 | 0x40c    |
| READ_DATA_4 | 0x410    |
| READ_DATA_5 | 0x414    |
| READ_DATA_6 | 0x418    |
| READ_DATA_7 | 0x41c    |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   ro   |   0x0   | VAL    |               |

## WRITE_DATA
Value to be written to the target memory.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name         | Offset   |
|:-------------|:---------|
| WRITE_DATA_0 | 0x500    |
| WRITE_DATA_1 | 0x504    |
| WRITE_DATA_2 | 0x508    |
| WRITE_DATA_3 | 0x50c    |
| WRITE_DATA_4 | 0x510    |
| WRITE_DATA_5 | 0x514    |
| WRITE_DATA_6 | 0x518    |
| WRITE_DATA_7 | 0x51c    |


### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   rw   |   0x0   | VAL    |               |

## INDEX
Index address of the SRAM word to be accessed.
- Offset: `0x600`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VAL", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description   |
|:------:|:------:|:-------:|:-------|:--------------|
|  31:0  |   rw   |   0x0   | VAL    |               |


<!-- END CMDGEN -->
