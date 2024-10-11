# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/dma/data/dma.hjson -->
## Summary

| Name                                                            | Offset   |   Length | Description                                                                                                                                              |
|:----------------------------------------------------------------|:---------|---------:|:---------------------------------------------------------------------------------------------------------------------------------------------------------|
| dma.[`INTR_STATE`](#intr_state)                                 | 0x0      |        4 | Interrupt State Register                                                                                                                                 |
| dma.[`INTR_ENABLE`](#intr_enable)                               | 0x4      |        4 | Interrupt Enable Register                                                                                                                                |
| dma.[`INTR_TEST`](#intr_test)                                   | 0x8      |        4 | Interrupt Test Register                                                                                                                                  |
| dma.[`ALERT_TEST`](#alert_test)                                 | 0xc      |        4 | Alert Test Register                                                                                                                                      |
| dma.[`SRC_ADDR_LO`](#src_addr_lo)                               | 0x10     |        4 | Lower 32 bits of the physical or virtual address of memory location within SoC memory address map or physical address within OT non-secure memory space. |
| dma.[`SRC_ADDR_HI`](#src_addr_hi)                               | 0x14     |        4 | Upper 32 bits of the source address.                                                                                                                     |
| dma.[`DST_ADDR_LO`](#dst_addr_lo)                               | 0x18     |        4 | Lower 32 bits of the physical or virtual address of memory location within SoC memory address map or physical address within OT non-secure memory space. |
| dma.[`DST_ADDR_HI`](#dst_addr_hi)                               | 0x1c     |        4 | Upper 32 bits of the destination address.                                                                                                                |
| dma.[`ADDR_SPACE_ID`](#addr_space_id)                           | 0x20     |        4 | Address space that source and destination pointers refer to.                                                                                             |
| dma.[`ENABLED_MEMORY_RANGE_BASE`](#enabled_memory_range_base)   | 0x24     |        4 | Base Address to mark the start of the DMA enabled memory range within the OT internal memory space.                                                      |
| dma.[`ENABLED_MEMORY_RANGE_LIMIT`](#enabled_memory_range_limit) | 0x28     |        4 | Limit Address to mark the end of the DMA enabled memory range within the OT internal memory space.                                                       |
| dma.[`RANGE_VALID`](#range_valid)                               | 0x2c     |        4 | Indicates that the ENABLED_MEMORY_RANGE_BASE and _LIMIT registers have been programmed to restrict DMA accesses within the OT internal address space.    |
| dma.[`RANGE_REGWEN`](#range_regwen)                             | 0x30     |        4 | Used to lock the DMA enabled memory range configuration registers.                                                                                       |
| dma.[`CFG_REGWEN`](#cfg_regwen)                                 | 0x34     |        4 | Indicates whether the configuration registers are locked because the DMA controller is operating.                                                        |
| dma.[`TOTAL_DATA_SIZE`](#total_data_size)                       | 0x38     |        4 | Total size of the data blob involved in DMA movement.                                                                                                    |
| dma.[`CHUNK_DATA_SIZE`](#chunk_data_size)                       | 0x3c     |        4 | Number of bytes to be transferred in response to each interrupt/firmware request.                                                                        |
| dma.[`TRANSFER_WIDTH`](#transfer_width)                         | 0x40     |        4 | Denotes the width of each transaction that the DMA shall issue.                                                                                          |
| dma.[`CONTROL`](#control)                                       | 0x44     |        4 | Control register for DMA data movement.                                                                                                                  |
| dma.[`STATUS`](#status)                                         | 0x48     |        4 | Status indication for DMA data movement.                                                                                                                 |
| dma.[`ERROR_CODE`](#error_code)                                 | 0x4c     |        4 | Denotes the source of the operational error.                                                                                                             |
| dma.[`SHA2_DIGEST_0`](#sha2_digest)                             | 0x50     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_1`](#sha2_digest)                             | 0x54     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_2`](#sha2_digest)                             | 0x58     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_3`](#sha2_digest)                             | 0x5c     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_4`](#sha2_digest)                             | 0x60     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_5`](#sha2_digest)                             | 0x64     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_6`](#sha2_digest)                             | 0x68     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_7`](#sha2_digest)                             | 0x6c     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_8`](#sha2_digest)                             | 0x70     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_9`](#sha2_digest)                             | 0x74     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_10`](#sha2_digest)                            | 0x78     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_11`](#sha2_digest)                            | 0x7c     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_12`](#sha2_digest)                            | 0x80     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_13`](#sha2_digest)                            | 0x84     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_14`](#sha2_digest)                            | 0x88     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`SHA2_DIGEST_15`](#sha2_digest)                            | 0x8c     |        4 | Digest register for the inline hashing operation.                                                                                                        |
| dma.[`HANDSHAKE_INTR_ENABLE`](#handshake_intr_enable)           | 0x90     |        4 | Enable bits for incoming handshake interrupt wires.                                                                                                      |
| dma.[`CLEAR_INTR_SRC`](#clear_intr_src)                         | 0x94     |        4 | Valid bits for which interrupt sources need clearing.                                                                                                    |
| dma.[`CLEAR_INTR_BUS`](#clear_intr_bus)                         | 0x98     |        4 | Bus selection bit where the clearing command should be performed."                                                                                       |
| dma.[`INTR_SRC_ADDR_0`](#intr_src_addr)                         | 0x9c     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_1`](#intr_src_addr)                         | 0xa0     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_2`](#intr_src_addr)                         | 0xa4     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_3`](#intr_src_addr)                         | 0xa8     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_4`](#intr_src_addr)                         | 0xac     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_5`](#intr_src_addr)                         | 0xb0     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_6`](#intr_src_addr)                         | 0xb4     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_7`](#intr_src_addr)                         | 0xb8     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_8`](#intr_src_addr)                         | 0xbc     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_9`](#intr_src_addr)                         | 0xc0     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_ADDR_10`](#intr_src_addr)                        | 0xc4     |        4 | Destination address for interrupt source clearing write.                                                                                                 |
| dma.[`INTR_SRC_WR_VAL_0`](#intr_src_wr_val)                     | 0x11c    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_1`](#intr_src_wr_val)                     | 0x120    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_2`](#intr_src_wr_val)                     | 0x124    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_3`](#intr_src_wr_val)                     | 0x128    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_4`](#intr_src_wr_val)                     | 0x12c    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_5`](#intr_src_wr_val)                     | 0x130    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_6`](#intr_src_wr_val)                     | 0x134    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_7`](#intr_src_wr_val)                     | 0x138    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_8`](#intr_src_wr_val)                     | 0x13c    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_9`](#intr_src_wr_val)                     | 0x140    |        4 | Write value for interrupt clearing write.                                                                                                                |
| dma.[`INTR_SRC_WR_VAL_10`](#intr_src_wr_val)                    | 0x144    |        4 | Write value for interrupt clearing write.                                                                                                                |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "dma_done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "dma_error", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                               |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------------------|
|  31:2  |        |         |           | Reserved                                                                  |
|   1    |  rw1c  |   0x0   | dma_error | DMA error has occurred. DMA_STATUS.error_code register shows the details. |
|   0    |  rw1c  |   0x0   | dma_done  | DMA operation has been completed.                                         |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "dma_done", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "dma_error", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                         |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------------|
|  31:2  |        |         |           | Reserved                                                            |
|   1    |   rw   |   0x0   | dma_error | Enable interrupt when [`INTR_STATE.dma_error`](#intr_state) is set. |
|   0    |   rw   |   0x0   | dma_done  | Enable interrupt when [`INTR_STATE.dma_done`](#intr_state) is set.  |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "dma_done", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "dma_error", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                  |
|:------:|:------:|:-------:|:----------|:-------------------------------------------------------------|
|  31:2  |        |         |           | Reserved                                                     |
|   1    |   wo   |   0x0   | dma_error | Write 1 to force [`INTR_STATE.dma_error`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | dma_done  | Write 1 to force [`INTR_STATE.dma_done`](#intr_state) to 1.  |

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

## SRC_ADDR_LO
Lower 32 bits of the physical or virtual address of memory location within SoC memory address map or physical address within OT non-secure memory space.
Data is read from this location in a copy operation.
The address may be an IO virtual address.
Must be aligned to the transfer width.
- Offset: `0x10`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "src_addr_lo", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                                 |
|:------:|:------:|:-------:|:------------|:----------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | src_addr_lo | Lower 32 bits of the source address. Must be aligned to the transfer width. |

## SRC_ADDR_HI
Upper 32 bits of the source address.
Must be aligned to the transfer width.
Source and destination address must have the same alignment.
- Offset: `0x14`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "src_addr_hi", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                     |
|:------:|:------:|:-------:|:-----------------------------------------|
|  31:0  |   rw   |   0x0   | [src_addr_hi](#src_addr_hi--src_addr_hi) |

### SRC_ADDR_HI . src_addr_hi
Upper 32 bits of the physical or virtual address of memory location within SoC memory address map or physical address within OT non-secure memory space.
Must be aligned to the transfer width.
Source and destination address must have the same alignment.

## DST_ADDR_LO
Lower 32 bits of the physical or virtual address of memory location within SoC memory address map or physical address within OT non-secure memory space.
Data is written to this location in a copy operation.
The address may be an IO virtual address.
Must be aligned to the transfer width.
Source and destination address must have the same alignment.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "dst_addr_lo", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                                                                                                   |
|:------:|:------:|:-------:|:------------|:----------------------------------------------------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | dst_addr_lo | Lower 32 bits of the destination address. Must be aligned to the transfer width. Source and destination address must have the same alignment. |

## DST_ADDR_HI
Upper 32 bits of the destination address.
Must be aligned to the transfer width.
Source and destination address must have the same alignment.
- Offset: `0x1c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "dst_addr_hi", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                     |
|:------:|:------:|:-------:|:-----------------------------------------|
|  31:0  |   rw   |   0x0   | [dst_addr_hi](#dst_addr_hi--dst_addr_hi) |

### DST_ADDR_HI . dst_addr_hi
Upper 32 bits of the physical or virtual address of memory location within SoC memory address map or physical address within OT non-secure memory space.
Must be aligned to the transfer width.
Source and destination address must have the same alignment.

## ADDR_SPACE_ID
Address space that source and destination pointers refer to.
- Offset: `0x20`
- Reset default: `0x77`
- Reset mask: `0xff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "src_asid", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "dst_asid", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
|  31:8  |        |         | Reserved                             |
|  7:4   |   rw   |   0x7   | [dst_asid](#addr_space_id--dst_asid) |
|  3:0   |   rw   |   0x7   | [src_asid](#addr_space_id--src_asid) |

### ADDR_SPACE_ID . dst_asid
Target address space that the destination address pointer refers to.

| Value   | Name      | Description                                                                              |
|:--------|:----------|:-----------------------------------------------------------------------------------------|
| 0x7     | OT_ADDR   | OpenTitan 32-bit internal bus.                                                           |
| 0xa     | SOC_ADDR  | SoC control register bus using 32-bit (or 64 bits if configured by an SoC) control port. |
| 0x9     | SYS_ADDR" | SoC system address bus using 64 bit SYS port.                                            |

Other values are reserved.

### ADDR_SPACE_ID . src_asid
Target address space that the source address pointer refers to.

| Value   | Name      | Description                                                                              |
|:--------|:----------|:-----------------------------------------------------------------------------------------|
| 0x7     | OT_ADDR   | OpenTitan 32-bit internal bus.                                                           |
| 0xa     | SOC_ADDR  | SoC control register bus using 32-bit (or 64 bits if configured by an SoC) control port. |
| 0x9     | SYS_ADDR" | SoC system address bus using 64 bit SYS port.                                            |

Other values are reserved.

## ENABLED_MEMORY_RANGE_BASE
Base Address to mark the start of the DMA enabled memory range within the OT internal memory space.
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Fields

```wavejson
{"reg": [{"name": "base", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                         |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | base   | Base Address to mark the start of the DMA enabled memory range within the OT internal memory space. |

## ENABLED_MEMORY_RANGE_LIMIT
Limit Address to mark the end of the DMA enabled memory range within the OT internal memory space.
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Fields

```wavejson
{"reg": [{"name": "limit", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                        |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------|
|  31:0  |   rw   |   0x0   | limit  | Limit Address to mark the end of the DMA enabled memory range within the OT internal memory space. |

## RANGE_VALID
Indicates that the ENABLED_MEMORY_RANGE_BASE and _LIMIT registers have been programmed to restrict DMA accesses within the OT internal address space.
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0x1`
- Register enable: [`RANGE_REGWEN`](#range_regwen)

### Fields

```wavejson
{"reg": [{"name": "range_valid", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                                     |
|:------:|:------:|:-------:|:------------|:----------------------------------------------------------------|
|  31:1  |        |         |             | Reserved                                                        |
|   0    |   rw   |   0x0   | range_valid | Once set the enabled memory base and limit registers are valid. |

## RANGE_REGWEN
Used to lock the DMA enabled memory range configuration registers.
- Offset: `0x30`
- Reset default: `0x6`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "regwen", "bits": 4, "attr": ["rw0c"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                            |
|:------:|:------:|:-------:|:--------------------------------|
|  31:4  |        |         | Reserved                        |
|  3:0   |  rw0c  |   0x6   | [regwen](#range_regwen--regwen) |

### RANGE_REGWEN . regwen
Used by firmware to lock the DMA enabled memory range configuration registers from further modification.
Once this register is set to kMultiBitBool4False, it can only be set to kMultiBitBool4True through a reset event.

Default Value = kMultiBitBool4True -> Unlocked at reset.

## CFG_REGWEN
Indicates whether the configuration registers are locked because the DMA controller is operating.
In the idle state, this register is set to kMultiBitBool4True.
When the DMA is performing an operation, i.e., the DMA is busy, this register is set to kMultiBitBool4False.
During the DMA operation, the CONTROL and STATUS registers remain usable.
The comportable registers (the interrupt and alert configuration) are NOT locked during the DMA operation and can still be updated.
When the DMA reaches an interrupt or alert condition, it will perform the action according to the current register configuration.
- Offset: `0x34`
- Reset default: `0x6`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "regwen", "bits": 4, "attr": ["ro"], "rotate": 0}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                       |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |        | Reserved                                                                                                                          |
|  3:0   |   ro   |   0x6   | regwen | Used by hardware to lock the DMA configuration registers. This register is purely managed by hardware and only software readable. |

## TOTAL_DATA_SIZE
Total size of the data blob involved in DMA movement.
- Offset: `0x38`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "data_size", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                     |
|:------:|:------:|:-------:|:-----------------------------------------|
|  31:0  |   rw   |   0x0   | [data_size](#total_data_size--data_size) |

### TOTAL_DATA_SIZE . data_size
Total size (in bytes) of the data blob involved in DMA movement for multiple transfers.

Minimum: 1 byte.
Maximum: May be restricted to a maximum pre-defined size based on OT DMA enabled memory space allocation.
Works in conjunction with Transfer width register.

## CHUNK_DATA_SIZE
Number of bytes to be transferred in response to each interrupt/firmware request.
- Offset: `0x3c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "data_size", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                     |
|:------:|:------:|:-------:|:-----------------------------------------|
|  31:0  |   rw   |   0x0   | [data_size](#chunk_data_size--data_size) |

### CHUNK_DATA_SIZE . data_size
Size (in bytes) for a single DMA transfer.
In hardware handshake mode, the DMA reads in chunks of CHUNK_DATA_SIZE from the peripheral.
For a single memory transfer CHUNK_DATA_SIZE and TOTAL_DATA_SIZE are set to the same value.

Minimum: 1 byte.
Maximum: May be restricted to a maximum pre-defined size based on OT DMA enabled memory space allocation.
Works in conjunction with Transfer width register.

## TRANSFER_WIDTH
Denotes the width of each transaction that the DMA shall issue.
- Offset: `0x40`
- Reset default: `0x2`
- Reset mask: `0x3`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "transaction_width", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name                                                    |
|:------:|:------:|:-------:|:--------------------------------------------------------|
|  31:2  |        |         | Reserved                                                |
|  1:0   |   rw   |   0x2   | [transaction_width](#transfer_width--transaction_width) |

### TRANSFER_WIDTH . transaction_width
Denotes the width of each transaction that the DMA shall issue during the data movement.

Multiple transactions of this width will be issued until total size number of bytes are reached.
Note that firmware may need to set a different value if a receiving IP supports a read / write transaction width that is less than 1 DWORD.
This does not affect the wrap-around mechanism.
Note that the value 3 for this register represents an invalid configuration that leads to an error.

| Value   | Name       | Description                                            |
|:--------|:-----------|:-------------------------------------------------------|
| 0x0     | ONE_BYTE   | One byte per transaction.                              |
| 0x1     | TWO_BYTE", | Two bytes per transaction.                             |
| 0x2     | FOUR_BYTE  | Four bytes per transaction. Default value after reset. |

Other values are reserved.

## CONTROL
Control register for DMA data movement.
- Offset: `0x44`
- Reset default: `0x0`
- Reset mask: `0x880001ff`

### Fields

```wavejson
{"reg": [{"name": "opcode", "bits": 4, "attr": ["rw"], "rotate": 0}, {"name": "hardware_handshake_enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "memory_buffer_auto_increment_enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "fifo_auto_increment_enable", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "data_direction", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "initial_transfer", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 18}, {"name": "abort", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 3}, {"name": "go", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 370}}
```

|  Bits  |  Type  |  Reset  | Name                                                                                 |
|:------:|:------:|:-------:|:-------------------------------------------------------------------------------------|
|   31   |   rw   |   0x0   | [go](#control--go)                                                                   |
| 30:28  |        |         | Reserved                                                                             |
|   27   |   wo   |   0x0   | [abort](#control--abort)                                                             |
|  26:9  |        |         | Reserved                                                                             |
|   8    |   rw   |   0x0   | [initial_transfer](#control--initial_transfer)                                       |
|   7    |   rw   |   0x0   | [data_direction](#control--data_direction)                                           |
|   6    |   rw   |   0x0   | [fifo_auto_increment_enable](#control--fifo_auto_increment_enable)                   |
|   5    |   rw   |   0x0   | [memory_buffer_auto_increment_enable](#control--memory_buffer_auto_increment_enable) |
|   4    |   rw   |   0x0   | [hardware_handshake_enable](#control--hardware_handshake_enable)                     |
|  3:0   |   rw   |   0x0   | [opcode](#control--opcode)                                                           |

### CONTROL . go
Trigger the DMA operation when the Go bit is set.
For normal operation, DMA engine clears the GO bit automatically after the configured operation is complete.
For Hardware handshake operation, DMA engine does not auto clear the Go bit.
Firmware shall clear the Go bit when it intends to stop the hardware handshake operation.

### CONTROL . abort
Aborts the DMA operation if this bit is set.
Sets the corresponding bit in the status register once abort operation is complete.
Any OpenTitan-internal transactions are guaranteed to complete, but there are no guarantees on the SoC interface.

### CONTROL . initial_transfer
Marks the initial transfer to initialize the DMA and SHA engine for one transfer that can span over multiple single DMA transfers.
Used for hardware handshake and ordinary transfers, in which multiple transfers contribute to a final digest.
Note, for non-handshake transfers with inline hashing mode enabled, this bit must be set to also mark the first transfer.

### CONTROL . data_direction
Used in conjunction with the hardware handshake enable.
0: Receive data from LSIO FIFO to memory buffer.
1: Send data from memory buffer to LSIO FIFO.

### CONTROL . fifo_auto_increment_enable
Used in conjunction with the hardware handshake mode of operation.
If set, reads/writes from/to incremental addresses for FIFO data accesses within each chunk, resetting to the initial value at the beginning of each new chunk.
Else uses the same address for all transactions.

### CONTROL . memory_buffer_auto_increment_enable
Used in conjunction with the hardware handshake mode of operation.
Auto Increments the memory buffer address register by data size to point to the next memory buffer address.
Generate a warning (assert interrupt) if the auto-incremented address reaches close to the value set in limit address register to prevent destination buffer overflow.
Enables firmware to take appropriate action prior to reaching the limit.

### CONTROL . hardware_handshake_enable
Enable hardware handshake mode.
Used to clear FIFOs from low speed IO peripherals receiving data, e.g., I3C receive buffer.
  Listen to an input trigger signal.
  Read data from source address location.
  Copy to destination address.
  Number of bytes specified in size register.
  Note assumption is the peripheral lowers input once FIFO is cleared.
No explicit clearing necessary.

### CONTROL . opcode
Defines the type of DMA operations.

| Value   | Name   | Description                                             |
|:--------|:-------|:--------------------------------------------------------|
| 0x0     | COPY   | Copy Operation, Simple copy from source to destination. |
| 0x1     | SHA256 | Perform inline hashing using SHA256.                    |
| 0x2     | SHA384 | Perform inline hashing using SHA384.                    |
| 0x3     | SHA512 | Perform inline hashing using SHA512.                    |

Other values are reserved.

## STATUS
Status indication for DMA data movement.
- Offset: `0x48`
- Reset default: `0x0`
- Reset mask: `0x1f`

### Fields

```wavejson
{"reg": [{"name": "busy", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "done", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "aborted", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "error", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "sha2_digest_valid", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 27}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                                                                                        |
|:------:|:------:|:-------:|:------------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:5  |        |         |                   | Reserved                                                                                                                                                                           |
|   4    |   ro   |   0x0   | sha2_digest_valid | Indicates whether the SHA2_DIGEST register contains a valid digest. This value is cleared on the initial transfer and set when the digest is written.                              |
|   3    |  rw1c  |   0x0   | error             | Error occurred during the operation. ERROR_CODE register denotes the source of the error.                                                                                          |
|   2    |  rw1c  |   0x0   | aborted           | Set once aborted operation drains.                                                                                                                                                 |
|   1    |  rw1c  |   0x0   | done              | Configured DMA operation is complete. Cleared automatically by the hardware when starting a new transfer.                                                                          |
|   0    |   ro   |   0x0   | busy              | DMA operation is active if this bit is set. DMA engine clears this bit when operation is complete. This bit may be set as long as hardware handshake mode is active and triggered. |

## ERROR_CODE
Denotes the source of the operational error.
The error is cleared by writing the RW1C STATUS.error register.
- Offset: `0x4c`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "src_addr_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "dst_addr_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "opcode_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "size_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "bus_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "base_limit_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "range_valid_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "asid_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                                                                                                                           |
|:------:|:------:|:-------:|:------------------|:--------------------------------------------------------------------------------------------------------------------------------------|
|  31:8  |        |         |                   | Reserved                                                                                                                              |
|   7    |   ro   |   0x0   | asid_error        | The source or destination ASID contains an invalid value.                                                                             |
|   6    |   ro   |   0x0   | range_valid_error | The DMA enabled memory range is not configured.                                                                                       |
|   5    |   ro   |   0x0   | base_limit_error  | The base and limit addresses contain an invalid value.                                                                                |
|   4    |   ro   |   0x0   | bus_error         | The bus transfer returned an error.                                                                                                   |
|   3    |   ro   |   0x0   | size_error        | TRANSFER_WIDTH encodes an invalid value, TOTAL_DATA_SIZE or CHUNK_SIZE are zero, or inline hashing is not using 32-bit transfer width |
|   2    |   ro   |   0x0   | opcode_error      | Opcode is invalid.                                                                                                                    |
|   1    |   ro   |   0x0   | dst_addr_error    | Destination address is invalid.                                                                                                       |
|   0    |   ro   |   0x0   | src_addr_error    | Source address is invalid.                                                                                                            |

## SHA2_DIGEST
Digest register for the inline hashing operation.
Depending on the used hashing mode, not all registers are used.
  SHA256: Digest is stored in registers 0 to 7
  SHA384: Digest is stored in registers 0 to 11
  SHA512: Digest is stored in registers 0 to 15
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name           | Offset   |
|:---------------|:---------|
| SHA2_DIGEST_0  | 0x50     |
| SHA2_DIGEST_1  | 0x54     |
| SHA2_DIGEST_2  | 0x58     |
| SHA2_DIGEST_3  | 0x5c     |
| SHA2_DIGEST_4  | 0x60     |
| SHA2_DIGEST_5  | 0x64     |
| SHA2_DIGEST_6  | 0x68     |
| SHA2_DIGEST_7  | 0x6c     |
| SHA2_DIGEST_8  | 0x70     |
| SHA2_DIGEST_9  | 0x74     |
| SHA2_DIGEST_10 | 0x78     |
| SHA2_DIGEST_11 | 0x7c     |
| SHA2_DIGEST_12 | 0x80     |
| SHA2_DIGEST_13 | 0x84     |
| SHA2_DIGEST_14 | 0x88     |
| SHA2_DIGEST_15 | 0x8c     |


### Fields

```wavejson
{"reg": [{"name": "data", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description      |
|:------:|:------:|:-------:|:-------|:-----------------|
|  31:0  |   ro   |   0x0   | data   | SHA2 digest data |

## HANDSHAKE_INTR_ENABLE
Enable bits for incoming handshake interrupt wires.
- Offset: `0x90`
- Reset default: `0x7ff`
- Reset mask: `0x7ff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "mask", "bits": 11, "attr": ["rw"], "rotate": 0}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                         |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------|
| 31:11  |        |         |        | Reserved                                            |
|  10:0  |   rw   |  0x7ff  | mask   | Enable bits for incoming handshake interrupt wires. |

## CLEAR_INTR_SRC
Valid bits for which interrupt sources need clearing.
When HANDSHAKE_INTR_ENABLE is non-zero and corresponding lsio_trigger becomes set,
DMA issues writes with address from INTR_SRC_ADDR and write value from INTR_SRC_WR_VAL corresponding to each
bit set in this register.
- Offset: `0x94`
- Reset default: `0x0`
- Reset mask: `0x7ff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "source", "bits": 11, "attr": ["rw"], "rotate": 0}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                      |
|:------:|:------:|:-------:|:-------|:---------------------------------|
| 31:11  |        |         |        | Reserved                         |
|  10:0  |   rw   |   0x0   | source | Source N needs interrupt cleared |

## CLEAR_INTR_BUS
Bus selection bit where the clearing command should be performed."
0: CTN/System fabric
1: OT-internal crossbar
- Offset: `0x98`
- Reset default: `0x0`
- Reset mask: `0x7ff`
- Register enable: [`CFG_REGWEN`](#cfg_regwen)

### Fields

```wavejson
{"reg": [{"name": "bus", "bits": 11, "attr": ["rw"], "rotate": 0}, {"bits": 21}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                     |
|:------:|:------:|:-------:|:-------|:--------------------------------|
| 31:11  |        |         |        | Reserved                        |
|  10:0  |   rw   |   0x0   | bus    | Bus selection bit for source N. |

## INTR_SRC_ADDR
Destination address for interrupt source clearing write.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name             | Offset   |
|:-----------------|:---------|
| INTR_SRC_ADDR_0  | 0x9c     |
| INTR_SRC_ADDR_1  | 0xa0     |
| INTR_SRC_ADDR_2  | 0xa4     |
| INTR_SRC_ADDR_3  | 0xa8     |
| INTR_SRC_ADDR_4  | 0xac     |
| INTR_SRC_ADDR_5  | 0xb0     |
| INTR_SRC_ADDR_6  | 0xb4     |
| INTR_SRC_ADDR_7  | 0xb8     |
| INTR_SRC_ADDR_8  | 0xbc     |
| INTR_SRC_ADDR_9  | 0xc0     |
| INTR_SRC_ADDR_10 | 0xc4     |


### Fields

```wavejson
{"reg": [{"name": "addr", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                              |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------|
|  31:0  |   rw   |   0x0   | addr   | Destination address for interrupt source clearing write. |

## INTR_SRC_WR_VAL
Write value for interrupt clearing write.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| INTR_SRC_WR_VAL_0  | 0x11c    |
| INTR_SRC_WR_VAL_1  | 0x120    |
| INTR_SRC_WR_VAL_2  | 0x124    |
| INTR_SRC_WR_VAL_3  | 0x128    |
| INTR_SRC_WR_VAL_4  | 0x12c    |
| INTR_SRC_WR_VAL_5  | 0x130    |
| INTR_SRC_WR_VAL_6  | 0x134    |
| INTR_SRC_WR_VAL_7  | 0x138    |
| INTR_SRC_WR_VAL_8  | 0x13c    |
| INTR_SRC_WR_VAL_9  | 0x140    |
| INTR_SRC_WR_VAL_10 | 0x144    |


### Fields

```wavejson
{"reg": [{"name": "wr_val", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                               |
|:------:|:------:|:-------:|:-------|:------------------------------------------|
|  31:0  |   rw   |   0x0   | wr_val | Write value for interrupt clearing write. |


<!-- END CMDGEN -->
