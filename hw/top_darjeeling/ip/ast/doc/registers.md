# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/top_darjeeling/ip/ast/data/ast.hjson -->
## Summary

| Name                    | Offset   |   Length | Description                                     |
|:------------------------|:---------|---------:|:------------------------------------------------|
| ast.[`REGA0`](#rega0)   | 0x0      |        4 | AST Register 0 for OTP/ROM Write Testing        |
| ast.[`REGA1`](#rega1)   | 0x4      |        4 | AST 1 Register for OTP/ROM Write Testing        |
| ast.[`REGA2`](#rega2)   | 0x8      |        4 | AST 2 Register for OTP/ROM Write Testing        |
| ast.[`REGA3`](#rega3)   | 0xc      |        4 | AST 3 Register for OTP/ROM Write Testing        |
| ast.[`REGA4`](#rega4)   | 0x10     |        4 | AST 4 Register for OTP/ROM Write Testing        |
| ast.[`REGA5`](#rega5)   | 0x14     |        4 | AST 5 Register for OTP/ROM Write Testing        |
| ast.[`REGA6`](#rega6)   | 0x18     |        4 | AST 6 Register for OTP/ROM Write Testing        |
| ast.[`REGA7`](#rega7)   | 0x1c     |        4 | AST 7 Register for OTP/ROM Write Testing        |
| ast.[`REGA8`](#rega8)   | 0x20     |        4 | AST 8 Register for OTP/ROM Write Testing        |
| ast.[`REGA9`](#rega9)   | 0x24     |        4 | AST 9 Register for OTP/ROM Write Testing        |
| ast.[`REGA10`](#rega10) | 0x28     |        4 | AST 10 Register for OTP/ROM Write Testing       |
| ast.[`REGA11`](#rega11) | 0x2c     |        4 | AST 11 Register for OTP/ROM Write Testing       |
| ast.[`REGA12`](#rega12) | 0x30     |        4 | AST 13 Register for OTP/ROM Write Testing       |
| ast.[`REGA13`](#rega13) | 0x34     |        4 | AST 13 Register for OTP/ROM Write Testing       |
| ast.[`REGA14`](#rega14) | 0x38     |        4 | AST 14 Register for OTP/ROM Write Testing       |
| ast.[`REGA15`](#rega15) | 0x3c     |        4 | AST 15 Register for OTP/ROM Write Testing       |
| ast.[`REGA16`](#rega16) | 0x40     |        4 | AST 16 Register for OTP/ROM Write Testing       |
| ast.[`REGA17`](#rega17) | 0x44     |        4 | AST 17 Register for OTP/ROM Write Testing       |
| ast.[`REGA18`](#rega18) | 0x48     |        4 | AST 18 Register for OTP/ROM Write Testing       |
| ast.[`REGA19`](#rega19) | 0x4c     |        4 | AST 19 Register for OTP/ROM Write Testing       |
| ast.[`REGA20`](#rega20) | 0x50     |        4 | AST 20 Register for OTP/ROM Write Testing       |
| ast.[`REGA21`](#rega21) | 0x54     |        4 | AST 21 Register for OTP/ROM Write Testing       |
| ast.[`REGA22`](#rega22) | 0x58     |        4 | AST 22 Register for OTP/ROM Write Testing       |
| ast.[`REGA23`](#rega23) | 0x5c     |        4 | AST 23 Register for OTP/ROM Write Testing       |
| ast.[`REGA24`](#rega24) | 0x60     |        4 | AST 24 Register for OTP/ROM Write Testing       |
| ast.[`REGA25`](#rega25) | 0x64     |        4 | AST 25 Register for OTP/ROM Write Testing       |
| ast.[`REGA26`](#rega26) | 0x68     |        4 | AST 26 Register for OTP/ROM Write Testing       |
| ast.[`REGA27`](#rega27) | 0x6c     |        4 | AST 27 Register for OTP/ROM Write Testing       |
| ast.[`REGA28`](#rega28) | 0x70     |        4 | AST 28 Register for OTP/ROM Write Testing       |
| ast.[`REGA29`](#rega29) | 0x74     |        4 | AST 29 Register for OTP/ROM Write Testing       |
| ast.[`REGAL`](#regal)   | 0x78     |        4 | AST Last Register for OTP/ROM Write Testing     |
| ast.[`REGB_0`](#regb)   | 0x200    |        4 | AST Registers Array-B to set address space size |
| ast.[`REGB_1`](#regb)   | 0x204    |        4 | AST Registers Array-B to set address space size |
| ast.[`REGB_2`](#regb)   | 0x208    |        4 | AST Registers Array-B to set address space size |
| ast.[`REGB_3`](#regb)   | 0x20c    |        4 | AST Registers Array-B to set address space size |
| ast.[`REGB_4`](#regb)   | 0x210    |        4 | AST Registers Array-B to set address space size |

## REGA0
AST Register 0 for OTP/ROM Write Testing
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   ro   |   0x0   | reg32  | 32-bit Register |

## REGA1
AST 1 Register for OTP/ROM Write Testing
- Offset: `0x4`
- Reset default: `0x1`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   ro   |   0x1   | reg32  | 32-bit Register |

## REGA2
AST 2 Register for OTP/ROM Write Testing
- Offset: `0x8`
- Reset default: `0x2`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0x2   | reg32  | 32-bit Register |

## REGA3
AST 3 Register for OTP/ROM Write Testing
- Offset: `0xc`
- Reset default: `0x3`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0x3   | reg32  | 32-bit Register |

## REGA4
AST 4 Register for OTP/ROM Write Testing
- Offset: `0x10`
- Reset default: `0x4`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0x4   | reg32  | 32-bit Register |

## REGA5
AST 5 Register for OTP/ROM Write Testing
- Offset: `0x14`
- Reset default: `0x5`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0x5   | reg32  | 32-bit Register |

## REGA6
AST 6 Register for OTP/ROM Write Testing
- Offset: `0x18`
- Reset default: `0x6`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0x6   | reg32  | 32-bit Register |

## REGA7
AST 7 Register for OTP/ROM Write Testing
- Offset: `0x1c`
- Reset default: `0x7`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0x7   | reg32  | 32-bit Register |

## REGA8
AST 8 Register for OTP/ROM Write Testing
- Offset: `0x20`
- Reset default: `0x8`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0x8   | reg32  | 32-bit Register |

## REGA9
AST 9 Register for OTP/ROM Write Testing
- Offset: `0x24`
- Reset default: `0x9`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0x9   | reg32  | 32-bit Register |

## REGA10
AST 10 Register for OTP/ROM Write Testing
- Offset: `0x28`
- Reset default: `0xa`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0xa   | reg32  | 32-bit Register |

## REGA11
AST 11 Register for OTP/ROM Write Testing
- Offset: `0x2c`
- Reset default: `0xb`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0xb   | reg32  | 32-bit Register |

## REGA12
AST 13 Register for OTP/ROM Write Testing
- Offset: `0x30`
- Reset default: `0xc`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0xc   | reg32  | 32-bit Register |

## REGA13
AST 13 Register for OTP/ROM Write Testing
- Offset: `0x34`
- Reset default: `0xd`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0xd   | reg32  | 32-bit Register |

## REGA14
AST 14 Register for OTP/ROM Write Testing
- Offset: `0x38`
- Reset default: `0xe`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0xe   | reg32  | 32-bit Register |

## REGA15
AST 15 Register for OTP/ROM Write Testing
- Offset: `0x3c`
- Reset default: `0xf`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0xf   | reg32  | 32-bit Register |

## REGA16
AST 16 Register for OTP/ROM Write Testing
- Offset: `0x40`
- Reset default: `0x10`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x10   | reg32  | 32-bit Register |

## REGA17
AST 17 Register for OTP/ROM Write Testing
- Offset: `0x44`
- Reset default: `0x11`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x11   | reg32  | 32-bit Register |

## REGA18
AST 18 Register for OTP/ROM Write Testing
- Offset: `0x48`
- Reset default: `0x12`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x12   | reg32  | 32-bit Register |

## REGA19
AST 19 Register for OTP/ROM Write Testing
- Offset: `0x4c`
- Reset default: `0x13`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x13   | reg32  | 32-bit Register |

## REGA20
AST 20 Register for OTP/ROM Write Testing
- Offset: `0x50`
- Reset default: `0x14`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x14   | reg32  | 32-bit Register |

## REGA21
AST 21 Register for OTP/ROM Write Testing
- Offset: `0x54`
- Reset default: `0x15`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x15   | reg32  | 32-bit Register |

## REGA22
AST 22 Register for OTP/ROM Write Testing
- Offset: `0x58`
- Reset default: `0x16`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x16   | reg32  | 32-bit Register |

## REGA23
AST 23 Register for OTP/ROM Write Testing
- Offset: `0x5c`
- Reset default: `0x17`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x17   | reg32  | 32-bit Register |

## REGA24
AST 24 Register for OTP/ROM Write Testing
- Offset: `0x60`
- Reset default: `0x18`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x18   | reg32  | 32-bit Register |

## REGA25
AST 25 Register for OTP/ROM Write Testing
- Offset: `0x64`
- Reset default: `0x19`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x19   | reg32  | 32-bit Register |

## REGA26
AST 26 Register for OTP/ROM Write Testing
- Offset: `0x68`
- Reset default: `0x1a`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x1a   | reg32  | 32-bit Register |

## REGA27
AST 27 Register for OTP/ROM Write Testing
- Offset: `0x6c`
- Reset default: `0x1b`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x1b   | reg32  | 32-bit Register |

## REGA28
AST 28 Register for OTP/ROM Write Testing
- Offset: `0x70`
- Reset default: `0x1c`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   ro   |  0x1c   | reg32  | 32-bit Register |

## REGA29
AST 29 Register for OTP/ROM Write Testing
- Offset: `0x74`
- Reset default: `0x1d`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |  0x1d   | reg32  | 32-bit Register |

## REGAL
AST Last Register for OTP/ROM Write Testing
- Offset: `0x78`
- Reset default: `0x1e`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["wo"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   wo   |  0x1e   | reg32  | 32-bit Register |

## REGB
AST Registers Array-B to set address space size
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name   | Offset   |
|:-------|:---------|
| REGB_0 | 0x200    |
| REGB_1 | 0x204    |
| REGB_2 | 0x208    |
| REGB_3 | 0x20c    |
| REGB_4 | 0x210    |


### Fields

```wavejson
{"reg": [{"name": "reg32", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description     |
|:------:|:------:|:-------:|:-------|:----------------|
|  31:0  |   rw   |   0x0   | reg32  | 32-bit Register |


<!-- END CMDGEN -->
