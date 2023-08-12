# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/rom_ctrl/data/rom_ctrl.hjson -->
## Summary of the **`regs`** interface's registers

| Name                                               | Offset   |   Length | Description                                         |
|:---------------------------------------------------|:---------|---------:|:----------------------------------------------------|
| rom_ctrl.[`ALERT_TEST`](#alert_test)               | 0x0      |        4 | Alert Test Register                                 |
| rom_ctrl.[`FATAL_ALERT_CAUSE`](#fatal_alert_cause) | 0x4      |        4 | The cause of a fatal alert.                         |
| rom_ctrl.[`DIGEST_0`](#digest)                     | 0x8      |        4 | The digest computed from the contents of ROM        |
| rom_ctrl.[`DIGEST_1`](#digest)                     | 0xc      |        4 | The digest computed from the contents of ROM        |
| rom_ctrl.[`DIGEST_2`](#digest)                     | 0x10     |        4 | The digest computed from the contents of ROM        |
| rom_ctrl.[`DIGEST_3`](#digest)                     | 0x14     |        4 | The digest computed from the contents of ROM        |
| rom_ctrl.[`DIGEST_4`](#digest)                     | 0x18     |        4 | The digest computed from the contents of ROM        |
| rom_ctrl.[`DIGEST_5`](#digest)                     | 0x1c     |        4 | The digest computed from the contents of ROM        |
| rom_ctrl.[`DIGEST_6`](#digest)                     | 0x20     |        4 | The digest computed from the contents of ROM        |
| rom_ctrl.[`DIGEST_7`](#digest)                     | 0x24     |        4 | The digest computed from the contents of ROM        |
| rom_ctrl.[`EXP_DIGEST_0`](#exp_digest)             | 0x28     |        4 | The expected digest, stored in the top words of ROM |
| rom_ctrl.[`EXP_DIGEST_1`](#exp_digest)             | 0x2c     |        4 | The expected digest, stored in the top words of ROM |
| rom_ctrl.[`EXP_DIGEST_2`](#exp_digest)             | 0x30     |        4 | The expected digest, stored in the top words of ROM |
| rom_ctrl.[`EXP_DIGEST_3`](#exp_digest)             | 0x34     |        4 | The expected digest, stored in the top words of ROM |
| rom_ctrl.[`EXP_DIGEST_4`](#exp_digest)             | 0x38     |        4 | The expected digest, stored in the top words of ROM |
| rom_ctrl.[`EXP_DIGEST_5`](#exp_digest)             | 0x3c     |        4 | The expected digest, stored in the top words of ROM |
| rom_ctrl.[`EXP_DIGEST_6`](#exp_digest)             | 0x40     |        4 | The expected digest, stored in the top words of ROM |
| rom_ctrl.[`EXP_DIGEST_7`](#exp_digest)             | 0x44     |        4 | The expected digest, stored in the top words of ROM |

## ALERT_TEST
Alert Test Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x1`

### Fields

```wavejson
{"reg": [{"name": "fatal", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 31}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                      |
|:------:|:------:|:-------:|:-------|:-------------------------------------------------|
|  31:1  |        |         |        | Reserved                                         |
|   0    |   wo   |   0x0   | fatal  | Write 1 to trigger one alert event of this kind. |

## FATAL_ALERT_CAUSE
The cause of a fatal alert.

The bits of this register correspond to errors that can cause a fatal
alert. Software can read these bits to see what went wrong. Once set,
these bits cannot be cleared.
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "checker_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "integrity_error", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                            |
|:------:|:------:|:-------:|:----------------|:-------------------------------------------------------|
|  31:2  |        |         |                 | Reserved                                               |
|   1    |   ro   |   0x0   | integrity_error | Set on an integrity error from the register interface. |
|   0    |   ro   |   0x0   | checker_error   | Set on a fatal error detected by the ROM checker.      |

## DIGEST
The digest computed from the contents of ROM
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name     | Offset   |
|:---------|:---------|
| DIGEST_0 | 0x8      |
| DIGEST_1 | 0xc      |
| DIGEST_2 | 0x10     |
| DIGEST_3 | 0x14     |
| DIGEST_4 | 0x18     |
| DIGEST_5 | 0x1c     |
| DIGEST_6 | 0x20     |
| DIGEST_7 | 0x24     |


### Fields

```wavejson
{"reg": [{"name": "DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   ro   |   0x0   | DIGEST | 32 bits of the digest |

## EXP_DIGEST
The expected digest, stored in the top words of ROM
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name         | Offset   |
|:-------------|:---------|
| EXP_DIGEST_0 | 0x28     |
| EXP_DIGEST_1 | 0x2c     |
| EXP_DIGEST_2 | 0x30     |
| EXP_DIGEST_3 | 0x34     |
| EXP_DIGEST_4 | 0x38     |
| EXP_DIGEST_5 | 0x3c     |
| EXP_DIGEST_6 | 0x40     |
| EXP_DIGEST_7 | 0x44     |


### Fields

```wavejson
{"reg": [{"name": "DIGEST", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description           |
|:------:|:------:|:-------:|:-------|:----------------------|
|  31:0  |   ro   |   0x0   | DIGEST | 32 bits of the digest |

## Summary of the **`rom`** interface's registers

| Name                   | Offset   |   Length | Description   |
|:-----------------------|:---------|---------:|:--------------|
| rom_ctrl.[`ROM`](#rom) | 0x0      |    32768 | ROM data      |

## ROM
ROM data

- Word Aligned Offset Range: `0x0`to`0x7ffc`
- Size (words): `8192`
- Access: `ro`
- Byte writes are *not* supported.


<!-- END CMDGEN -->
