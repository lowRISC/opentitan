# Registers

The revocation bitmap is not a register but a memory window on the `revbm` interface; see the
[Theory of Operation](theory_of_operation.md#meta-sram-address-map).

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/cheriot/data/cheriot.hjson -->
## Summary

| Name                                | Offset   |   Length | Description         |
|:------------------------------------|:---------|---------:|:--------------------|
| cheriot.[`ALERT_TEST`](#alert_test) | 0x0      |        4 | Alert Test Register |

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


<!-- END CMDGEN -->
