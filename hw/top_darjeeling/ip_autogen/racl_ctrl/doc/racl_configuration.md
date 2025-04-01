# RACL Configuration

<!-- BEGIN CMDGEN util/raclgen.py --doc ./hw/top_darjeeling/data/autogen/top_darjeeling.gen.hjson -->
## RACL groups

### RACL group: Null

| Policy Name   |   Index | Description                                                       |
|:--------------|--------:|:------------------------------------------------------------------|
| ALL_RD_WR     |       0 | Standard policies allowing all roles to access a register         |
| ROT_PRIVATE   |       1 | Standard policies allowing only the ROT role to access a register |
| SOC_ROT       |       2 | Custom policy                                                     |


## RACL configuration

### RACL configuration for `mbx0` and interface `soc`

- IP: mbx
- Instance base address: 0x1465000
- RACL group: Null


| Name                             | Offset   | Address   | Width   | Policy        | ROT   | ROLE1   | SOC   |
|:---------------------------------|:---------|:----------|:--------|:--------------|:------|:--------|:------|
| mbx0.soc.`SOC_CONTROL`           | 0x8      | 0x1465008 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx0.soc.`SOC_STATUS`            | 0xc      | 0x146500c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx0.soc.`WDATA`                 | 0x10     | 0x1465010 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx0.soc.`RDATA`                 | 0x14     | 0x1465014 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx0.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x1465018 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx0.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x146501c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |

### RACL configuration for `mbx1` and interface `soc`

- IP: mbx
- Instance base address: 0x1465100
- RACL group: Null


| Name                             | Offset   | Address   | Width   | Policy        | ROT   | ROLE1   | SOC   |
|:---------------------------------|:---------|:----------|:--------|:--------------|:------|:--------|:------|
| mbx1.soc.`SOC_CONTROL`           | 0x8      | 0x1465108 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx1.soc.`SOC_STATUS`            | 0xc      | 0x146510c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx1.soc.`WDATA`                 | 0x10     | 0x1465110 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx1.soc.`RDATA`                 | 0x14     | 0x1465114 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx1.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x1465118 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx1.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x146511c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |

### RACL configuration for `mbx2` and interface `soc`

- IP: mbx
- Instance base address: 0x1465200
- RACL group: Null


| Name                             | Offset   | Address   | Width   | Policy        | ROT   | ROLE1   | SOC   |
|:---------------------------------|:---------|:----------|:--------|:--------------|:------|:--------|:------|
| mbx2.soc.`SOC_CONTROL`           | 0x8      | 0x1465208 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx2.soc.`SOC_STATUS`            | 0xc      | 0x146520c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx2.soc.`WDATA`                 | 0x10     | 0x1465210 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx2.soc.`RDATA`                 | 0x14     | 0x1465214 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx2.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x1465218 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx2.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x146521c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |

### RACL configuration for `mbx3` and interface `soc`

- IP: mbx
- Instance base address: 0x1465300
- RACL group: Null


| Name                             | Offset   | Address   | Width   | Policy        | ROT   | ROLE1   | SOC   |
|:---------------------------------|:---------|:----------|:--------|:--------------|:------|:--------|:------|
| mbx3.soc.`SOC_CONTROL`           | 0x8      | 0x1465308 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx3.soc.`SOC_STATUS`            | 0xc      | 0x146530c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx3.soc.`WDATA`                 | 0x10     | 0x1465310 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx3.soc.`RDATA`                 | 0x14     | 0x1465314 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx3.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x1465318 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx3.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x146531c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |

### RACL configuration for `mbx4` and interface `soc`

- IP: mbx
- Instance base address: 0x1465400
- RACL group: Null


| Name                             | Offset   | Address   | Width   | Policy        | ROT   | ROLE1   | SOC   |
|:---------------------------------|:---------|:----------|:--------|:--------------|:------|:--------|:------|
| mbx4.soc.`SOC_CONTROL`           | 0x8      | 0x1465408 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx4.soc.`SOC_STATUS`            | 0xc      | 0x146540c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx4.soc.`WDATA`                 | 0x10     | 0x1465410 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx4.soc.`RDATA`                 | 0x14     | 0x1465414 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx4.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x1465418 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx4.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x146541c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |

### RACL configuration for `mbx5` and interface `soc`

- IP: mbx
- Instance base address: 0x1465500
- RACL group: Null


| Name                             | Offset   | Address   | Width   | Policy        | ROT   | ROLE1   | SOC   |
|:---------------------------------|:---------|:----------|:--------|:--------------|:------|:--------|:------|
| mbx5.soc.`SOC_CONTROL`           | 0x8      | 0x1465508 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx5.soc.`SOC_STATUS`            | 0xc      | 0x146550c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx5.soc.`WDATA`                 | 0x10     | 0x1465510 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx5.soc.`RDATA`                 | 0x14     | 0x1465514 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx5.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x1465518 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx5.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x146551c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |

### RACL configuration for `mbx6` and interface `soc`

- IP: mbx
- Instance base address: 0x1496000
- RACL group: Null


| Name                             | Offset   | Address   | Width   | Policy        | ROT   | ROLE1   | SOC   |
|:---------------------------------|:---------|:----------|:--------|:--------------|:------|:--------|:------|
| mbx6.soc.`SOC_CONTROL`           | 0x8      | 0x1496008 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx6.soc.`SOC_STATUS`            | 0xc      | 0x149600c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx6.soc.`WDATA`                 | 0x10     | 0x1496010 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx6.soc.`RDATA`                 | 0x14     | 0x1496014 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx6.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x1496018 | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx6.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x149601c | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |

### RACL configuration for `mbx_jtag` and interface `soc`

- IP: mbx
- Instance base address: 0x2200
- RACL group: Null


| Name                                 | Offset   | Address   | Width   | Policy        | ROT   | ROLE1   | SOC   |
|:-------------------------------------|:---------|:----------|:--------|:--------------|:------|:--------|:------|
| mbx_jtag.soc.`SOC_CONTROL`           | 0x8      | 0x2208    | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx_jtag.soc.`SOC_STATUS`            | 0xc      | 0x220c    | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx_jtag.soc.`WDATA`                 | 0x10     | 0x2210    | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx_jtag.soc.`RDATA`                 | 0x14     | 0x2214    | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx_jtag.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x2218    | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |
| mbx_jtag.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x221c    | 0x4     | 0 (ALL_RD_WR) | R / W | R / W   | R / W |

### RACL configuration for `mbx_pcie0` and interface `soc`

- IP: mbx
- Instance base address: 0x1460100
- RACL group: Null


| Name                                  | Offset   | Address   | Width   | Policy      | ROT   | ROLE1   | SOC   |
|:--------------------------------------|:---------|:----------|:--------|:------------|:------|:--------|:------|
| mbx_pcie0.soc.`SOC_CONTROL`           | 0x8      | 0x1460108 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie0.soc.`SOC_STATUS`            | 0xc      | 0x146010c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie0.soc.`WDATA`                 | 0x10     | 0x1460110 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie0.soc.`RDATA`                 | 0x14     | 0x1460114 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie0.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x1460118 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie0.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x146011c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |

### RACL configuration for `mbx_pcie1` and interface `soc`

- IP: mbx
- Instance base address: 0x1460200
- RACL group: Null


| Name                                  | Offset   | Address   | Width   | Policy      | ROT   | ROLE1   | SOC   |
|:--------------------------------------|:---------|:----------|:--------|:------------|:------|:--------|:------|
| mbx_pcie1.soc.`SOC_CONTROL`           | 0x8      | 0x1460208 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie1.soc.`SOC_STATUS`            | 0xc      | 0x146020c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie1.soc.`WDATA`                 | 0x10     | 0x1460210 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie1.soc.`RDATA`                 | 0x14     | 0x1460214 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie1.soc.`SOC_DOE_INTR_MSG_ADDR` | 0x18     | 0x1460218 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| mbx_pcie1.soc.`SOC_DOE_INTR_MSG_DATA` | 0x1c     | 0x146021c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |

### RACL configuration for `ac_range_check` and interface `null`

- IP: ac_range_check
- Instance base address: 0x1464000
- RACL group: Null


| Name                                           | Offset   | Address   | Width   | Policy      | ROT   | ROLE1   | SOC   |
|:-----------------------------------------------|:---------|:----------|:--------|:------------|:------|:--------|:------|
| ac_range_check.`INTR_STATE`                    | 0x0      | 0x1464000 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`INTR_ENABLE`                   | 0x4      | 0x1464004 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`INTR_TEST`                     | 0x8      | 0x1464008 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`ALERT_TEST`                    | 0xc      | 0x146400c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`ALERT_STATUS`                  | 0x10     | 0x1464010 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`LOG_CONFIG`                    | 0x14     | 0x1464014 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`LOG_STATUS`                    | 0x18     | 0x1464018 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`LOG_ADDRESS`                   | 0x1c     | 0x146401c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_0`                | 0x20     | 0x1464020 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_1`                | 0x24     | 0x1464024 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_2`                | 0x28     | 0x1464028 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_3`                | 0x2c     | 0x146402c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_4`                | 0x30     | 0x1464030 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_5`                | 0x34     | 0x1464034 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_6`                | 0x38     | 0x1464038 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_7`                | 0x3c     | 0x146403c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_8`                | 0x40     | 0x1464040 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_9`                | 0x44     | 0x1464044 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_10`               | 0x48     | 0x1464048 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_11`               | 0x4c     | 0x146404c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_12`               | 0x50     | 0x1464050 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_13`               | 0x54     | 0x1464054 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_14`               | 0x58     | 0x1464058 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_15`               | 0x5c     | 0x146405c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_16`               | 0x60     | 0x1464060 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_17`               | 0x64     | 0x1464064 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_18`               | 0x68     | 0x1464068 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_19`               | 0x6c     | 0x146406c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_20`               | 0x70     | 0x1464070 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_21`               | 0x74     | 0x1464074 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_22`               | 0x78     | 0x1464078 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_23`               | 0x7c     | 0x146407c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_24`               | 0x80     | 0x1464080 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_25`               | 0x84     | 0x1464084 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_26`               | 0x88     | 0x1464088 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_27`               | 0x8c     | 0x146408c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_28`               | 0x90     | 0x1464090 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_29`               | 0x94     | 0x1464094 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_30`               | 0x98     | 0x1464098 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_REGWEN_31`               | 0x9c     | 0x146409c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_0`                  | 0xa0     | 0x14640a0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_1`                  | 0xa4     | 0x14640a4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_2`                  | 0xa8     | 0x14640a8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_3`                  | 0xac     | 0x14640ac | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_4`                  | 0xb0     | 0x14640b0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_5`                  | 0xb4     | 0x14640b4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_6`                  | 0xb8     | 0x14640b8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_7`                  | 0xbc     | 0x14640bc | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_8`                  | 0xc0     | 0x14640c0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_9`                  | 0xc4     | 0x14640c4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_10`                 | 0xc8     | 0x14640c8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_11`                 | 0xcc     | 0x14640cc | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_12`                 | 0xd0     | 0x14640d0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_13`                 | 0xd4     | 0x14640d4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_14`                 | 0xd8     | 0x14640d8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_15`                 | 0xdc     | 0x14640dc | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_16`                 | 0xe0     | 0x14640e0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_17`                 | 0xe4     | 0x14640e4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_18`                 | 0xe8     | 0x14640e8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_19`                 | 0xec     | 0x14640ec | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_20`                 | 0xf0     | 0x14640f0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_21`                 | 0xf4     | 0x14640f4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_22`                 | 0xf8     | 0x14640f8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_23`                 | 0xfc     | 0x14640fc | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_24`                 | 0x100    | 0x1464100 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_25`                 | 0x104    | 0x1464104 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_26`                 | 0x108    | 0x1464108 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_27`                 | 0x10c    | 0x146410c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_28`                 | 0x110    | 0x1464110 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_29`                 | 0x114    | 0x1464114 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_30`                 | 0x118    | 0x1464118 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_BASE_31`                 | 0x11c    | 0x146411c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_0`                 | 0x120    | 0x1464120 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_1`                 | 0x124    | 0x1464124 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_2`                 | 0x128    | 0x1464128 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_3`                 | 0x12c    | 0x146412c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_4`                 | 0x130    | 0x1464130 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_5`                 | 0x134    | 0x1464134 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_6`                 | 0x138    | 0x1464138 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_7`                 | 0x13c    | 0x146413c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_8`                 | 0x140    | 0x1464140 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_9`                 | 0x144    | 0x1464144 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_10`                | 0x148    | 0x1464148 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_11`                | 0x14c    | 0x146414c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_12`                | 0x150    | 0x1464150 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_13`                | 0x154    | 0x1464154 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_14`                | 0x158    | 0x1464158 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_15`                | 0x15c    | 0x146415c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_16`                | 0x160    | 0x1464160 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_17`                | 0x164    | 0x1464164 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_18`                | 0x168    | 0x1464168 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_19`                | 0x16c    | 0x146416c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_20`                | 0x170    | 0x1464170 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_21`                | 0x174    | 0x1464174 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_22`                | 0x178    | 0x1464178 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_23`                | 0x17c    | 0x146417c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_24`                | 0x180    | 0x1464180 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_25`                | 0x184    | 0x1464184 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_26`                | 0x188    | 0x1464188 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_27`                | 0x18c    | 0x146418c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_28`                | 0x190    | 0x1464190 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_29`                | 0x194    | 0x1464194 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_30`                | 0x198    | 0x1464198 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_LIMIT_31`                | 0x19c    | 0x146419c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_0`                  | 0x1a0    | 0x14641a0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_1`                  | 0x1a4    | 0x14641a4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_2`                  | 0x1a8    | 0x14641a8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_3`                  | 0x1ac    | 0x14641ac | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_4`                  | 0x1b0    | 0x14641b0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_5`                  | 0x1b4    | 0x14641b4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_6`                  | 0x1b8    | 0x14641b8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_7`                  | 0x1bc    | 0x14641bc | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_8`                  | 0x1c0    | 0x14641c0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_9`                  | 0x1c4    | 0x14641c4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_10`                 | 0x1c8    | 0x14641c8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_11`                 | 0x1cc    | 0x14641cc | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_12`                 | 0x1d0    | 0x14641d0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_13`                 | 0x1d4    | 0x14641d4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_14`                 | 0x1d8    | 0x14641d8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_15`                 | 0x1dc    | 0x14641dc | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_16`                 | 0x1e0    | 0x14641e0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_17`                 | 0x1e4    | 0x14641e4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_18`                 | 0x1e8    | 0x14641e8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_19`                 | 0x1ec    | 0x14641ec | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_20`                 | 0x1f0    | 0x14641f0 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_21`                 | 0x1f4    | 0x14641f4 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_22`                 | 0x1f8    | 0x14641f8 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_23`                 | 0x1fc    | 0x14641fc | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_24`                 | 0x200    | 0x1464200 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_25`                 | 0x204    | 0x1464204 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_26`                 | 0x208    | 0x1464208 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_27`                 | 0x20c    | 0x146420c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_28`                 | 0x210    | 0x1464210 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_29`                 | 0x214    | 0x1464214 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_30`                 | 0x218    | 0x1464218 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_ATTR_31`                 | 0x21c    | 0x146421c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_0`  | 0x220    | 0x1464220 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_1`  | 0x224    | 0x1464224 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_2`  | 0x228    | 0x1464228 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_3`  | 0x22c    | 0x146422c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_4`  | 0x230    | 0x1464230 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_5`  | 0x234    | 0x1464234 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_6`  | 0x238    | 0x1464238 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_7`  | 0x23c    | 0x146423c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_8`  | 0x240    | 0x1464240 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_9`  | 0x244    | 0x1464244 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_10` | 0x248    | 0x1464248 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_11` | 0x24c    | 0x146424c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_12` | 0x250    | 0x1464250 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_13` | 0x254    | 0x1464254 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_14` | 0x258    | 0x1464258 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_15` | 0x25c    | 0x146425c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_16` | 0x260    | 0x1464260 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_17` | 0x264    | 0x1464264 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_18` | 0x268    | 0x1464268 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_19` | 0x26c    | 0x146426c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_20` | 0x270    | 0x1464270 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_21` | 0x274    | 0x1464274 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_22` | 0x278    | 0x1464278 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_23` | 0x27c    | 0x146427c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_24` | 0x280    | 0x1464280 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_25` | 0x284    | 0x1464284 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_26` | 0x288    | 0x1464288 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_27` | 0x28c    | 0x146428c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_28` | 0x290    | 0x1464290 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_29` | 0x294    | 0x1464294 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_30` | 0x298    | 0x1464298 | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |
| ac_range_check.`RANGE_RACL_POLICY_SHADOWED_31` | 0x29c    | 0x146429c | 0x4     | 2 (SOC_ROT) | R / W | - / -   | R / W |


<!-- END CMDGEN -->
