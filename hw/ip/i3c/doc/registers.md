# Registers

<!-- BEGIN CMDGEN util/regtool.py -d ./hw/ip/i3c/data/i3c.hjson -->
## Summary

| Name                                                                        | Offset   |   Length | Description                                                                        |
|:----------------------------------------------------------------------------|:---------|---------:|:-----------------------------------------------------------------------------------|
| i3c.[`INTR_STATE`](#intr_state)                                             | 0x0      |        4 | Interrupt State Register                                                           |
| i3c.[`INTR_ENABLE`](#intr_enable)                                           | 0x4      |        4 | Interrupt Enable Register                                                          |
| i3c.[`INTR_TEST`](#intr_test)                                               | 0x8      |        4 | Interrupt Test Register                                                            |
| i3c.[`ALERT_TEST`](#alert_test)                                             | 0xc      |        4 | Alert Test Register                                                                |
| i3c.[`INFO`](#info)                                                         | 0x10     |        4 | IP block information, allowing software to adapt dynamically.                      |
| i3c.[`CTRL_STATUS`](#ctrl_status)                                           | 0x14     |        4 | Controller-side Status register.                                                   |
| i3c.[`CTRL_ERROR`](#ctrl_error)                                             | 0x18     |        4 | Controller Error counts.                                                           |
| i3c.[`TARG_CONTROL`](#targ_control)                                         | 0x1c     |        4 | Target Control register.                                                           |
| i3c.[`TARG_STATUS`](#targ_status)                                           | 0x20     |        4 | Target-side Status register                                                        |
| i3c.[`TARG_SINK_CONTROL`](#targ_sink_control)                               | 0x24     |        4 | Target data sink control.                                                          |
| i3c.[`TARG_SINK_STATUS`](#targ_sink_status)                                 | 0x28     |        4 | Target data sink status.                                                           |
| i3c.[`RESET_DET_CTRL`](#reset_det_ctrl)                                     | 0x2c     |        4 | Reset detector control.                                                            |
| i3c.[`RESET_DET_STATUS`](#reset_det_status)                                 | 0x30     |        4 | Reset detector status.                                                             |
| i3c.[`CTRL_TIME_SP`](#ctrl_time_sp)                                         | 0x34     |        4 | Controller Timing Parameters for Start and stoP.                                   |
| i3c.[`CTRL_TIME_OD`](#ctrl_time_od)                                         | 0x38     |        4 | Controller Timing Parameters for Open Drain signaling.                             |
| i3c.[`CTRL_TIME_PP`](#ctrl_time_pp)                                         | 0x3c     |        4 | Controller Timing Parameters for SDR0/HDR-DDR Push-Pull SCL High signaling.        |
| i3c.[`CTRL_TIME_SDR0`](#ctrl_time_sdr0)                                     | 0x40     |        4 | Controller Timing Parameters for SDR0/HDR-DDR Push-Pull SCL Low signaling.         |
| i3c.[`CTRL_TIME_SDR1`](#ctrl_time_sdr1)                                     | 0x44     |        4 | Controller Timing Parameters for SDR1 Push-Pull SCL Low signaling.                 |
| i3c.[`CTRL_TIME_SDR2`](#ctrl_time_sdr2)                                     | 0x48     |        4 | Controller Timing Parameters for SDR2 Push-Pull SCL Low signaling.                 |
| i3c.[`CTRL_TIME_SDR3`](#ctrl_time_sdr3)                                     | 0x4c     |        4 | Controller Timing Parameters for SDR3 Push-Pull SCL Low signaling.                 |
| i3c.[`CTRL_TIME_SDR4`](#ctrl_time_sdr4)                                     | 0x50     |        4 | Controller Timing Parameters for SDR4 Push-Pull SCL Low signaling.                 |
| i3c.[`CTRL_TIME_FMP`](#ctrl_time_fmp)                                       | 0x54     |        4 | Controller Timing Parameters for I2C Fast Mode Plus signaling.                     |
| i3c.[`CTRL_TIME_FM`](#ctrl_time_fm)                                         | 0x58     |        4 | Controller Timing Parameters for I2C Fast Mode signaling.                          |
| i3c.[`INTERVAL_TIME0`](#interval_time0)                                     | 0x5c     |        4 | Interval Timers 0 register.                                                        |
| i3c.[`INTERVAL_TIME1`](#interval_time1)                                     | 0x60     |        4 | Interval Timers 1 register.                                                        |
| i3c.[`PHY_CONFIG`](#phy_config)                                             | 0x64     |        4 | PHY configuration                                                                  |
| i3c.[`BLOCKED_ADDR`](#blocked_addr)                                         | 0x68     |        4 | Blocked target addresses.                                                          |
| i3c.[`BUFFER_CTRL`](#buffer_ctrl)                                           | 0x6c     |        4 | Buffer control                                                                     |
| i3c.[`BUFFER_STATUS`](#buffer_status)                                       | 0x70     |        4 | Buffer status                                                                      |
| i3c.[`CTRL_TXBUF_CONFIG`](#ctrl_txbuf_config)                               | 0x74     |        4 | Controller TX Buffer Configuration                                                 |
| i3c.[`CTRL_TXBUF_STATE`](#ctrl_txbuf_state)                                 | 0x78     |        4 | Controller TX Buffer State.                                                        |
| i3c.[`CTRL_RXBUF_CONFIG`](#ctrl_rxbuf_config)                               | 0x7c     |        4 | Controller RX Buffer Configuration                                                 |
| i3c.[`CTRL_RXBUF_STATE`](#ctrl_rxbuf_state)                                 | 0x80     |        4 | Controller RX Buffer State.                                                        |
| i3c.[`COMMAND_QUEUE_CONFIG`](#command_queue_config)                         | 0x84     |        4 | Command Queue Configuration.                                                       |
| i3c.[`COMMAND_QUEUE_STATE`](#command_queue_state)                           | 0x88     |        4 | Command Queue State.                                                               |
| i3c.[`RESPONSE_QUEUE_CONFIG`](#response_queue_config)                       | 0x8c     |        4 | Response Queue Configuration.                                                      |
| i3c.[`RESPONSE_QUEUE_STATE`](#response_queue_state)                         | 0x90     |        4 | Response Queue State.                                                              |
| i3c.[`IBI_CONFIG`](#ibi_config)                                             | 0x94     |        4 | In-Band Interrupt Queue Configuration.                                             |
| i3c.[`IBI_STATE`](#ibi_state)                                               | 0x98     |        4 | In-Band Interrupt Queue State.                                                     |
| i3c.[`IBI_STAT_CONFIG`](#ibi_stat_config)                                   | 0x9c     |        4 | In-Band Status Descriptor FIFO Configuration.                                      |
| i3c.[`IBI_STAT_STATE`](#ibi_stat_state)                                     | 0xa0     |        4 | In-Band Status Descriptor FIFO State.                                              |
| i3c.[`TARG_TXBUF_CONFIG_0`](#targ_txbuf_config)                             | 0xa4     |        4 | Target TX Buffer Configuration.                                                    |
| i3c.[`TARG_TXBUF_CONFIG_1`](#targ_txbuf_config)                             | 0xa8     |        4 | Target TX Buffer Configuration.                                                    |
| i3c.[`TARG_TXBUF_CONFIG_2`](#targ_txbuf_config)                             | 0xac     |        4 | Target TX Buffer Configuration.                                                    |
| i3c.[`TARG_TXBUF_CONFIG_3`](#targ_txbuf_config)                             | 0xb0     |        4 | Target TX Buffer Configuration.                                                    |
| i3c.[`TARG_TXBUF_STATE_0`](#targ_txbuf_state)                               | 0xb4     |        4 | Target 0 TX Buffer State.                                                          |
| i3c.[`TARG_TXBUF_STATE_1`](#targ_txbuf_state)                               | 0xb8     |        4 | Target 0 TX Buffer State.                                                          |
| i3c.[`TARG_TXBUF_STATE_2`](#targ_txbuf_state)                               | 0xbc     |        4 | Target 0 TX Buffer State.                                                          |
| i3c.[`TARG_TXBUF_STATE_3`](#targ_txbuf_state)                               | 0xc0     |        4 | Target 0 TX Buffer State.                                                          |
| i3c.[`TARG_RXBUF_CONFIG`](#targ_rxbuf_config)                               | 0xc4     |        4 | Target RX Buffer Configuration                                                     |
| i3c.[`TARG_RXBUF_STATE`](#targ_rxbuf_state)                                 | 0xc8     |        4 | Target RX Buffer State.                                                            |
| i3c.[`TARG_IBI_CONFIG`](#targ_ibi_config)                                   | 0xcc     |        4 | Target In-Band Interrupt Payload Queue Configuration                               |
| i3c.[`TARG_IBI_STATE`](#targ_ibi_state)                                     | 0xd0     |        4 | Target In-Band Interrupt Payload Queue State.                                      |
| i3c.[`TARG_TXDESC_CONFIG_0`](#targ_txdesc_config)                           | 0xd4     |        4 | Target Transmission Descriptor Queue Configuration.                                |
| i3c.[`TARG_TXDESC_CONFIG_1`](#targ_txdesc_config)                           | 0xd8     |        4 | Target Transmission Descriptor Queue Configuration.                                |
| i3c.[`TARG_TXDESC_CONFIG_2`](#targ_txdesc_config)                           | 0xdc     |        4 | Target Transmission Descriptor Queue Configuration.                                |
| i3c.[`TARG_TXDESC_CONFIG_3`](#targ_txdesc_config)                           | 0xe0     |        4 | Target Transmission Descriptor Queue Configuration.                                |
| i3c.[`TARG_TXDESC_STATE_0`](#targ_txdesc_state)                             | 0xe4     |        4 | Target Transmission Descriptor Queue State.                                        |
| i3c.[`TARG_TXDESC_STATE_1`](#targ_txdesc_state)                             | 0xe8     |        4 | Target Transmission Descriptor Queue State.                                        |
| i3c.[`TARG_TXDESC_STATE_2`](#targ_txdesc_state)                             | 0xec     |        4 | Target Transmission Descriptor Queue State.                                        |
| i3c.[`TARG_TXDESC_STATE_3`](#targ_txdesc_state)                             | 0xf0     |        4 | Target Transmission Descriptor Queue State.                                        |
| i3c.[`TARG_RXDESC_CONFIG`](#targ_rxdesc_config)                             | 0xf4     |        4 | Target Reception Descriptor Queue Configuration.                                   |
| i3c.[`TARG_RXDESC_STATE`](#targ_rxdesc_state)                               | 0xf8     |        4 | Target Reception Descriptor Queue State.                                           |
| i3c.[`TARG_IBIDESC_CONFIG`](#targ_ibidesc_config)                           | 0xfc     |        4 | Target In-Band Interrupt Descriptor Queue Configuration.                           |
| i3c.[`TARG_IBIDESC_STATE`](#targ_ibidesc_state)                             | 0x100    |        4 | Target In-Band Interrupt Descriptor Queue State.                                   |
| i3c.[`TARG_ASYNC_CONFIG`](#targ_async_config)                               | 0x104    |        4 | Target Asynchronous Event Queue Configuration.                                     |
| i3c.[`TARG_ASYNC_STATE`](#targ_async_state)                                 | 0x108    |        4 | Target Asynchronous Event Queue State.                                             |
| i3c.[`HCI_VERSION`](#hci_version)                                           | 0x180    |        4 | HCI Version.                                                                       |
| i3c.[`HC_CONTROL`](#hc_control)                                             | 0x184    |        4 | Host Controller Control.                                                           |
| i3c.[`CONTROLLER_DEVICE_ADDR`](#controller_device_addr)                     | 0x188    |        4 | Controller Device Address.                                                         |
| i3c.[`HC_CAPABILITIES`](#hc_capabilities)                                   | 0x18c    |        4 | Host Controller Capabilities.                                                      |
| i3c.[`RESET_CONTROL`](#reset_control)                                       | 0x190    |        4 | Reset Control.                                                                     |
| i3c.[`PRESENT_STATE`](#present_state)                                       | 0x194    |        4 | Present State.                                                                     |
| i3c.[`INTR_STATUS`](#intr_status)                                           | 0x1a0    |        4 | Interrupt Status.                                                                  |
| i3c.[`INTR_STATUS_ENABLE`](#intr_status_enable)                             | 0x1a4    |        4 | Interrupt Status Enable.                                                           |
| i3c.[`INTR_SIGNAL_ENABLE`](#intr_signal_enable)                             | 0x1a8    |        4 | Interrupt Signal Enable.                                                           |
| i3c.[`INTR_FORCE`](#intr_force)                                             | 0x1ac    |        4 | Interrupt Force.                                                                   |
| i3c.[`DAT_SECTION_OFFSET`](#dat_section_offset)                             | 0x1b0    |        4 | Device Address Table Section Offset.                                               |
| i3c.[`DCT_SECTION_OFFSET`](#dct_section_offset)                             | 0x1b4    |        4 | Device Characteristics Table Section Offset.                                       |
| i3c.[`RING_HEADERS_SECTION_OFFSET`](#ring_headers_section_offset)           | 0x1b8    |        4 | Ring Headers Section Offset.                                                       |
| i3c.[`PIO_SECTION_OFFSET`](#pio_section_offset)                             | 0x1bc    |        4 | PIO Section Offset.                                                                |
| i3c.[`EXT_CAPS_SECTION_OFFSET`](#ext_caps_section_offset)                   | 0x1c0    |        4 | Extended Capabilities Section Offset.                                              |
| i3c.[`INT_CTRL_CMDS_EN`](#int_ctrl_cmds_en)                                 | 0x1cc    |        4 | Internal Control Command Subtype Support.                                          |
| i3c.[`IBI_NOTIFY_CTRL`](#ibi_notify_ctrl)                                   | 0x1d8    |        4 | IBI Notify Control.                                                                |
| i3c.[`IBI_DATA_ABORT_CTRL`](#ibi_data_abort_ctrl)                           | 0x1dc    |        4 | IBI Data Abort Control.                                                            |
| i3c.[`DEV_CTX_BASE_LO`](#dev_ctx_base_lo)                                   | 0x1e0    |        4 | Device Context Base Address Low.                                                   |
| i3c.[`DEV_CTX_BASE_HI`](#dev_ctx_base_hi)                                   | 0x1e4    |        4 | Device Context Base Address High.                                                  |
| i3c.[`DEV_CTX_SG`](#dev_ctx_sg)                                             | 0x1e8    |        4 | Device Context Scatter-Gather Support.                                             |
| i3c.[`HCI_PORTS`](#hci_ports)                                               | 0x200    |       16 | HCI ports, occupying successive word addresses:                                    |
| i3c.[`QUEUE_THLD_CTRL`](#queue_thld_ctrl)                                   | 0x210    |        4 | Queue Threshold Control.                                                           |
| i3c.[`DATA_BUFFER_THLD_CTRL`](#data_buffer_thld_ctrl)                       | 0x214    |        4 | Transfer Data Buffer Threshold Control.                                            |
| i3c.[`QUEUE_SIZE`](#queue_size)                                             | 0x218    |        4 | Queue Size.                                                                        |
| i3c.[`ALT_QUEUE_SIZE`](#alt_queue_size)                                     | 0x21c    |        4 | Alternate Queue Size.                                                              |
| i3c.[`PIO_INTR_STATUS`](#pio_intr_status)                                   | 0x220    |        4 | PIO Interrupt Status.                                                              |
| i3c.[`PIO_INTR_STATUS_ENABLE`](#pio_intr_status_enable)                     | 0x224    |        4 | PIO Interrupt Status Enable.                                                       |
| i3c.[`PIO_INTR_SIGNAL_ENABLE`](#pio_intr_signal_enable)                     | 0x228    |        4 | PIO Interrupt Signal Enable.                                                       |
| i3c.[`PIO_INTR_FORCE`](#pio_intr_force)                                     | 0x22c    |        4 | PIO Interrupt Force.                                                               |
| i3c.[`PIO_CONTROL`](#pio_control)                                           | 0x230    |        4 | PIO Control.                                                                       |
| i3c.[`ID_EXTCAP_HEADER`](#id_extcap_header)                                 | 0x2a0    |        4 | Hardware Identification Extended Capability Header                                 |
| i3c.[`COMP_MANUFACTURER`](#comp_manufacturer)                               | 0x2a4    |        4 | Component Manufacturer.                                                            |
| i3c.[`COMP_VERSION`](#comp_version)                                         | 0x2a8    |        4 | Component Version.                                                                 |
| i3c.[`COMP_TYPE`](#comp_type)                                               | 0x2ac    |        4 | Component Type.                                                                    |
| i3c.[`CTRL_CFG_EXTCAP_HEADER`](#ctrl_cfg_extcap_header)                     | 0x2b0    |        4 | Controller Config Extended Capability Header                                       |
| i3c.[`CONTROLLER_CONFIG`](#controller_config)                               | 0x2b4    |        4 | Controller Config.                                                                 |
| i3c.[`DBR_EXTCAP_HEADER`](#dbr_extcap_header)                               | 0x2b8    |        4 | Dead Bus Recovery Extended Capability Header                                       |
| i3c.[`DBR_ENGAGE`](#dbr_engage)                                             | 0x2bc    |        4 | Dead Bus Recovery Engage.                                                          |
| i3c.[`DEBUG_EXTCAP_HEADER`](#debug_extcap_header)                           | 0x2c0    |        4 | Debug Specific Extended Capability Header                                          |
| i3c.[`QUEUE_STATUS_LEVEL`](#queue_status_level)                             | 0x2c4    |        4 | Queue Status Level                                                                 |
| i3c.[`DATA_BUFFER_STATUS_LEVEL`](#data_buffer_status_level)                 | 0x2c8    |        4 | Data Buffer Status Level                                                           |
| i3c.[`PRESENT_STATE_DEBUG`](#present_state_debug)                           | 0x2cc    |        4 | Present State Debug                                                                |
| i3c.[`MX_ERROR_COUNTERS`](#mx_error_counters)                               | 0x2d0    |        4 | Controller Error Counters.                                                         |
| i3c.[`SCHED_CMDS_DEBUG`](#sched_cmds_debug)                                 | 0x2d4    |        4 | Scheduled Commands Debug                                                           |
| i3c.[`STBY_CR_EXTCAP_HEADER`](#stby_cr_extcap_header)                       | 0x2d8    |        4 | Standby Controller Extended Capability Header                                      |
| i3c.[`STBY_CR_CONTROL`](#stby_cr_control)                                   | 0x2dc    |        4 | Standby Controller Control                                                         |
| i3c.[`STBY_CR_DEVICE_ADDR`](#stby_cr_device_addr)                           | 0x2e0    |        4 | Standby Controller Device Address                                                  |
| i3c.[`STBY_CR_CAPABILITIES`](#stby_cr_capabilities)                         | 0x2e4    |        4 | Standby Controller Capabilities                                                    |
| i3c.[`STBY_CR_STATUS`](#stby_cr_status)                                     | 0x2ec    |        4 | Standby Controller Status                                                          |
| i3c.[`STBY_CR_DEVICE_CHAR`](#stby_cr_device_char)                           | 0x2f0    |        4 | Standby Controller Device Characteristics                                          |
| i3c.[`STBY_CR_DEVICE_PID_LO`](#stby_cr_device_pid_lo)                       | 0x2f4    |        4 | Standby Controller PID Low                                                         |
| i3c.[`STBY_CR_INTR_STATUS`](#stby_cr_intr_status)                           | 0x2f8    |        4 | Standby Controller Interrupt Status                                                |
| i3c.[`STBY_CR_INTR_SIGNAL_ENABLE`](#stby_cr_intr_signal_enable)             | 0x300    |        4 | Standby Controller Interrupt Signal Enable                                         |
| i3c.[`STBY_CR_INTR_FORCE`](#stby_cr_intr_force)                             | 0x304    |        4 | Standby Controller Interrupt Force                                                 |
| i3c.[`STBY_CR_CCC_CONFIG_GETCAPS`](#stby_cr_ccc_config_getcaps)             | 0x308    |        4 | Standby Controller CCC Auto-Response Config Get Capabilities                       |
| i3c.[`STBY_CR_CCC_CONFIG_RSTACT_PARAMS`](#stby_cr_ccc_config_rstact_params) | 0x30c    |        4 | Standby Controller CCC Auto-Response Config Target Reset Action                    |
| i3c.[`TTI_EXTCAP_HEADER`](#tti_extcap_header)                               | 0x310    |        4 | Target Transaction Interface Extended Capability Header                            |
| i3c.[`TARG_INTR_STATUS`](#targ_intr_status)                                 | 0x314    |        4 | Target Interrupt Status.                                                           |
| i3c.[`TARG_INTR_STATUS_ENABLE`](#targ_intr_status_enable)                   | 0x318    |        4 | Target Interrupt Status Enable.                                                    |
| i3c.[`TARG_INTR_SIGNAL_ENABLE`](#targ_intr_signal_enable)                   | 0x31c    |        4 | Target Interrupt Signal Enable.                                                    |
| i3c.[`TARG_INTR_FORCE`](#targ_intr_force)                                   | 0x320    |        4 | Target Interrupt Force.                                                            |
| i3c.[`TARG_PIO_CONTROL`](#targ_pio_control)                                 | 0x324    |        4 | Target PIO mode Control register.                                                  |
| i3c.[`TARG_ASYNC_EVT_CONTROL`](#targ_async_evt_control)                     | 0x328    |        4 | Target Asynchronous Event Queue Control.                                           |
| i3c.[`TARG_ERROR`](#targ_error)                                             | 0x32c    |        4 | Target Error counts.                                                               |
| i3c.[`TARG_QUEUE_THLD_CTRL`](#targ_queue_thld_ctrl)                         | 0x330    |        4 | Target-side control register for setting queue interrupt thresholds.               |
| i3c.[`TARG_QUEUE_STATUS_LEVEL`](#targ_queue_status_level)                   | 0x334    |        4 | Target-side queue levels.                                                          |
| i3c.[`TARG_BUF_THLD_CTRL`](#targ_buf_thld_ctrl)                             | 0x338    |        4 | Target-side control register for setting buffer interrupt thresholds.              |
| i3c.[`TARG_BUF_STATUS_LEVEL`](#targ_buf_status_level)                       | 0x33c    |        4 | Target-side data buffer levels.                                                    |
| i3c.[`TARG_RW_LEN_0`](#targ_rw_len)                                         | 0x340    |        4 | Target Read/Write Length.                                                          |
| i3c.[`TARG_RW_LEN_1`](#targ_rw_len)                                         | 0x344    |        4 | Target Read/Write Length.                                                          |
| i3c.[`TARG_RW_LEN_2`](#targ_rw_len)                                         | 0x348    |        4 | Target Read/Write Length.                                                          |
| i3c.[`TARG_RW_LEN_3`](#targ_rw_len)                                         | 0x34c    |        4 | Target Read/Write Length.                                                          |
| i3c.[`TARG_IBI_LEN`](#targ_ibi_len)                                         | 0x350    |        4 | Target IBI payload Length.                                                         |
| i3c.[`TARG_EVENT_ENABLE_0`](#targ_event_enable)                             | 0x354    |        4 | Target Event enables.                                                              |
| i3c.[`TARG_EVENT_ENABLE_1`](#targ_event_enable)                             | 0x358    |        4 | Target Event enables.                                                              |
| i3c.[`TARG_EVENT_ENABLE_2`](#targ_event_enable)                             | 0x35c    |        4 | Target Event enables.                                                              |
| i3c.[`TARG_EVENT_ENABLE_3`](#targ_event_enable)                             | 0x360    |        4 | Target Event enables.                                                              |
| i3c.[`TARG_STATE_DEBUG`](#targ_state_debug)                                 | 0x364    |        4 | Target State Debug                                                                 |
| i3c.[`TARG_ENABLE`](#targ_enable)                                           | 0x368    |        4 | Enable signals for individual virtual targets.                                     |
| i3c.[`TARG_GROUP_0`](#targ_group)                                           | 0x36c    |        4 | Group addressing configuration.                                                    |
| i3c.[`TARG_GROUP_1`](#targ_group)                                           | 0x370    |        4 | Group addressing configuration.                                                    |
| i3c.[`TARG_GROUP_2`](#targ_group)                                           | 0x374    |        4 | Group addressing configuration.                                                    |
| i3c.[`TARG_GROUP_3`](#targ_group)                                           | 0x378    |        4 | Group addressing configuration.                                                    |
| i3c.[`TARG_GROUP_4`](#targ_group)                                           | 0x37c    |        4 | Group addressing configuration.                                                    |
| i3c.[`TARG_GROUP_5`](#targ_group)                                           | 0x380    |        4 | Group addressing configuration.                                                    |
| i3c.[`TARG_GROUP_6`](#targ_group)                                           | 0x384    |        4 | Group addressing configuration.                                                    |
| i3c.[`TARG_GROUP_7`](#targ_group)                                           | 0x388    |        4 | Group addressing configuration.                                                    |
| i3c.[`TARG_TX_THLD_CTRL_0`](#targ_tx_thld_ctrl)                             | 0x38c    |        4 | Target control register for setting Tx thresholds.                                 |
| i3c.[`TARG_TX_THLD_CTRL_1`](#targ_tx_thld_ctrl)                             | 0x390    |        4 | Target control register for setting Tx thresholds.                                 |
| i3c.[`TARG_TX_THLD_CTRL_2`](#targ_tx_thld_ctrl)                             | 0x394    |        4 | Target control register for setting Tx thresholds.                                 |
| i3c.[`TARG_TX_THLD_CTRL_3`](#targ_tx_thld_ctrl)                             | 0x398    |        4 | Target control register for setting Tx thresholds.                                 |
| i3c.[`TARG_TX_QUEUE_STATUS_LEVEL_0`](#targ_tx_queue_status_level)           | 0x39c    |        4 | Target status register reporting transmit queue levels.                            |
| i3c.[`TARG_TX_QUEUE_STATUS_LEVEL_1`](#targ_tx_queue_status_level)           | 0x3a0    |        4 | Target status register reporting transmit queue levels.                            |
| i3c.[`TARG_TX_QUEUE_STATUS_LEVEL_2`](#targ_tx_queue_status_level)           | 0x3a4    |        4 | Target status register reporting transmit queue levels.                            |
| i3c.[`TARG_TX_QUEUE_STATUS_LEVEL_3`](#targ_tx_queue_status_level)           | 0x3a8    |        4 | Target status register reporting transmit queue levels.                            |
| i3c.[`TARG_ADDR_0`](#targ_addr)                                             | 0x3ac    |        4 | Target address on the I3C bus.                                                     |
| i3c.[`TARG_ADDR_1`](#targ_addr)                                             | 0x3b0    |        4 | Target address on the I3C bus.                                                     |
| i3c.[`TARG_ADDR_2`](#targ_addr)                                             | 0x3b4    |        4 | Target address on the I3C bus.                                                     |
| i3c.[`TARG_ADDR_3`](#targ_addr)                                             | 0x3b8    |        4 | Target address on the I3C bus.                                                     |
| i3c.[`TARG_CHAR_0`](#targ_char)                                             | 0x3bc    |        4 | Target Characteristics.                                                            |
| i3c.[`TARG_CHAR_1`](#targ_char)                                             | 0x3c0    |        4 | Target Characteristics.                                                            |
| i3c.[`TARG_CHAR_2`](#targ_char)                                             | 0x3c4    |        4 | Target Characteristics.                                                            |
| i3c.[`TARG_CHAR_3`](#targ_char)                                             | 0x3c8    |        4 | Target Characteristics.                                                            |
| i3c.[`TARG_PID_LO_0`](#targ_pid_lo)                                         | 0x3cc    |        4 | Low part of Target Provisioned ID.                                                 |
| i3c.[`TARG_PID_LO_1`](#targ_pid_lo)                                         | 0x3d0    |        4 | Low part of Target Provisioned ID.                                                 |
| i3c.[`TARG_PID_LO_2`](#targ_pid_lo)                                         | 0x3d4    |        4 | Low part of Target Provisioned ID.                                                 |
| i3c.[`TARG_PID_LO_3`](#targ_pid_lo)                                         | 0x3d8    |        4 | Low part of Target Provisioned ID.                                                 |
| i3c.[`TARG_CAPS_0`](#targ_caps)                                             | 0x3dc    |        4 | Target Capabilities.                                                               |
| i3c.[`TARG_CAPS_1`](#targ_caps)                                             | 0x3e0    |        4 | Target Capabilities.                                                               |
| i3c.[`TARG_CAPS_2`](#targ_caps)                                             | 0x3e4    |        4 | Target Capabilities.                                                               |
| i3c.[`TARG_CAPS_3`](#targ_caps)                                             | 0x3e8    |        4 | Target Capabilities.                                                               |
| i3c.[`TARG_INFO_0`](#targ_info)                                             | 0x3ec    |        4 | Target information.                                                                |
| i3c.[`TARG_INFO_1`](#targ_info)                                             | 0x3f0    |        4 | Target information.                                                                |
| i3c.[`TARG_INFO_2`](#targ_info)                                             | 0x3f4    |        4 | Target information.                                                                |
| i3c.[`TARG_INFO_3`](#targ_info)                                             | 0x3f8    |        4 | Target information.                                                                |
| i3c.[`TARG_MAX_RDWR_0`](#targ_max_rdwr)                                     | 0x3fc    |        4 | Target Maximum Read/Write Rate and Turnaround.                                     |
| i3c.[`TARG_MAX_RDWR_1`](#targ_max_rdwr)                                     | 0x400    |        4 | Target Maximum Read/Write Rate and Turnaround.                                     |
| i3c.[`TARG_MAX_RDWR_2`](#targ_max_rdwr)                                     | 0x404    |        4 | Target Maximum Read/Write Rate and Turnaround.                                     |
| i3c.[`TARG_MAX_RDWR_3`](#targ_max_rdwr)                                     | 0x408    |        4 | Target Maximum Read/Write Rate and Turnaround.                                     |
| i3c.[`TTI_PORTS`](#tti_ports)                                               | 0x440    |       52 | TTI ports, occupying successive word addresses:                                    |
| i3c.[`TARGEXT_EXTCAP_HEADER`](#targext_extcap_header)                       | 0x474    |        4 | Target Extension Extended Capability Header                                        |
| i3c.[`TERM_EXTCAP_HEADER`](#term_extcap_header)                             | 0x478    |        4 | Terminating Extended Capability Header                                             |
| i3c.[`DAT`](#dat)                                                           | 0xa00    |      256 | Device Address Table.                                                              |
| i3c.[`DCT`](#dct)                                                           | 0xc00    |      512 | Device Characteristics Table.                                                      |
| i3c.[`BUFFER`](#buffer)                                                     | 0x1000   |     4096 | Software-managed 4KiB message buffer used for transmitting and receiving messages. |

## INTR_STATE
Interrupt State Register
- Offset: `0x0`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "hci", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "targ", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description       |
|:------:|:------:|:-------:|:-------|:------------------|
|  31:2  |        |         |        | Reserved          |
|   1    |   ro   |   0x0   | targ   | Target interrupt. |
|   0    |   ro   |   0x0   | hci    | HCI interrupt.    |

## INTR_ENABLE
Interrupt Enable Register
- Offset: `0x4`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "hci", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "targ", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                    |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------|
|  31:2  |        |         |        | Reserved                                                       |
|   1    |   rw   |   0x0   | targ   | Enable interrupt when [`INTR_STATE.targ`](#intr_state) is set. |
|   0    |   rw   |   0x0   | hci    | Enable interrupt when [`INTR_STATE.hci`](#intr_state) is set.  |

## INTR_TEST
Interrupt Test Register
- Offset: `0x8`
- Reset default: `0x0`
- Reset mask: `0x3`

### Fields

```wavejson
{"reg": [{"name": "hci", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "targ", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 30}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                             |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------|
|  31:2  |        |         |        | Reserved                                                |
|   1    |   wo   |   0x0   | targ   | Write 1 to force [`INTR_STATE.targ`](#intr_state) to 1. |
|   0    |   wo   |   0x0   | hci    | Write 1 to force [`INTR_STATE.hci`](#intr_state) to 1.  |

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

## INFO
IP block information, allowing software to adapt dynamically.
- Offset: `0x10`
- Reset default: `0xfffff10`
- Reset mask: `0x1fffffff`

### Fields

```wavejson
{"reg": [{"name": "REVISION", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "VERSION", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "DAT_ENTRY_MAX", "bits": 5, "attr": ["ro"], "rotate": -90}, {"name": "DCT_ENTRY_MAX", "bits": 5, "attr": ["ro"], "rotate": -90}, {"name": "BUF_DWORD_MAX", "bits": 11, "attr": ["ro"], "rotate": 0}, {"bits": 3}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                 |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------------------------------------------------|
| 31:29  |        |         |               | Reserved                                                                                                    |
| 28:18  |   ro   |  0x3ff  | BUF_DWORD_MAX | Index of the final DWORD of the shared Message Buffer. i.e. one less than its size in DWORDs.               |
| 17:13  |   ro   |  0x1f   | DCT_ENTRY_MAX | Index of the final entry of the HCI Device Characteristics Table. i.e. one less than the number of entries. |
|  12:8  |   ro   |  0x1f   | DAT_ENTRY_MAX | Index of the final entry of the HCI Device Address Table. i.e. one less than the number of entries.         |
|  7:4   |   ro   |   0x1   | VERSION       | Version number of the IP block.                                                                             |
|  3:0   |   ro   |   0x0   | REVISION      | Revision number of the IP block.                                                                            |

## CTRL_STATUS
Controller-side Status register.
- Offset: `0x14`
- Reset default: `0x80000000`
- Reset mask: `0x80000000`

### Fields

```wavejson
{"reg": [{"bits": 31}, {"name": "PRESENT", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name    | Description                                         |
|:------:|:------:|:-------:|:--------|:----------------------------------------------------|
|   31   |   ro   |   0x1   | PRESENT | Indicates the presence of Controller functionality. |
|  30:0  |        |         |         | Reserved                                            |

## CTRL_ERROR
Controller Error counts.
- Offset: `0x18`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "CE0", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "CE1", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "CE2", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "CE3", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------|
| 31:16  |        |         |        | Reserved                           |
| 15:12  |  rw1c  |   0x0   | CE3    | Count of type 3 Controller Errors. |
|  11:8  |  rw1c  |   0x0   | CE2    | Count of type 2 Controller Errors. |
|  7:4   |  rw1c  |   0x0   | CE1    | Count of type 1 Controller Errors. |
|  3:0   |  rw1c  |   0x0   | CE0    | Count of type 0 Controller Errors. |

## TARG_CONTROL
Target Control register.
- Offset: `0x1c`
- Reset default: `0x2`
- Reset mask: `0xc000001f`

### Fields

```wavejson
{"reg": [{"name": "EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "STBY_CR_SUPPORT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CRHDLY1_AS", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "CRHDLY1_SET_AS", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 25}, {"name": "HJ_REQUEST", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RESET", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
|   31   |   wo   |   0x0   | [RESET](#targ_control--reset)                     |
|   30   |   rw   |   0x0   | [HJ_REQUEST](#targ_control--hj_request)           |
|  29:5  |        |         | Reserved                                          |
|   4    |   rw   |   0x0   | [CRHDLY1_SET_AS](#targ_control--crhdly1_set_as)   |
|  3:2   |   rw   |   0x0   | [CRHDLY1_AS](#targ_control--crhdly1_as)           |
|   1    |   rw   |   0x1   | [STBY_CR_SUPPORT](#targ_control--stby_cr_support) |
|   0    |   rw   |   0x0   | [EN](#targ_control--en)                           |

### TARG_CONTROL . RESET
Software reset of Target logic.

Iff the Standby Controller support is disabled by clearing `STBY_CR_SUPPORT`, writing '1' to this field will reset all of the Target-side logic.
To reset the Target-side logic when Standby Controller support is enabled, software shall instead use the `SOFT_RST` field of the HCI-specified `RESET_CONTROL` register, whether or not the Controller is currently the Active Controller.

### TARG_CONTROL . HJ_REQUEST
Issue Hot-Join request.

This applies to all Virtual Targets since they share a single physical Target.
Software shall set this to '1' to issue the request, and the hardware will clear it when the request has been sent and acknowledged.

### TARG_CONTROL . CRHDLY1_SET_AS
Set Bus Activity State.
This information is returned in response to the CRHDLY form of the GETMXDS CCC.

### TARG_CONTROL . CRHDLY1_AS
Controller Handoff Activity State.
This information is returned in response to the CRHDLY form of the GETMXDS CCC.

### TARG_CONTROL . STBY_CR_SUPPORT
Standby Controller role supported.

When set the Controller shall have the option of performing Controller Role Handoff and switching into Standby Controller mode.
If this field is clear the Controller will refuse to hand off the bus when requested and will instead remain the Active Controller,
thus freeing up the first Virtual Target to operate independently as a dedicated Target device.

### TARG_CONTROL . EN
Target enable.

Enable the Target-side logic as a separate I3C device, instead of supporting Standby Controller mode.
In this configuration the Controller-side logic must remain the Active Controller and cannot perform Controller Role Handoff.

## TARG_STATUS
Target-side Status register
- Offset: `0x20`
- Reset default: `0x80000000`
- Reset mask: `0xc7ffffff`

### Fields

```wavejson
{"reg": [{"name": "EXT_INFO", "bits": 15, "attr": ["rw"], "rotate": 0}, {"name": "EXT_PRESENT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RSTACT", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "RSTACT_VIRT_TARG_DET", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "VTM", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "PROTOCOL_ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 3}, {"name": "ACTIVE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "PRESENT", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                                                                                                                                               |
|:------:|:------:|:-------:|:---------------------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|   31   |   ro   |   0x1   | PRESENT              | Indicates the presence of Target functionality.                                                                                                                                                                                                           |
|   30   |   ro   |   0x0   | ACTIVE               | Indicates whether the Target functionality is presently active, as opposed to under reset.                                                                                                                                                                |
| 29:27  |        |         |                      | Reserved                                                                                                                                                                                                                                                  |
|   26   |   ro   |   0x0   | PROTOCOL_ERROR       | Protocol error detected since the last GETSTATUS CCC to read this indicator.                                                                                                                                                                              |
|   25   |   ro   |   0x0   | VTM                  | Vendor Test Mode active, in response to ENTTM.                                                                                                                                                                                                            |
|   24   |   ro   |   0x0   | RSTACT_VIRT_TARG_DET | RSTACT Virtual Target Detect.                                                                                                                                                                                                                             |
| 23:16  |   ro   |   0x0   | RSTACT               | Configured Target Reset action.                                                                                                                                                                                                                           |
|   15   |   ro   |   0x0   | EXT_PRESENT          | Indicates whether one or more additional protocols is implemented in the Target hardware. Some protocols require a sufficiently fast response that software involvement is not possible. These may be implemented as an extension within the Target core. |
|  14:0  |   rw   |   0x0   | EXT_INFO             | Extension-specific information.                                                                                                                                                                                                                           |

## TARG_SINK_CONTROL
Target data sink control.
- Offset: `0x24`
- Reset default: `0x0`
- Reset mask: `0x87ff7000`

### Fields

```wavejson
{"reg": [{"bits": 12}, {"name": "BUFFER", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "LENGTH", "bits": 11, "attr": ["rw"], "rotate": 0}, {"bits": 4}, {"name": "START", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                                 |
|:------:|:------:|:-------:|:-------------------------------------|
|   31   |   wo   |   0x0   | [START](#targ_sink_control--start)   |
| 30:27  |        |         | Reserved                             |
| 26:16  |   rw   |   0x0   | [LENGTH](#targ_sink_control--length) |
|   15   |        |         | Reserved                             |
| 14:12  |   rw   |   0x0   | [BUFFER](#targ_sink_control--buffer) |
|  11:0  |        |         | Reserved                             |

### TARG_SINK_CONTROL . START
Initiate removal of DWORDs from a transmission buffer.

The 'data sink' logic is a mechanism for recovering from aborting or failed transmissions without impacting subsequent, already-queued transfers.
Software shall write '1' to this field to start the 'data sink' logic.
The ACTIVE field in the corresponding `TARG_SINK_STATUS` register shows whether the logic is still active.

### TARG_SINK_CONTROL . LENGTH
Specifies the number of DWORDs to be removed, minus 1.

This field instructs the 'data sink' logic to remove a specified number of DWORDs of data from the specified source.
Software shall program 'n-1' into this field to remove 'n' DWORDs.

### TARG_SINK_CONTROL . BUFFER
Specifies the transmission buffer from which DWORDs are to be removed.

0 - IBI Data buffer.
1 - Virtual Target 0 Tx buffer
2 - Virtual Target 1 Tx buffer...

## TARG_SINK_STATUS
Target data sink status.
- Offset: `0x28`
- Reset default: `0x0`
- Reset mask: `0x7ff0003`

### Fields

```wavejson
{"reg": [{"name": "ACTIVE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ERROR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 14}, {"name": "LENGTH", "bits": 11, "attr": ["ro"], "rotate": 0}, {"bits": 5}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                |
|:------:|:------:|:-------:|:-------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:27  |        |         |        | Reserved                                                                                                                                                                                                                   |
| 26:16  |   ro   |   0x0   | LENGTH | Reports the numbers of DWORDs still to be removed. In the event of an error, this value may be used to ascertain how much of the operation was performed.                                                                  |
|  15:2  |        |         |        | Reserved                                                                                                                                                                                                                   |
|   1    |   ro   |   0x0   | ERROR  | Indicates whether the data sink mechanism stopped prematurely. If the specified buffer did not contain sufficient data for the logic to remove the specified number of DWORDs it will set this bit when becoming inactive. |
|   0    |   ro   |   0x0   | ACTIVE | Indicates whether the data sink logic is active. This bit becomes set when the operation is started and will be cleared at most a few tens of microseconds later when the operation is complete.                           |

## RESET_DET_CTRL
Reset detector control.
- Offset: `0x2c`
- Reset default: `0x0`
- Reset mask: `0x310002`

### Fields

```wavejson
{"reg": [{"bits": 1}, {"name": "SLEEP_REQ", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 14}, {"name": "WAKE_ACK", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 3}, {"name": "RST_PERIPH_EN", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RST_TARGET_EN", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 10}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                            |
|:------:|:------:|:-------:|:--------------|:-----------------------------------------------------------------------|
| 31:22  |        |         |               | Reserved                                                               |
|   21   |   wo   |   0x0   | RST_TARGET_EN | Enable response to a Whole Target reset request.                       |
|   20   |   wo   |   0x0   | RST_PERIPH_EN | Enable response to a Peripheral reset request.                         |
| 19:17  |        |         |               | Reserved                                                               |
|   16   |   wo   |   0x0   | WAKE_ACK      | Wake acknowledgement.                                                  |
|  15:2  |        |         |               | Reserved                                                               |
|   1    |   wo   |   0x0   | SLEEP_REQ     | Activate the reset detector prior to entry into 'Deepest Sleep' state. |

## RESET_DET_STATUS
Reset detector status.
- Offset: `0x30`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "ACTIVE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "WAKE_UP", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RST_PERIPH", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "RST_TARGET", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                               |
|:------:|:------:|:-------:|:-----------|:----------------------------------------------------------|
|  31:4  |        |         |            | Reserved                                                  |
|   3    |   ro   |   0x0   | RST_TARGET | Indicates that a Whole Target reset requst was received.  |
|   2    |   ro   |   0x0   | RST_PERIPH | Indicates that a Peripheral request request was received. |
|   1    |   ro   |   0x0   | WAKE_UP    | Indicates that a Wake Up request was received.            |
|   0    |   ro   |   0x0   | ACTIVE     | Indicates whether the reset detector is active.           |

## CTRL_TIME_SP
Controller Timing Parameters for Start and stoP.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x34`
- Reset default: `0x3ff03ff`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "TCBP_DIV2", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "TCAS_DIV2", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                                                                                                                                                                                         |
|:------:|:------:|:-------:|:----------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |           | Reserved                                                                                                                                                                                                            |
| 25:16  |   rw   |  0x3ff  | TCAS_DIV2 | Half of the delay between SDA falling and SCL falling in START timing, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value. |
| 15:10  |        |         |           | Reserved                                                                                                                                                                                                            |
|  9:0   |   rw   |  0x3ff  | TCBP_DIV2 | Half of the delay between SCL rising and SDA rising in STOP timing, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value.    |

## CTRL_TIME_OD
Controller Timing Parameters for Open Drain signaling.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x38`
- Reset default: `0x3ff03ff`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "SCLLO_DIV2", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "SCLHI_DIV2", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                                                                                                                             |
|:------:|:------:|:-------:|:-----------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |            | Reserved                                                                                                                                                                                                |
| 25:16  |   rw   |  0x3ff  | SCLHI_DIV2 | Half of the SCL high interval during Open Drain signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value. |
| 15:10  |        |         |            | Reserved                                                                                                                                                                                                |
|  9:0   |   rw   |  0x3ff  | SCLLO_DIV2 | Half of the SCL low interval during Open Drain signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value.  |

## CTRL_TIME_PP
Controller Timing Parameters for SDR0/HDR-DDR Push-Pull SCL High signaling.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x3c`
- Reset default: `0x3ff83ff`
- Reset mask: `0x3ff83ff`

### Fields

```wavejson
{"reg": [{"name": "TCHH", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 5}, {"name": "HCEXT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TCHS", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                          |
|:------:|:------:|:-------:|:------------------------------|
| 31:26  |        |         | Reserved                      |
| 25:16  |   rw   |  0x3ff  | [TCHS](#ctrl_time_pp--tchs)   |
|   15   |   rw   |   0x1   | [HCEXT](#ctrl_time_pp--hcext) |
| 14:10  |        |         | Reserved                      |
|  9:0   |   rw   |  0x3ff  | [TCHH](#ctrl_time_pp--tchh)   |

### CTRL_TIME_PP . TCHS
Half of the SCL high interval during Push-Pull signaling, minus 1.
This interval is in terms of the IP clock period.
If this field has all bits set then the hardware will calculate a suitable value.

### CTRL_TIME_PP . HCEXT
Enable half-cycle SCL extension.
If the field `PP_SCLHI_DIV2` has been set to something other than 0x3ff, this bit controls whether the half-cycle SCL extension is enabled.
If `PP_SCLHI_DIV2` has all bits set then the hardware will determine this setting automatically.
Extending SCL by half a cycle of the IP clock enables support for other clock frequencies such as 96MHz.

### CTRL_TIME_PP . TCHH
Half of the SCL low interval during Push-Pull signaling at SDR0 rate, minus 1.
This interval is in terms of the IP clock period.
If this field has all bits set then the hardware will calculate a suitable value.

## CTRL_TIME_SDR0
Controller Timing Parameters for SDR0/HDR-DDR Push-Pull SCL Low signaling.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x40`
- Reset default: `0x3ff03ff`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "TCLH", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "TCLS", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |        | Reserved                                                                                                                                                                                                                           |
| 25:16  |   rw   |  0x3ff  | TCLS   | Duration of setup phase before rising SCL when using Push-Pull signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value.             |
| 15:10  |        |         |        | Reserved                                                                                                                                                                                                                           |
|  9:0   |   rw   |  0x3ff  | TCLH   | Duration of hold phase after falling SCL when using Push-Pull signaling at SDR0 rate, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value. |

## CTRL_TIME_SDR1
Controller Timing Parameters for SDR1 Push-Pull SCL Low signaling.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x44`
- Reset default: `0x3ff03ff`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "TCLH", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "TCLS", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |        | Reserved                                                                                                                                                                                                                           |
| 25:16  |   rw   |  0x3ff  | TCLS   | Duration of setup phase before rising SCL when using Push-Pull signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value.             |
| 15:10  |        |         |        | Reserved                                                                                                                                                                                                                           |
|  9:0   |   rw   |  0x3ff  | TCLH   | Duration of hold phase after falling SCL when using Push-Pull signaling at SDR0 rate, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value. |

## CTRL_TIME_SDR2
Controller Timing Parameters for SDR2 Push-Pull SCL Low signaling.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x48`
- Reset default: `0x3ff03ff`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "TCLH", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "TCLS", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |        | Reserved                                                                                                                                                                                                                           |
| 25:16  |   rw   |  0x3ff  | TCLS   | Duration of setup phase before rising SCL when using Push-Pull signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value.             |
| 15:10  |        |         |        | Reserved                                                                                                                                                                                                                           |
|  9:0   |   rw   |  0x3ff  | TCLH   | Duration of hold phase after falling SCL when using Push-Pull signaling at SDR0 rate, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value. |

## CTRL_TIME_SDR3
Controller Timing Parameters for SDR3 Push-Pull SCL Low signaling.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x4c`
- Reset default: `0x3ff03ff`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "TCLH", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "TCLS", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |        | Reserved                                                                                                                                                                                                                           |
| 25:16  |   rw   |  0x3ff  | TCLS   | Duration of setup phase before rising SCL when using Push-Pull signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value.             |
| 15:10  |        |         |        | Reserved                                                                                                                                                                                                                           |
|  9:0   |   rw   |  0x3ff  | TCLH   | Duration of hold phase after falling SCL when using Push-Pull signaling at SDR0 rate, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value. |

## CTRL_TIME_SDR4
Controller Timing Parameters for SDR4 Push-Pull SCL Low signaling.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x50`
- Reset default: `0x3ff03ff`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "TCLH", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "TCLS", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                                                                                                                                                                                        |
|:------:|:------:|:-------:|:-------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |        | Reserved                                                                                                                                                                                                                           |
| 25:16  |   rw   |  0x3ff  | TCLS   | Duration of setup phase before rising SCL when using Push-Pull signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value.             |
| 15:10  |        |         |        | Reserved                                                                                                                                                                                                                           |
|  9:0   |   rw   |  0x3ff  | TCLH   | Duration of hold phase after falling SCL when using Push-Pull signaling at SDR0 rate, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value. |

## CTRL_TIME_FMP
Controller Timing Parameters for I2C Fast Mode Plus signaling.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x54`
- Reset default: `0x3ff03ff`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "SCLLO_DIV2", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "SCLHI_DIV2", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                                                                                                                                     |
|:------:|:------:|:-------:|:-----------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |            | Reserved                                                                                                                                                                                                        |
| 25:16  |   rw   |  0x3ff  | SCLHI_DIV2 | Half of the SCL high interval during I2C Fast Mode Plus signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value. |
| 15:10  |        |         |            | Reserved                                                                                                                                                                                                        |
|  9:0   |   rw   |  0x3ff  | SCLLO_DIV2 | Half of the SCL low interval during I2C Fast Mode Plus signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value.  |

## CTRL_TIME_FM
Controller Timing Parameters for I2C Fast Mode signaling.

This register shall be modified only when the Controller is not connected to the I3C bus.
- Offset: `0x58`
- Reset default: `0x3ff03ff`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "SCLLO_DIV2", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "SCLHI_DIV2", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                                                                                                                                |
|:------:|:------:|:-------:|:-----------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |            | Reserved                                                                                                                                                                                                   |
| 25:16  |   rw   |  0x3ff  | SCLHI_DIV2 | Half of the SCL high interval during I2C Fast Mode signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value. |
| 15:10  |        |         |            | Reserved                                                                                                                                                                                                   |
|  9:0   |   rw   |  0x3ff  | SCLLO_DIV2 | Half of the SCL low interval during I2C Fast Mode signaling, minus 1. This interval is in terms of the IP clock period. If this field has all bits set then the hardware will calculate a suitable value.  |

## INTERVAL_TIME0
Interval Timers 0 register.
Time intervals are specified in microseconds.
- Offset: `0x5c`
- Reset default: `0xc3501096`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "READ_STALLED", "bits": 12, "attr": ["rw"], "rotate": 0}, {"name": "CTRL_BUS_AVAIL", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "DEAD_BUS", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                        |
|:------:|:------:|:-------:|:---------------|:---------------------------------------------------------------------------------------------------|
| 31:16  |   rw   | 0xc350  | DEAD_BUS       | Timer interval for the Dead Bus condition.                                                         |
| 15:12  |   rw   |   0x1   | CTRL_BUS_AVAIL | Timer interval for the Controller Bus Available condition.                                         |
|  11:0  |   rw   |  0x96   | READ_STALLED   | Timer interval for detection of SDA read stalls (no Controller SCL activity during Read Transfer). |

## INTERVAL_TIME1
Interval Timers 1 register.
Time intervals are specified in microseconds.
- Offset: `0x60`
- Reset default: `0x1503c0c8`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "TARG_BUS_IDLE", "bits": 12, "attr": ["rw"], "rotate": 0}, {"name": "TE0_RECOV", "bits": 12, "attr": ["rw"], "rotate": 0}, {"name": "TARG_TRX_RST", "bits": 4, "attr": ["rw"], "rotate": -90}, {"name": "TARG_BUS_AVAIL", "bits": 4, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                                    |
|:------:|:------:|:-------:|:---------------|:---------------------------------------------------------------------------------------------------------------|
| 31:28  |   rw   |   0x1   | TARG_BUS_AVAIL | Timer interval for the Target Bus Available condition.                                                         |
| 27:24  |   rw   |   0x5   | TARG_TRX_RST   | Duration of the Target reset interval in microseconds.                                                         |
| 23:12  |   rw   |  0x3c   | TE0_RECOV      | Duration of the interval before which the Target shall attempt recovery from a Target Error 0 (TE0) condition. |
|  11:0  |   rw   |  0xc8   | TARG_BUS_IDLE  | Timer interval for the Target Bus Idle condition.                                                              |

## PHY_CONFIG
PHY configuration
- Offset: `0x64`
- Reset default: `0x1100003`
- Reset mask: `0x8bf00003`

### Fields

```wavejson
{"reg": [{"name": "SCL_HK_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "SDA_HK_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 18}, {"name": "CTRL_SDA", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CTRL_SDA_PU_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CTRL_SDA_OD_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CTRL_SDA_PP_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CTRL_SCL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CTRL_SCL_PU_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "CTRL_SCL_PP_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "CTRL_DIRECT_DRIVE_EN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                          |
|:------:|:------:|:-------:|:---------------------|:-----------------------------------------------------------------------------------------------------|
|   31   |   rw   |   0x0   | CTRL_DIRECT_DRIVE_EN | Enable direct driving of the Serial Clock (SCL) and Serial Data (SDA) lines by software.             |
| 30:28  |        |         |                      | Reserved                                                                                             |
|   27   |   rw   |   0x0   | CTRL_SCL_PP_EN       | Enable push-pull driving of SCL in direct-driving mode.                                              |
|   26   |        |         |                      | Reserved                                                                                             |
|   25   |   rw   |   0x0   | CTRL_SCL_PU_EN       | Enable pull-up on SCL in direct-driving mode.                                                        |
|   24   |   rw   |   0x1   | CTRL_SCL             | State of the SCL line when direct-driving is enabled.                                                |
|   23   |   rw   |   0x0   | CTRL_SDA_PP_EN       | Enable push-pull driving of SDA in direct-driving mode, when open drain driving is not also enabled. |
|   22   |   rw   |   0x0   | CTRL_SDA_OD_EN       | Enable open drain driving of SDA in direct-driving mode.                                             |
|   21   |   rw   |   0x0   | CTRL_SDA_PU_EN       | Enable pull-up on SDA in direct-driving mode.                                                        |
|   20   |   rw   |   0x1   | CTRL_SDA             | State of the SDA line when direct-driving is enabled.                                                |
|  19:2  |        |         |                      | Reserved                                                                                             |
|   1    |   rw   |   0x1   | SDA_HK_EN            | High-keeper enable for the SDA lane.                                                                 |
|   0    |   rw   |   0x1   | SCL_HK_EN            | High-keeper enable for the SCL line.                                                                 |

## BLOCKED_ADDR
Blocked target addresses.
The controller will raise an error if any attempt is made to access a blocked target address.
This feature is intended to safeguard against inadvertent accesses to any I2C device that may try to employ clock-stretching, but it may also be of use diagnostically.
- Offset: `0x68`
- Reset default: `0x0`
- Reset mask: `0x7f7f7f7f`

### Fields

```wavejson
{"reg": [{"name": "ADDR0", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 1}, {"name": "MASK0", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 1}, {"name": "ADDR1", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 1}, {"name": "MASK1", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name                          |
|:------:|:------:|:-------:|:------------------------------|
|   31   |        |         | Reserved                      |
| 30:24  |   rw   |   0x0   | [MASK1](#blocked_addr--mask1) |
|   23   |        |         | Reserved                      |
| 22:16  |   rw   |   0x0   | [ADDR1](#blocked_addr--addr1) |
|   15   |        |         | Reserved                      |
|  14:8  |   rw   |   0x0   | [MASK0](#blocked_addr--mask0) |
|   7    |        |         | Reserved                      |
|  6:0   |   rw   |   0x0   | [ADDR0](#blocked_addr--addr0) |

### BLOCKED_ADDR . MASK1
Address mask for the second set of blocked addresses.

This mask determines which bits of the device address will be tested and matched against the address in 'ADDR1'.
I2C devices are commonly configured with one of a small set of static addresses, differing in only one two address bits.
If this field is zero then 'ADDR1' is implicitly not used.

### BLOCKED_ADDR . ADDR1
Second blocked address.

### BLOCKED_ADDR . MASK0
Address mask for the first set of blocked addresses.

This mask determines which bits of the device address will be tested and matched against the address in 'ADDR0'.
I2C devices are commonly configured with one of a small set of static addresses, differing in only one two address bits.
If this field is zero then 'ADDR0' is implicitly not used.

### BLOCKED_ADDR . ADDR0
First blocked address.

## BUFFER_CTRL
Buffer control
- Offset: `0x6c`
- Reset default: `0x0`
- Reset mask: `0xb0000000`

### Fields

```wavejson
{"reg": [{"bits": 28}, {"name": "SW_ADDR_HI", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "CLEAR", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name                                   |
|:------:|:------:|:-------:|:---------------------------------------|
|   31   |   wo   |   0x0   | [CLEAR](#buffer_ctrl--clear)           |
|   30   |        |         | Reserved                               |
| 29:28  |   rw   |   0x0   | [SW_ADDR_HI](#buffer_ctrl--sw_addr_hi) |
|  27:0  |        |         | Reserved                               |

### BUFFER_CTRL . CLEAR
Software clear of buffer state including the following:
All `WPTR` and `RPTR` values are set to the corresponding `MIN` values, emptying all circular buffers.
This shall only be used when both the Controller- and the Target-side functionality are disabled.

### BUFFER_CTRL . SW_ADDR_HI
Supplies the high address bits when software performs direct accesses to the internal message buffer.
The IP may be configured to map part of its internal message buffer into the upper half of the IP address space.
This provides more RAM to a memory-limited system when the I3C is not being used, and may be diagnostically useful when it is used.
Since half of the IP address space is typically 2KiB but the message buffer is larger, this field allows software-controlled paging.

## BUFFER_STATUS
Buffer status
- Offset: `0x70`
- Reset default: `0x0`
- Reset mask: `0xc0000000`

### Fields

```wavejson
{"reg": [{"bits": 30}, {"name": "TTIQ_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "HCIQ_ERR", "bits": 1, "attr": ["rw1c"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                                                                                                                                                                               |
|:------:|:------:|:-------:|:---------|:----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|   31   |  rw1c  |   0x0   | HCIQ_ERR | Diagnostic error indicator for the Host Controller Interface (HCI) queues. The hardware sets this bit in the event of a write to a full or read-only queue, or a read from an empty or write-only queue. Software shall clear this bit by writing '1'.    |
|   30   |  rw1c  |   0x0   | TTIQ_ERR | Diagnostic error indicator for the Target Transaction Interface (TTI) queues. The hardware sets this bit in the event of a write to a full or read-only queue, or a read from an empty or write-only queue. Software shall clear this bit by writing '1'. |
|  29:0  |        |         |          | Reserved                                                                                                                                                                                                                                                  |

## CTRL_TXBUF_CONFIG
Controller TX Buffer Configuration
- Offset: `0x74`
- Reset default: `0x607f0000`
- Reset mask: `0x73ff03ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "SIZE_VAL", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                       |
|:------:|:------:|:-------:|:---------|:--------------------------------------------------------------------------------------------------|
|   31   |        |         |          | Reserved                                                                                          |
| 30:28  |   rw   |   0x6   | SIZE_VAL | Size value presented as `QUEUE_SIZE.TX_DATA_BUFFER_SIZE`. This value is log2(size in DWORDs) - 1. |
| 27:26  |        |         |          | Reserved                                                                                          |
| 25:16  |   rw   |  0x7f   | MAX_ADDR | Maximum address for Controller TX use (inclusive).                                                |
| 15:10  |        |         |          | Reserved                                                                                          |
|  9:0   |   rw   |   0x0   | MIN_ADDR | Minimum address for Controller TX use.                                                            |

## CTRL_TXBUF_STATE
Controller TX Buffer State.
- Offset: `0x78`
- Reset default: `0x0`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the buffer is full.           |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |   0x0   | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |   0x0   | WPTR   | Current write pointer.                     |

## CTRL_RXBUF_CONFIG
Controller RX Buffer Configuration
- Offset: `0x7c`
- Reset default: `0x60ff0080`
- Reset mask: `0x73ff03ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "SIZE_VAL", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                       |
|:------:|:------:|:-------:|:---------|:--------------------------------------------------------------------------------------------------|
|   31   |        |         |          | Reserved                                                                                          |
| 30:28  |   rw   |   0x6   | SIZE_VAL | Size value presented as `QUEUE_SIZE.RX_DATA_BUFFER_SIZE`. This value is log2(size in DWORDs) - 1. |
| 27:26  |        |         |          | Reserved                                                                                          |
| 25:16  |   rw   |  0xff   | MAX_ADDR | Maximum address for Controller RX use (inclusive).                                                |
| 15:10  |        |         |          | Reserved                                                                                          |
|  9:0   |   rw   |  0x80   | MIN_ADDR | Minimum address for Controller RX use.                                                            |

## CTRL_RXBUF_STATE
Controller RX Buffer State.
- Offset: `0x80`
- Reset default: `0x800080`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the buffer is full.           |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x80   | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x80   | WPTR   | Current write pointer.                     |

## COMMAND_QUEUE_CONFIG
Command Queue Configuration.
- Offset: `0x84`
- Reset default: `0x1011f100`
- Reset mask: `0xff3ff3ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "SIZE_VAL", "bits": 8, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                         |
|:------:|:------:|:-------:|:---------|:----------------------------------------------------|
| 31:24  |   rw   |  0x10   | SIZE_VAL | Size value presented as `QUEUE_SIZE.CR_QUEUE_SIZE`. |
| 23:22  |        |         |          | Reserved                                            |
| 21:12  |   rw   |  0x11f  | MAX_ADDR | Maximum address for Command Queue use (inclusive).  |
| 11:10  |        |         |          | Reserved                                            |
|  9:0   |   rw   |  0x100  | MIN_ADDR | Minimum address for Command Queue use.              |

## COMMAND_QUEUE_STATE
Command Queue State.
- Offset: `0x88`
- Reset default: `0x1000100`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the queue is full.            |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x100  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x100  | WPTR   | Current write pointer.                     |

## RESPONSE_QUEUE_CONFIG
Response Queue Configuration.
- Offset: `0x8c`
- Reset default: `0x1012f120`
- Reset mask: `0xff3ff3ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "SIZE_VAL", "bits": 8, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                  |
|:------:|:------:|:-------:|:---------|:-------------------------------------------------------------|
| 31:24  |   rw   |  0x10   | SIZE_VAL | Size value presented as `ALT_QUEUE_SIZE.ALT_RSP_QUEUE_SIZE`. |
| 23:22  |        |         |          | Reserved                                                     |
| 21:12  |   rw   |  0x12f  | MAX_ADDR | Maximum address for Response Queue use (inclusive).          |
| 11:10  |        |         |          | Reserved                                                     |
|  9:0   |   rw   |  0x120  | MIN_ADDR | Minimum address for Response Queue use.                      |

## RESPONSE_QUEUE_STATE
Response Queue State.
- Offset: `0x90`
- Reset default: `0x1200120`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the queue is full.            |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x120  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x120  | WPTR   | Current write pointer.                     |

## IBI_CONFIG
In-Band Interrupt Queue Configuration.
- Offset: `0x94`
- Reset default: `0x101af130`
- Reset mask: `0xff3ff3ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "SIZE_VAL", "bits": 8, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                                                                                                                                                |
|:------:|:------:|:-------:|:---------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:24  |   rw   |  0x10   | SIZE_VAL | Size value presented as `QUEUE_SIZE.IBI_STATUS_SIZE`. This value represents the sum of the IBI Queue and the IBI Status Descriptor FIFO. Since EXT_IBI_QUEUE_EN is set, the actual number of DWORDs is 8 times this value. |
| 23:22  |        |         |          | Reserved                                                                                                                                                                                                                   |
| 21:12  |   rw   |  0x1af  | MAX_ADDR | Maximum address for IBI Queue use (inclusive).                                                                                                                                                                             |
| 11:10  |        |         |          | Reserved                                                                                                                                                                                                                   |
|  9:0   |   rw   |  0x130  | MIN_ADDR | Minimum address for IBI Queue use.                                                                                                                                                                                         |

## IBI_STATE
In-Band Interrupt Queue State.
- Offset: `0x98`
- Reset default: `0x1300130`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the queue is full.            |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x130  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x130  | WPTR   | Current write pointer.                     |

## IBI_STAT_CONFIG
In-Band Status Descriptor FIFO Configuration.
- Offset: `0x9c`
- Reset default: `0x1cf1b0`
- Reset mask: `0x3ff3ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 2}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 10}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                     |
|:------:|:------:|:-------:|:---------|:----------------------------------------------------------------|
| 31:22  |        |         |          | Reserved                                                        |
| 21:12  |   rw   |  0x1cf  | MAX_ADDR | Maximum address for IBI Status Descriptor FIFO use (inclusive). |
| 11:10  |        |         |          | Reserved                                                        |
|  9:0   |   rw   |  0x1b0  | MIN_ADDR | Minimum address for IBI Status Descriptor FIFO use.             |

## IBI_STAT_STATE
In-Band Status Descriptor FIFO State.
- Offset: `0xa0`
- Reset default: `0x1b001b0`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the FIFO is full.             |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x1b0  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x1b0  | WPTR   | Current write pointer.                     |

## TARG_TXBUF_CONFIG
Target TX Buffer Configuration.
- Reset default: `0x20f01d0`
- Reset mask: `0x3ff03ff`

### Instances

| Name                | Offset   |
|:--------------------|:---------|
| TARG_TXBUF_CONFIG_0 | 0xa4     |
| TARG_TXBUF_CONFIG_1 | 0xa8     |
| TARG_TXBUF_CONFIG_2 | 0xac     |
| TARG_TXBUF_CONFIG_3 | 0xb0     |


### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                                                                                                                                                                             |
|:------:|:------:|:-------:|:---------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:26  |        |         |          | Reserved                                                                                                                                                                                                                                                |
| 25:16  |   rw   |  0x20f  | MAX_ADDR | Maximum address for Target TX use (inclusive). The default addressing apportions the available storage space among the maximum number of Virtual Targets. For configurations employing fewer Virtual Targets, software should modify the configuration. |
| 15:10  |        |         |          | Reserved                                                                                                                                                                                                                                                |
|  9:0   |   rw   |  0x1d0  | MIN_ADDR | Minimum address for Target TX use. The default addressing apportions the available storage space among the maximum number of Virtual Targets. For configurations employing fewer Virtual Targets, software should modify the configuration.             |

## TARG_TXBUF_STATE
Target 0 TX Buffer State.
- Reset default: `0x1d001d0`
- Reset mask: `0xc3ff03ff`

### Instances

| Name               | Offset   |
|:-------------------|:---------|
| TARG_TXBUF_STATE_0 | 0xb4     |
| TARG_TXBUF_STATE_1 | 0xb8     |
| TARG_TXBUF_STATE_2 | 0xbc     |
| TARG_TXBUF_STATE_3 | 0xc0     |


### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the buffer is full.           |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x1d0  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x1d0  | WPTR   | Current write pointer.                     |

## TARG_RXBUF_CONFIG
Target RX Buffer Configuration
- Offset: `0xc4`
- Reset default: `0x36f02d0`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                    |
|:------:|:------:|:-------:|:---------|:-----------------------------------------------|
| 31:26  |        |         |          | Reserved                                       |
| 25:16  |   rw   |  0x36f  | MAX_ADDR | Maximum address for Target RX use (inclusive). |
| 15:10  |        |         |          | Reserved                                       |
|  9:0   |   rw   |  0x2d0  | MIN_ADDR | Minimum address for Target RX use.             |

## TARG_RXBUF_STATE
Target RX Buffer State.
- Offset: `0xc8`
- Reset default: `0x2d002d0`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the buffer is full.           |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x2d0  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x2d0  | WPTR   | Current write pointer.                     |

## TARG_IBI_CONFIG
Target In-Band Interrupt Payload Queue Configuration
- Offset: `0xcc`
- Reset default: `0x3af0370`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                         |
|:------:|:------:|:-------:|:---------|:----------------------------------------------------|
| 31:26  |        |         |          | Reserved                                            |
| 25:16  |   rw   |  0x3af  | MAX_ADDR | Maximum address for Target RX data use (inclusive). |
| 15:10  |        |         |          | Reserved                                            |
|  9:0   |   rw   |  0x370  | MIN_ADDR | Minimum address for Target IBI data use.            |

## TARG_IBI_STATE
Target In-Band Interrupt Payload Queue State.
- Offset: `0xd0`
- Reset default: `0x3700370`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the buffer is full.           |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x370  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x370  | WPTR   | Current write pointer.                     |

## TARG_TXDESC_CONFIG
Target Transmission Descriptor Queue Configuration.
- Reset default: `0x3b703b0`
- Reset mask: `0x3ff03ff`

### Instances

| Name                 | Offset   |
|:---------------------|:---------|
| TARG_TXDESC_CONFIG_0 | 0xd4     |
| TARG_TXDESC_CONFIG_1 | 0xd8     |
| TARG_TXDESC_CONFIG_2 | 0xdc     |
| TARG_TXDESC_CONFIG_3 | 0xe0     |


### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                       |
|:------:|:------:|:-------:|:---------|:------------------------------------------------------------------|
| 31:26  |        |         |          | Reserved                                                          |
| 25:16  |   rw   |  0x3b7  | MAX_ADDR | Maximum address for Target 0 Tx Descriptor Queue use (inclusive). |
| 15:10  |        |         |          | Reserved                                                          |
|  9:0   |   rw   |  0x3b0  | MIN_ADDR | Minimum address for Target 0 Tx Descriptor Queue use.             |

## TARG_TXDESC_STATE
Target Transmission Descriptor Queue State.
- Reset default: `0x3b003b0`
- Reset mask: `0xc3ff03ff`

### Instances

| Name                | Offset   |
|:--------------------|:---------|
| TARG_TXDESC_STATE_0 | 0xe4     |
| TARG_TXDESC_STATE_1 | 0xe8     |
| TARG_TXDESC_STATE_2 | 0xec     |
| TARG_TXDESC_STATE_3 | 0xf0     |


### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the queue is full.            |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x3b0  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x3b0  | WPTR   | Current write pointer.                     |

## TARG_RXDESC_CONFIG
Target Reception Descriptor Queue Configuration.
- Offset: `0xf4`
- Reset default: `0x3df03d0`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                     |
|:------:|:------:|:-------:|:---------|:----------------------------------------------------------------|
| 31:26  |        |         |          | Reserved                                                        |
| 25:16  |   rw   |  0x3df  | MAX_ADDR | Maximum address for Target Rx Descriptor Queue use (inclusive). |
| 15:10  |        |         |          | Reserved                                                        |
|  9:0   |   rw   |  0x3d0  | MIN_ADDR | Minimum address for Target Rx Descriptor Queue use.             |

## TARG_RXDESC_STATE
Target Reception Descriptor Queue State.
- Offset: `0xf8`
- Reset default: `0x3d003d0`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the queue is full.            |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x3d0  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x3d0  | WPTR   | Current write pointer.                     |

## TARG_IBIDESC_CONFIG
Target In-Band Interrupt Descriptor Queue Configuration.
- Offset: `0xfc`
- Reset default: `0x3ef03e0`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                      |
|:------:|:------:|:-------:|:---------|:-----------------------------------------------------------------|
| 31:26  |        |         |          | Reserved                                                         |
| 25:16  |   rw   |  0x3ef  | MAX_ADDR | Maximum address for Target IBI Descriptor Queue use (inclusive). |
| 15:10  |        |         |          | Reserved                                                         |
|  9:0   |   rw   |  0x3e0  | MIN_ADDR | Minimum address for Target IBI Descriptor Queue use.             |

## TARG_IBIDESC_STATE
Target In-Band Interrupt Descriptor Queue State.
- Offset: `0x100`
- Reset default: `0x3e003e0`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the queue is full.            |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x3e0  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x3e0  | WPTR   | Current write pointer.                     |

## TARG_ASYNC_CONFIG
Target Asynchronous Event Queue Configuration.
- Offset: `0x104`
- Reset default: `0x3ff03f0`
- Reset mask: `0x3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "MIN_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}, {"name": "MAX_ADDR", "bits": 10, "attr": ["rw"], "rotate": 0}, {"bits": 6}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                          |
|:------:|:------:|:-------:|:---------|:---------------------------------------------------------------------|
| 31:26  |        |         |          | Reserved                                                             |
| 25:16  |   rw   |  0x3ff  | MAX_ADDR | Maximum address for Target Asynchronous Event Queue use (inclusive). |
| 15:10  |        |         |          | Reserved                                                             |
|  9:0   |   rw   |  0x3f0  | MIN_ADDR | Minimum address for Target Asynchronous Event Queue use.             |

## TARG_ASYNC_STATE
Target Asynchronous Event Queue State.
- Offset: `0x108`
- Reset default: `0x3f003f0`
- Reset mask: `0xc3ff03ff`

### Fields

```wavejson
{"reg": [{"name": "WPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 6}, {"name": "RPTR", "bits": 10, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "PRE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "FULL", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                |
|:------:|:------:|:-------:|:-------|:-------------------------------------------|
|   31   |   ro   |   0x0   | FULL   | Indicates if the queue is full.            |
|   30   |   ro   |   0x0   | PRE    | Indicates if prefetched data is available. |
| 29:26  |        |         |        | Reserved                                   |
| 25:16  |   ro   |  0x3f0  | RPTR   | Current read pointer.                      |
| 15:10  |        |         |        | Reserved                                   |
|  9:0   |   ro   |  0x3f0  | WPTR   | Current write pointer.                     |

## HCI_VERSION
HCI Version.
- Offset: `0x180`
- Reset default: `0x120`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "VERSION", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description   |
|:------:|:------:|:-------:|:--------|:--------------|
|  31:0  |   ro   |  0x120  | VERSION | HCI Version.  |

## HC_CONTROL
Host Controller Control.
- Offset: `0x184`
- Reset default: `0x48`
- Reset mask: `0xe00011d9`

### Fields

```wavejson
{"reg": [{"name": "IBA_INCLUDE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 2}, {"name": "AUTOCMD_DATA_RPT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "DATA_BYTE_ORDER_MODE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}, {"name": "MODE_SELECTOR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "I2C_DEV_PRESENT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "HOT_JOIN_CTRL", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "HALT_ON_CMD_SEQ_TIMEOUT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 16}, {"name": "ABORT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RESUME", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "BUS_ENABLE", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 250}}
```

|  Bits  |  Type  |  Reset  | Name                    | Description                       |
|:------:|:------:|:-------:|:------------------------|:----------------------------------|
|   31   |   rw   |   0x0   | BUS_ENABLE              | Host Controller Bus Enable.       |
|   30   |   rw   |   0x0   | RESUME                  | Host Controller Resume.           |
|   29   |   rw   |   0x0   | ABORT                   | Host Controller Abort.            |
| 28:13  |        |         |                         | Reserved                          |
|   12   |   rw   |   0x0   | HALT_ON_CMD_SEQ_TIMEOUT | Halt on Command Sequence Timeout. |
|  11:9  |        |         |                         | Reserved                          |
|   8    |   rw   |   0x0   | HOT_JOIN_CTRL           | Hot-Join ACK/NACK Control.        |
|   7    |   rw   |   0x0   | I2C_DEV_PRESENT         | I2C Device Present on Bus.        |
|   6    |   ro   |   0x1   | MODE_SELECTOR           | DMA/PIO Mode Selector.            |
|   5    |        |         |                         | Reserved                          |
|   4    |   ro   |   0x0   | DATA_BYTE_ORDER_MODE    | Data Byte Ordering Mode.          |
|   3    |   rw   |   0x1   | AUTOCMD_DATA_RPT        | Auto-Command Data Report.         |
|  2:1   |        |         |                         | Reserved                          |
|   0    |   rw   |   0x0   | IBA_INCLUDE             | Include I3C Broadcast Address.    |

## CONTROLLER_DEVICE_ADDR
Controller Device Address.
- Offset: `0x188`
- Reset default: `0x0`
- Reset mask: `0x807f0000`

### Fields

```wavejson
{"reg": [{"bits": 16}, {"name": "DYNAMIC_ADDR", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 8}, {"name": "DYNAMIC_ADDR_VALID", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description               |
|:------:|:------:|:-------:|:-------------------|:--------------------------|
|   31   |   rw   |   0x0   | DYNAMIC_ADDR_VALID | Dynamic Address is Valid. |
| 30:23  |        |         |                    | Reserved                  |
| 22:16  |   rw   |   0x0   | DYNAMIC_ADDR       | Device Dynamic Address.   |
|  15:0  |        |         |                    | Reserved                  |

## HC_CAPABILITIES
Host Controller Capabilities.
- Offset: `0x18c`
- Reset default: `0x440`
- Reset mask: `0x70303cec`

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "COMBO_COMMAND", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "AUTO_COMMAND", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}, {"name": "STANDBY_CR_CAP", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "HDR_DDR_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "HDR_TS_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "CMD_CCC_DEFBYTE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "IBI_DATA_ABORT_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "IBI_CREDIT_COUNT_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SCHEDULED_COMMANDS_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 6}, {"name": "CMD_SIZE", "bits": 2, "attr": ["ro"], "rotate": -90}, {"bits": 6}, {"name": "SG_CAPABILITY_CR_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SG_CAPABILITY_IBI_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SG_CAPABILITY_DC_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                                                            |
|:------:|:------:|:-------:|:----------------------|:-------------------------------------------------------------------------------------------------------|
|   31   |        |         |                       | Reserved                                                                                               |
|   30   |   ro   |   0x0   | SG_CAPABILITY_DC_EN   | Defines whether the Host Controller supports Scatter-Gather for Device Context memory.                 |
|   29   |   ro   |   0x0   | SG_CAPABILITY_IBI_EN  | Defines whether the Host Controller supports Scatter-Gather for IBI Status and IBI Data Rings.         |
|   28   |   ro   |   0x0   | SG_CAPABILITY_CR_EN   | Defines whether the Host Controller supports Scatter-Gather for Command and Response Rings.            |
| 27:22  |        |         |                       | Reserved                                                                                               |
| 21:20  |   ro   |   0x0   | CMD_SIZE              | Defines the size and structure of the Command Descriptor supported by the Host Controller.             |
| 19:14  |        |         |                       | Reserved                                                                                               |
|   13   |   ro   |   0x0   | SCHEDULED_COMMANDS_EN | Defines whether the Host Controller supports Scheduled Commands capabilities.                          |
|   12   |   ro   |   0x0   | IBI_CREDIT_COUNT_EN   | Defines whether the Host Controller supports Target IBI Credit Counting.                               |
|   11   |   ro   |   0x0   | IBI_DATA_ABORT_EN     | Defines whether the Host Controller supports the IBI Data Abort operation.                             |
|   10   |   ro   |   0x1   | CMD_CCC_DEFBYTE       | Defines whether the Host Controller supports Transfer Commands that indicate CCCs with Defining Bytes. |
|  9:8   |        |         |                       | Reserved                                                                                               |
|   7    |   ro   |   0x0   | HDR_TS_EN             | Defines whether the Host Controller supports HDR-Ternary transfers.                                    |
|   6    |   ro   |   0x1   | HDR_DDR_EN            | Defines whether the Host Controller supports HDR-DDR transfers.                                        |
|   5    |   ro   |   0x0   | STANDBY_CR_CAP        | Defines whether the Host Controller supports handoff of the Active Controller role.                    |
|   4    |        |         |                       | Reserved                                                                                               |
|   3    |   ro   |   0x0   | AUTO_COMMAND          | Defines whether the Host Controller supports Auto-Command functionality.                               |
|   2    |   ro   |   0x0   | COMBO_COMMAND         | Defines whether the Host Controller supports Combo Transfer Command transfers.                         |
|  1:0   |        |         |                       | Reserved                                                                                               |

## RESET_CONTROL
Reset Control.
- Offset: `0x190`
- Reset default: `0x0`
- Reset mask: `0x3f`

### Fields

```wavejson
{"reg": [{"name": "SOFT_RST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "CMD_QUEUE_RST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RESP_QUEUE_RST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TX_FIFO_RST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RX_FIFO_RST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "IBI_QUEUE_RST", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                           |
|:------:|:------:|:-------:|:---------------|:--------------------------------------|
|  31:6  |        |         |                | Reserved                              |
|   5    |   wo   |   0x0   | IBI_QUEUE_RST  | IBI Queue Buffer Software Reset.      |
|   4    |   wo   |   0x0   | RX_FIFO_RST    | Receive Queue Buffer Software Reset.  |
|   3    |   wo   |   0x0   | TX_FIFO_RST    | Transmit Queue Buffer Software Reset. |
|   2    |   wo   |   0x0   | RESP_QUEUE_RST | Response Queue Software Reset.        |
|   1    |   wo   |   0x0   | CMD_QUEUE_RST  | Command Queue Software Reset.         |
|   0    |   wo   |   0x0   | SOFT_RST       | Core Software Reset.                  |

## PRESENT_STATE
Present State.
- Offset: `0x194`
- Reset default: `0x0`
- Reset mask: `0x4`

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "AC_CURRENT_OWN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description        |
|:------:|:------:|:-------:|:---------------|:-------------------|
|  31:3  |        |         |                | Reserved           |
|   2    |   ro   |   0x0   | AC_CURRENT_OWN | Active Controller. |
|  1:0   |        |         |                | Reserved           |

## INTR_STATUS
Interrupt Status.
- Offset: `0x1a0`
- Reset default: `0x0`
- Reset mask: `0x7c00`

### Fields

```wavejson
{"reg": [{"bits": 10}, {"name": "HC_INTERNAL_ERR_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "HC_SEQ_CANCEL_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "HC_WARN_CMD_SEQ_STALL_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "HC_ERR_CMD_SEQ_TIMEOUT_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "SCHED_CMD_MISSED_TICK_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 290}}
```

|  Bits  |  Type  |  Reset  | Name                        | Description                                     |
|:------:|:------:|:-------:|:----------------------------|:------------------------------------------------|
| 31:15  |        |         |                             | Reserved                                        |
|   14   |  rw1c  |   0x0   | SCHED_CMD_MISSED_TICK_STAT  | Scheduled Command Missed Tick.                  |
|   13   |  rw1c  |   0x0   | HC_ERR_CMD_SEQ_TIMEOUT_STAT | Host Controller Command Sequence Timeout.       |
|   12   |  rw1c  |   0x0   | HC_WARN_CMD_SEQ_STALL_STAT  | Host Controller Command Sequence Stall.         |
|   11   |  rw1c  |   0x0   | HC_SEQ_CANCEL_STAT          | Host Controller Cancelled Transaction Sequence. |
|   10   |  rw1c  |   0x0   | HC_INTERNAL_ERR_STAT        | Host Controller Internal Error.                 |
|  9:0   |        |         |                             | Reserved                                        |

## INTR_STATUS_ENABLE
Interrupt Status Enable.
- Offset: `0x1a4`
- Reset default: `0x0`
- Reset mask: `0x7c00`

### Fields

```wavejson
{"reg": [{"bits": 10}, {"name": "HC_INTERNAL_ERR_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "HC_SEQ_CANCEL_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "HC_WARN_CMD_SEQ_STALL_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "HC_ERR_CMD_SEQ_TIMEOUT_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "SCHED_CMD_MISSED_TICK_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 320}}
```

|  Bits  |  Type  |  Reset  | Name                           | Description                                                   |
|:------:|:------:|:-------:|:-------------------------------|:--------------------------------------------------------------|
| 31:15  |        |         |                                | Reserved                                                      |
|   14   |   rw   |   0x0   | SCHED_CMD_MISSED_TICK_STAT_EN  | Scheduled Command Missed Tick Status Enable.                  |
|   13   |   rw   |   0x0   | HC_ERR_CMD_SEQ_TIMEOUT_STAT_EN | Host Controller Command Sequence Timeout Status Enable.       |
|   12   |   rw   |   0x0   | HC_WARN_CMD_SEQ_STALL_STAT_EN  | Host Controller Command Sequence Stall Status Enable.         |
|   11   |   rw   |   0x0   | HC_SEQ_CANCEL_STAT_EN          | Host Controller Cancelled Transaction Sequence Status Enable. |
|   10   |   rw   |   0x0   | HC_INTERNAL_ERR_STAT_EN        | Host Controller Internal Error Status Enable.                 |
|  9:0   |        |         |                                | Reserved                                                      |

## INTR_SIGNAL_ENABLE
Interrupt Signal Enable.
- Offset: `0x1a8`
- Reset default: `0x0`
- Reset mask: `0x7c00`

### Fields

```wavejson
{"reg": [{"bits": 10}, {"name": "HC_INTERNAL_ERR_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "HC_SEQ_CANCEL_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "HC_WARN_CMD_SEQ_STALL_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "HC_ERR_CMD_SEQ_TIMEOUT_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "SCHED_CMD_MISSED_TICK_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 340}}
```

|  Bits  |  Type  |  Reset  | Name                             | Description                                                   |
|:------:|:------:|:-------:|:---------------------------------|:--------------------------------------------------------------|
| 31:15  |        |         |                                  | Reserved                                                      |
|   14   |   rw   |   0x0   | SCHED_CMD_MISSED_TICK_SIGNAL_EN  | Scheduled Command Missed Tick Signal Enable.                  |
|   13   |   rw   |   0x0   | HC_ERR_CMD_SEQ_TIMEOUT_SIGNAL_EN | Host Controller Command Sequence Timeout Signal Enable.       |
|   12   |   rw   |   0x0   | HC_WARN_CMD_SEQ_STALL_SIGNAL_EN  | Host Controller Command Sequence Stall Signal Enable.         |
|   11   |   rw   |   0x0   | HC_SEQ_CANCEL_SIGNAL_EN          | Host Controller Cancelled Transaction Sequence Signal Enable. |
|   10   |   rw   |   0x0   | HC_INTERNAL_ERR_SIGNAL_EN        | Host Controller Internal Error Signal Enable.                 |
|  9:0   |        |         |                                  | Reserved                                                      |

## INTR_FORCE
Interrupt Force.
- Offset: `0x1ac`
- Reset default: `0x0`
- Reset mask: `0x7c00`

### Fields

```wavejson
{"reg": [{"bits": 10}, {"name": "HC_INTERNAL_ERR_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "HC_SEQ_CANCEL_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "HC_WARN_CMD_SEQ_STALL_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "HC_ERR_CMD_SEQ_TIMEOUT_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "SCHED_CMD_MISSED_TICK_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 17}], "config": {"lanes": 1, "fontsize": 10, "vspace": 300}}
```

|  Bits  |  Type  |  Reset  | Name                         | Description                                           |
|:------:|:------:|:-------:|:-----------------------------|:------------------------------------------------------|
| 31:15  |        |         |                              | Reserved                                              |
|   14   |   wo   |   0x0   | SCHED_CMD_MISSED_TICK_FORCE  | Force Scheduled Command Missed Tick.                  |
|   13   |   wo   |   0x0   | HC_ERR_CMD_SEQ_TIMEOUT_FORCE | Force Host Controller Command Sequence Timeout.       |
|   12   |   wo   |   0x0   | HC_WARN_CMD_SEQ_STALL_FORCE  | Force Host Controller Command Sequence Stall.         |
|   11   |   wo   |   0x0   | HC_SEQ_CANCEL_FORCE          | Force Host Controller Cancelled Transaction Sequence. |
|   10   |   wo   |   0x0   | HC_INTERNAL_ERR_FORCE        | Force Host Controller Internal Error.                 |
|  9:0   |        |         |                              | Reserved                                              |

## DAT_SECTION_OFFSET
Device Address Table Section Offset.
- Offset: `0x1b0`
- Reset default: `0x20880`
- Reset mask: `0xf007ffff`

### Fields

```wavejson
{"reg": [{"name": "TABLE_OFFSET", "bits": 12, "attr": ["ro"], "rotate": 0}, {"name": "TABLE_SIZE", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 9}, {"name": "ENTRY_SIZE", "bits": 4, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 120}}
```

|  Bits  |  Type  |  Reset  | Name         | Description       |
|:------:|:------:|:-------:|:-------------|:------------------|
| 31:28  |   ro   |   0x0   | ENTRY_SIZE   | DAT Entry size.   |
| 27:19  |        |         |              | Reserved          |
| 18:12  |   ro   |  0x20   | TABLE_SIZE   | DAT Table Size.   |
|  11:0  |   ro   |  0x880  | TABLE_OFFSET | DAT Table Offset. |

## DCT_SECTION_OFFSET
Device Characteristics Table Section Offset.
- Offset: `0x1b4`
- Reset default: `0x20a80`
- Reset mask: `0xf0ffffff`

### Fields

```wavejson
{"reg": [{"name": "TABLE_OFFSET", "bits": 12, "attr": ["ro"], "rotate": 0}, {"name": "TABLE_SIZE", "bits": 7, "attr": ["ro"], "rotate": 0}, {"name": "TABLE_INDEX", "bits": 5, "attr": ["rw"], "rotate": -90}, {"bits": 4}, {"name": "ENTRY_SIZE", "bits": 4, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name         | Description       |
|:------:|:------:|:-------:|:-------------|:------------------|
| 31:28  |   ro   |   0x0   | ENTRY_SIZE   | DCT Entry size.   |
| 27:24  |        |         |              | Reserved          |
| 23:19  |   rw   |   0x0   | TABLE_INDEX  | DCT Table Index.  |
| 18:12  |   ro   |  0x20   | TABLE_SIZE   | DCT Table Size.   |
|  11:0  |   ro   |  0xa80  | TABLE_OFFSET | DCT Table Offset. |

## RING_HEADERS_SECTION_OFFSET
Ring Headers Section Offset.
- Offset: `0x1b8`
- Reset default: `0x0`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "SECTION_OFFSET", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                  |
|:------:|:------:|:-------:|:---------------|:-----------------------------|
| 31:16  |        |         |                | Reserved                     |
|  15:0  |   ro   |   0x0   | SECTION_OFFSET | Ring Headers Section Offset. |

## PIO_SECTION_OFFSET
PIO Section Offset.
- Offset: `0x1bc`
- Reset default: `0x80`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "SECTION_OFFSET", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description         |
|:------:|:------:|:-------:|:---------------|:--------------------|
| 31:16  |        |         |                | Reserved            |
|  15:0  |   ro   |  0x80   | SECTION_OFFSET | PIO Section Offset. |

## EXT_CAPS_SECTION_OFFSET
Extended Capabilities Section Offset.
- Offset: `0x1c0`
- Reset default: `0x120`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "SECTION_OFFSET", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                           |
|:------:|:------:|:-------:|:---------------|:--------------------------------------|
| 31:16  |        |         |                | Reserved                              |
|  15:0  |   ro   |  0x120  | SECTION_OFFSET | Extended Capabilities Section Offset. |

## INT_CTRL_CMDS_EN
Internal Control Command Subtype Support.
- Offset: `0x1cc`
- Reset default: `0x61`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "ICC_SUPPORT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "MIPI_CMDS_SUPPORTED", "bits": 15, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                          |
|:------:|:------:|:-------:|:--------------------|:-------------------------------------|
| 31:16  |        |         |                     | Reserved                             |
|  15:1  |   ro   |  0x30   | MIPI_CMDS_SUPPORTED | MIPI Alliance Commands Supported.    |
|   0    |   ro   |   0x1   | ICC_SUPPORT         | Internal Control Commands Supported. |

## IBI_NOTIFY_CTRL
IBI Notify Control.
- Offset: `0x1d8`
- Reset default: `0x0`
- Reset mask: `0xb`

### Fields

```wavejson
{"reg": [{"name": "NOTIFY_HJ_REJECTED", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "NOTIFY_CRR_REJECTED", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "NOTIFY_IBI_REJECTED", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                        |
|:------:|:------:|:-------:|:--------------------|:---------------------------------------------------|
|  31:4  |        |         |                     | Reserved                                           |
|   3    |   rw   |   0x0   | NOTIFY_IBI_REJECTED | Notify Rejected In-Band Interrupt Request Control. |
|   2    |        |         |                     | Reserved                                           |
|   1    |   rw   |   0x0   | NOTIFY_CRR_REJECTED | Notify Rejected Controller Role Request Control.   |
|   0    |   rw   |   0x0   | NOTIFY_HJ_REJECTED  | Notify Rejected Hot-Join Control.                  |

## IBI_DATA_ABORT_CTRL
IBI Data Abort Control.
- Offset: `0x1dc`
- Reset default: `0x0`
- Reset mask: `0x801fff00`

### Fields

```wavejson
{"reg": [{"bits": 8}, {"name": "MATCH_IBI_ID", "bits": 8, "attr": ["wo"], "rotate": 0}, {"name": "AFTER_N_CHUNKS", "bits": 2, "attr": ["wo"], "rotate": -90}, {"name": "MATCH_STATUS_TYPE", "bits": 3, "attr": ["wo"], "rotate": -90}, {"bits": 10}, {"name": "IBI_DATA_ABORT_MON", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description               |
|:------:|:------:|:-------:|:-------------------|:--------------------------|
|   31   |   rw   |   0x0   | IBI_DATA_ABORT_MON | IBI Data Abort Monitor.   |
| 30:21  |        |         |                    | Reserved                  |
| 20:18  |   wo   |   0x0   | MATCH_STATUS_TYPE  | Match IBI Status Type.    |
| 17:16  |   wo   |   0x0   | AFTER_N_CHUNKS     | Abort After N Chunks.     |
|  15:8  |   wo   |   0x0   | MATCH_IBI_ID       | Match IBI Target Address. |
|  7:0   |        |         |                    | Reserved                  |

## DEV_CTX_BASE_LO
Device Context Base Address Low.
- Offset: `0x1e0`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BASE_LO", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description              |
|:------:|:------:|:-------:|:--------|:-------------------------|
|  31:0  |   ro   |   0x0   | BASE_LO | Device Context Base Low. |

## DEV_CTX_BASE_HI
Device Context Base Address High.
- Offset: `0x1e4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "BASE_HI", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name    | Description               |
|:------:|:------:|:-------:|:--------|:--------------------------|
|  31:0  |   ro   |   0x0   | BASE_HI | Device Context Base High. |

## DEV_CTX_SG
Device Context Scatter-Gather Support.
- Offset: `0x1e8`
- Reset default: `0x0`
- Reset mask: `0x8000ffff`

### Fields

```wavejson
{"reg": [{"name": "LIST_SIZE", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 15}, {"name": "BLP", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description              |
|:------:|:------:|:-------:|:----------|:-------------------------|
|   31   |   ro   |   0x0   | BLP       | Buffer Vs. List Pointer. |
| 30:16  |        |         |           | Reserved                 |
|  15:0  |   ro   |   0x0   | LIST_SIZE | List Size.               |

## HCI_PORTS
HCI ports, occupying successive word addresses:

- COMMAND_QUEUE_PORT - Write-only Command Descriptor queue.
- RESPONSE_QUEUE_PORT - Read-only Response Descriptor queue.
- XFER_DATA_PORT - Read/write data buffer; Rx Data Buffer and Tx Data Buffer.
- IBI_PORT - Read-only In-Band Interrupt queue.

- Word Aligned Offset Range: `0x200`to`0x20c`
- Size (words): `4`
- Access: `rw`
- Byte writes are *not* supported.

## QUEUE_THLD_CTRL
Queue Threshold Control.
- Offset: `0x210`
- Reset default: `0x1010101`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CMD_EMPTY_BUF_THLD", "bits": 8, "attr": ["rw"], "rotate": -90}, {"name": "RESP_BUF_THLD", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "IBI_DATA_SEGMENT_SIZE", "bits": 8, "attr": ["rw"], "rotate": -90}, {"name": "IBI_STATUS_THLD", "bits": 8, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                      |
|:------:|:------:|:-------:|:----------------------|:---------------------------------|
| 31:24  |   rw   |   0x1   | IBI_STATUS_THLD       | IBI Status Threshold.            |
| 23:16  |   rw   |   0x1   | IBI_DATA_SEGMENT_SIZE | IBI Data Segment Size.           |
|  15:8  |   rw   |   0x1   | RESP_BUF_THLD         | Response Ready Buffer Threshold. |
|  7:0   |   rw   |   0x1   | CMD_EMPTY_BUF_THLD    | Command Ready Buffer Threshold.  |

## DATA_BUFFER_THLD_CTRL
Transfer Data Buffer Threshold Control.
- Offset: `0x214`
- Reset default: `0x1010101`
- Reset mask: `0x7070707`

### Fields

```wavejson
{"reg": [{"name": "TX_BUF_THLD", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "RX_BUF_THLD", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "TX_START_THLD", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "RX_START_THLD", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 5}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                                                                                                     |
|:------:|:------:|:-------:|:--------------|:------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:27  |        |         |               | Reserved                                                                                                                                        |
| 26:24  |   rw   |   0x1   | RX_START_THLD | Receive Start Threshold in DWORDs. Wait until there are at least 2^(N+1) DWORD entries available before starting a Read Transfer.               |
| 23:19  |        |         |               | Reserved                                                                                                                                        |
| 18:16  |   rw   |   0x1   | TX_START_THLD | Transmit (Transfer) Start Threshold in DWORDs. Wait until there are at least 2^(N+1) DWORDs of data available before starting a Write Transfer. |
| 15:11  |        |         |               | Reserved                                                                                                                                        |
|  10:8  |   rw   |   0x1   | RX_BUF_THLD   | Receive Buffer Threshold. Interrupt triggers when there are at least 2^(N+1) Rx Buffer DWORDs of data available.                                |
|  7:3   |        |         |               | Reserved                                                                                                                                        |
|  2:0   |   rw   |   0x1   | TX_BUF_THLD   | Transmit Buffer Threshold. Interrupt triggers when there are at least 2^(N+1) Tx Buffer DWORD entries available.                                |

## QUEUE_SIZE
Queue Size.
- Offset: `0x218`
- Reset default: `0x6060808`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "CR_QUEUE_SIZE", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "IBI_STATUS_SIZE", "bits": 8, "attr": ["ro"], "rotate": -90}, {"name": "RX_DATA_BUFFER_SIZE", "bits": 8, "attr": ["ro"], "rotate": -90}, {"name": "TX_DATA_BUFFER_SIZE", "bits": 8, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                  |
|:------:|:------:|:-------:|:--------------------|:-----------------------------|
| 31:24  |   ro   |   0x6   | TX_DATA_BUFFER_SIZE | Transmit Data Buffer Size.   |
| 23:16  |   ro   |   0x6   | RX_DATA_BUFFER_SIZE | Receive Data Buffer Size.    |
|  15:8  |   ro   |   0x8   | IBI_STATUS_SIZE     | IBI Queue Size.              |
|  7:0   |   ro   |   0x8   | CR_QUEUE_SIZE       | Command/Response Queue Size. |

## ALT_QUEUE_SIZE
Alternate Queue Size.
- Offset: `0x21c`
- Reset default: `0x10000000`
- Reset mask: `0x110000ff`

### Fields

```wavejson
{"reg": [{"name": "ALT_RESP_QUEUE_SIZE", "bits": 8, "attr": ["ro"], "rotate": -90}, {"bits": 16}, {"name": "ALT_RESP_QUEUE_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 3}, {"name": "EXT_IBI_QUEUE_EN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 3}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                    |
|:------:|:------:|:-------:|:--------------------|:-------------------------------|
| 31:29  |        |         |                     | Reserved                       |
|   28   |   ro   |   0x1   | EXT_IBI_QUEUE_EN    | Extended IBI Queue Size.       |
| 27:25  |        |         |                     | Reserved                       |
|   24   |   ro   |   0x0   | ALT_RESP_QUEUE_EN   | Alternate Response Queue.      |
|  23:8  |        |         |                     | Reserved                       |
|  7:0   |   ro   |   0x0   | ALT_RESP_QUEUE_SIZE | Alternate Response Queue Size. |

## PIO_INTR_STATUS
PIO Interrupt Status.
- Offset: `0x220`
- Reset default: `0x0`
- Reset mask: `0x23f`

### Fields

```wavejson
{"reg": [{"name": "TX_THLD_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "RX_THLD_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "IBI_STATUS_THLD_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "CMD_QUEUE_READY_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "RESP_READY_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "TRANSFER_ABORT_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 3}, {"name": "TRANSFER_ERR_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                      |
|:------:|:------:|:-------:|:---------------------|:---------------------------------|
| 31:10  |        |         |                      | Reserved                         |
|   9    |  rw1c  |   0x0   | TRANSFER_ERR_STAT    | Transfer Error Status.           |
|  8:6   |        |         |                      | Reserved                         |
|   5    |  rw1c  |   0x0   | TRANSFER_ABORT_STAT  | Transfer Abort Status.           |
|   4    |  rw1c  |   0x0   | RESP_READY_STAT      | Response Ready Status.           |
|   3    |  rw1c  |   0x0   | CMD_QUEUE_READY_STAT | Command Queue Ready Status.      |
|   2    |  rw1c  |   0x0   | IBI_STATUS_THLD_STAT | IBI Status Threshold Status.     |
|   1    |  rw1c  |   0x0   | RX_THLD_STAT         | Rx Data Buffer Threshold Status. |
|   0    |  rw1c  |   0x0   | TX_THLD_STAT         | Tx Data Buffer Threshold Status. |

## PIO_INTR_STATUS_ENABLE
PIO Interrupt Status Enable.
- Offset: `0x224`
- Reset default: `0x0`
- Reset mask: `0x23f`

### Fields

```wavejson
{"reg": [{"name": "TX_THLD_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RX_THLD_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "IBI_STATUS_THLD_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CMD_QUEUE_READY_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RESP_READY_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TRANSFER_ABORT_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "TRANSFER_ERR_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 250}}
```

|  Bits  |  Type  |  Reset  | Name                    | Description                             |
|:------:|:------:|:-------:|:------------------------|:----------------------------------------|
| 31:10  |        |         |                         | Reserved                                |
|   9    |   rw   |   0x0   | TRANSFER_ERR_STAT_EN    | Transfer Error Status Enable.           |
|  8:6   |        |         |                         | Reserved                                |
|   5    |   rw   |   0x0   | TRANSFER_ABORT_STAT_EN  | Transfer Abort Status Enable.           |
|   4    |   rw   |   0x0   | RESP_READY_STAT_EN      | Response Ready Status Enable.           |
|   3    |   rw   |   0x0   | CMD_QUEUE_READY_STAT_EN | Command Queue Ready Status Enable.      |
|   2    |   rw   |   0x0   | IBI_STATUS_THLD_STAT_EN | IBI Status Threshold Status Enable.     |
|   1    |   rw   |   0x0   | RX_THLD_STAT_EN         | Rx Data Buffer Threshold Status Enable. |
|   0    |   rw   |   0x0   | TX_THLD_STAT_EN         | Tx Data Buffer Threshold Status Enable. |

## PIO_INTR_SIGNAL_ENABLE
PIO Interrupt Signal Enable.
- Offset: `0x228`
- Reset default: `0x0`
- Reset mask: `0x23f`

### Fields

```wavejson
{"reg": [{"name": "TX_THLD_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RX_THLD_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "IBI_STATUS_THLD_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CMD_QUEUE_READY_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RESP_READY_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TRANSFER_ABORT_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 3}, {"name": "TRANSFER_ERR_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 270}}
```

|  Bits  |  Type  |  Reset  | Name                      | Description                             |
|:------:|:------:|:-------:|:--------------------------|:----------------------------------------|
| 31:10  |        |         |                           | Reserved                                |
|   9    |   rw   |   0x0   | TRANSFER_ERR_SIGNAL_EN    | Transfer Error Signal Enable.           |
|  8:6   |        |         |                           | Reserved                                |
|   5    |   rw   |   0x0   | TRANSFER_ABORT_SIGNAL_EN  | Transfer Abort Signal Enable.           |
|   4    |   rw   |   0x0   | RESP_READY_SIGNAL_EN      | Response Ready Signal Enable.           |
|   3    |   rw   |   0x0   | CMD_QUEUE_READY_SIGNAL_EN | Command Queue Ready Signal Enable.      |
|   2    |   rw   |   0x0   | IBI_STATUS_THLD_SIGNAL_EN | IBI Status Threshold Signal Enable.     |
|   1    |   rw   |   0x0   | RX_THLD_SIGNAL_EN         | Rx Data Buffer Threshold Signal Enable. |
|   0    |   rw   |   0x0   | TX_THLD_SIGNAL_EN         | Tx Data Buffer Threshold Signal Enable. |

## PIO_INTR_FORCE
PIO Interrupt Force.
- Offset: `0x22c`
- Reset default: `0x0`
- Reset mask: `0x23f`

### Fields

```wavejson
{"reg": [{"name": "TX_THLD_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RX_THLD_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "IBI_THLD_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "CMD_QUEUE_READY_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RESP_READY_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TRANSFER_ABORT_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 3}, {"name": "TRANSFER_ERR_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 22}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                     |
|:------:|:------:|:-------:|:----------------------|:--------------------------------|
| 31:10  |        |         |                       | Reserved                        |
|   9    |   wo   |   0x0   | TRANSFER_ERR_FORCE    | Force Transfer Error.           |
|  8:6   |        |         |                       | Reserved                        |
|   5    |   wo   |   0x0   | TRANSFER_ABORT_FORCE  | Force Transfer Abort.           |
|   4    |   wo   |   0x0   | RESP_READY_FORCE      | Force Response Ready.           |
|   3    |   wo   |   0x0   | CMD_QUEUE_READY_FORCE | Force Command Queue Ready.      |
|   2    |   wo   |   0x0   | IBI_THLD_FORCE        | Force IBI Status Threshold.     |
|   1    |   wo   |   0x0   | RX_THLD_FORCE         | Force Rx Data Buffer Threshold. |
|   0    |   wo   |   0x0   | TX_THLD_FORCE         | Force Tx Data Buffer Threshold. |

## PIO_CONTROL
PIO Control.
- Offset: `0x230`
- Reset default: `0x1`
- Reset mask: `0x7`

### Fields

```wavejson
{"reg": [{"name": "ENABLE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RS", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ABORT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                |
|:------:|:------:|:-------:|:-------|:---------------------------|
|  31:3  |        |         |        | Reserved                   |
|   2    |   rw   |   0x0   | ABORT  | PIO Abort Request.         |
|   1    |   rw   |   0x0   | RS     | PIO Run/Stop Request.      |
|   0    |   rw   |   0x1   | ENABLE | PIO Queues Enable Request. |

## ID_EXTCAP_HEADER
Hardware Identification Extended Capability Header
- Offset: `0x2a0`
- Reset default: `0x401`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "CAP_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CAP_LENGTH", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                            |
|:------:|:------:|:-------:|:-----------|:---------------------------------------|
| 31:24  |        |         |            | Reserved                               |
|  23:8  |   ro   |   0x4   | CAP_LENGTH | Capability Structure Length in DWORDs. |
|  7:0   |   ro   |   0x1   | CAP_ID     | Extended Capability ID                 |

## COMP_MANUFACTURER
Component Manufacturer.
- Offset: `0x2a4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "MIPI_VENDOR_ID", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                            |
|:------:|:------:|:-------:|:---------------|:-------------------------------------------------------|
|  31:0  |   ro   |   0x0   | MIPI_VENDOR_ID | MIPI-assigned Manufacturer ID for the Host Controller. |

## COMP_VERSION
Component Version.
- Offset: `0x2a8`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "I3C_VER_ID", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                |
|:------:|:------:|:-------:|:-----------|:-----------------------------------------------------------|
|  31:0  |   ro   |   0x0   | I3C_VER_ID | Vendor-assigned component version for the Host Controller. |

## COMP_TYPE
Component Type.
- Offset: `0x2ac`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "I3C_PRODUCT_ID", "bits": 32, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                             |
|:------:|:------:|:-------:|:---------------|:--------------------------------------------------------|
|  31:0  |   ro   |   0x0   | I3C_PRODUCT_ID | Vendor-assigned component type for the Host Controller. |

## CTRL_CFG_EXTCAP_HEADER
Controller Config Extended Capability Header
- Offset: `0x2b0`
- Reset default: `0x202`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "CAP_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CAP_LENGTH", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                            |
|:------:|:------:|:-------:|:-----------|:---------------------------------------|
| 31:24  |        |         |            | Reserved                               |
|  23:8  |   ro   |   0x2   | CAP_LENGTH | Capability Structure Length in DWORDs. |
|  7:0   |   ro   |   0x2   | CAP_ID     | Extended Capability ID                 |

## CONTROLLER_CONFIG
Controller Config.
- Offset: `0x2b4`
- Reset default: `0x10`
- Reset mask: `0x30`

### Fields

```wavejson
{"reg": [{"bits": 4}, {"name": "OPERATION_MODE", "bits": 2, "attr": ["ro"], "rotate": -90}, {"bits": 26}], "config": {"lanes": 1, "fontsize": 10, "vspace": 160}}
```

|  Bits  |  Type  |  Reset  | Name           | Description                                                                                                                                                          |
|:------:|:------:|:-------:|:---------------|:---------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|  31:6  |        |         |                | Reserved                                                                                                                                                             |
|  5:4   |   ro   |   0x1   | OPERATION_MODE | Controller Operation Mode. 0x1 : Controller Role functionality only. 0x2 : Target Role functionality only. 0x3 : Both Controller Role and Target Role functionality. |
|  3:0   |        |         |                | Reserved                                                                                                                                                             |

## DBR_EXTCAP_HEADER
Dead Bus Recovery Extended Capability Header
- Offset: `0x2b8`
- Reset default: `0x20b`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "CAP_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CAP_LENGTH", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                            |
|:------:|:------:|:-------:|:-----------|:---------------------------------------|
| 31:24  |        |         |            | Reserved                               |
|  23:8  |   ro   |   0x2   | CAP_LENGTH | Capability Structure Length in DWORDs. |
|  7:0   |   ro   |   0xb   | CAP_ID     | Extended Capability ID                 |

## DBR_ENGAGE
Dead Bus Recovery Engage.
- Offset: `0x2bc`
- Reset default: `0x0`
- Reset mask: `0x7f037f`

### Fields

```wavejson
{"reg": [{"name": "DBR_VERIF_KEY", "bits": 4, "attr": ["wo"], "rotate": -90}, {"name": "DBR_MODE", "bits": 3, "attr": ["wo"], "rotate": -90}, {"bits": 1}, {"name": "DBR_ASX_TIMING", "bits": 2, "attr": ["wo"], "rotate": -90}, {"bits": 6}, {"name": "DBR_IBI_ADDRESS", "bits": 7, "attr": ["wo"], "rotate": -90}, {"bits": 9}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description            |
|:------:|:------:|:-------:|:----------------|:-----------------------|
| 31:23  |        |         |                 | Reserved               |
| 22:16  |   wo   |   0x0   | DBR_IBI_ADDRESS | IBI Address.           |
| 15:10  |        |         |                 | Reserved               |
|  9:8   |   wo   |   0x0   | DBR_ASX_TIMING  | Activity State Timing. |
|   7    |        |         |                 | Reserved               |
|  6:4   |   wo   |   0x0   | DBR_MODE        | Engagement Mode.       |
|  3:0   |   wo   |   0x0   | DBR_VERIF_KEY   | Verification Key.      |

## DEBUG_EXTCAP_HEADER
Debug Specific Extended Capability Header
- Offset: `0x2c0`
- Reset default: `0x60c`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "CAP_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CAP_LENGTH", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                            |
|:------:|:------:|:-------:|:-----------|:---------------------------------------|
| 31:24  |        |         |            | Reserved                               |
|  23:8  |   ro   |   0x6   | CAP_LENGTH | Capability Structure Length in DWORDs. |
|  7:0   |   ro   |   0xc   | CAP_ID     | Extended Capability ID                 |

## QUEUE_STATUS_LEVEL
Queue Status Level
- Offset: `0x2c4`
- Reset default: `0x10`
- Reset mask: `0x1fffffff`

### Fields

```wavejson
{"reg": [{"name": "CMD_QUEUE_FREE_LVL", "bits": 8, "attr": ["ro"], "rotate": -90}, {"name": "RESPONSE_BUFFER_LVL", "bits": 8, "attr": ["ro"], "rotate": -90}, {"name": "IBI_BUFFER_LVL", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "IBI_STATUS_CNT", "bits": 5, "attr": ["ro"], "rotate": -90}, {"bits": 3}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                      |
|:------:|:------:|:-------:|:--------------------|:---------------------------------|
| 31:29  |        |         |                     | Reserved                         |
| 28:24  |   ro   |   0x0   | IBI_STATUS_CNT      | IBI Buffer Status Count.         |
| 23:16  |   ro   |   0x0   | IBI_BUFFER_LVL      | IBI Buffer Level.                |
|  15:8  |   ro   |   0x0   | RESPONSE_BUFFER_LVL | Response Buffer Level.           |
|  7:0   |   ro   |  0x10   | CMD_QUEUE_FREE_LVL  | Command Queue Free Buffer Level. |

## DATA_BUFFER_STATUS_LEVEL
Data Buffer Status Level
- Offset: `0x2c8`
- Reset default: `0x80`
- Reset mask: `0xffff`

### Fields

```wavejson
{"reg": [{"name": "TX_BUF_FREE_LVL", "bits": 8, "attr": ["ro"], "rotate": -90}, {"name": "RX_BUF_LVL", "bits": 8, "attr": ["ro"], "rotate": 0}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                  |
|:------:|:------:|:-------:|:----------------|:-----------------------------|
| 31:16  |        |         |                 | Reserved                     |
|  15:8  |   ro   |   0x0   | RX_BUF_LVL      | Rx Data Buffer Status Count. |
|  7:0   |   ro   |  0x80   | TX_BUF_FREE_LVL | Tx Data Buffer Status Count. |

## PRESENT_STATE_DEBUG
Present State Debug
- Offset: `0x2cc`
- Reset default: `0x3`
- Reset mask: `0xf3f3f03`

### Fields

```wavejson
{"reg": [{"name": "SCL_LINE_SIGNAL_LEVEL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SDA_LINE_SIGNAL_LEVEL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 6}, {"name": "BCL_TFR_STATUS", "bits": 6, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "BCL_TFR_ST_STATUS", "bits": 6, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "CMD_TID", "bits": 4, "attr": ["ro"], "rotate": -90}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                |
|:------:|:------:|:-------:|:----------------------|:-------------------------------------------|
| 31:28  |        |         |                       | Reserved                                   |
| 27:24  |   ro   |   0x0   | CMD_TID               | Command Transaction ID.                    |
| 23:22  |        |         |                       | Reserved                                   |
| 21:16  |   ro   |   0x0   | BCL_TFR_ST_STATUS     | Bus Controller Logic State.                |
| 15:14  |        |         |                       | Reserved                                   |
|  13:8  |   ro   |   0x0   | BCL_TFR_STATUS        | Bus Controller Logic Transfer Type Status. |
|  7:2   |        |         |                       | Reserved                                   |
|   1    |   ro   |   0x1   | SDA_LINE_SIGNAL_LEVEL | SDA Line Signal Level.                     |
|   0    |   ro   |   0x1   | SCL_LINE_SIGNAL_LEVEL | SCL Line Signal Level.                     |

## MX_ERROR_COUNTERS
Controller Error Counters.
- Offset: `0x2d0`
- Reset default: `0x0`
- Reset mask: `0xff`

### Fields

```wavejson
{"reg": [{"name": "CE2_ERROR_COUNT", "bits": 8, "attr": ["ro"], "rotate": -90}, {"bits": 24}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description        |
|:------:|:------:|:-------:|:----------------|:-------------------|
|  31:8  |        |         |                 | Reserved           |
|  7:0   |   ro   |   0x0   | CE2_ERROR_COUNT | CE2 Error Counter. |

## SCHED_CMDS_DEBUG
Scheduled Commands Debug
- Offset: `0x2d4`
- Reset default: `0x0`
- Reset mask: `0x3fffff`

### Fields

```wavejson
{"reg": [{"name": "SCHED_HANDLER", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "INST_ID", "bits": 3, "attr": ["ro"], "rotate": -90}, {"name": "ERR_TYPE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ENTITY_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "TICK_INTERVAL", "bits": 5, "attr": ["ro"], "rotate": -90}, {"name": "ERR_OCCURRED", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 10}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                     |
|:------:|:------:|:-------:|:--------------|:--------------------------------|
| 31:22  |        |         |               | Reserved                        |
|   21   |   ro   |   0x0   | ERR_OCCURRED  | Error Occurred.                 |
| 20:16  |   ro   |   0x0   | TICK_INTERVAL | Tick Interval Number.           |
|  15:8  |   ro   |   0x0   | ENTITY_ID     | Entity ID.                      |
|   7    |   ro   |   0x0   | ERR_TYPE      | Error Type.                     |
|  6:4   |   ro   |   0x0   | INST_ID       | Instance ID.                    |
|  3:0   |   ro   |   0x0   | SCHED_HANDLER | Scheduled Command Handler Type. |

## STBY_CR_EXTCAP_HEADER
Standby Controller Extended Capability Header
- Offset: `0x2d8`
- Reset default: `0xe12`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "CAP_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CAP_LENGTH", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                            |
|:------:|:------:|:-------:|:-----------|:---------------------------------------|
| 31:24  |        |         |            | Reserved                               |
|  23:8  |   ro   |   0xe   | CAP_LENGTH | Capability Structure Length in DWORDs. |
|  7:0   |   ro   |  0x12   | CAP_ID     | Extended Capability ID                 |

## STBY_CR_CONTROL
Standby Controller Control
- Offset: `0x2dc`
- Reset default: `0x100c`
- Reset mask: `0xc010f73f`

### Fields

```wavejson
{"reg": [{"name": "PENDING_RX_NACK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "HANDOFF_DELAY_NACK", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ACR_FSM_OP_SELECT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "PRIME_ACCEPT_GETACCCR", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "HANDOFF_DEEP_SLEEP", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CR_REQUEST_SEND", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 2}, {"name": "BCAST_CCC_IBI_RING", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "TARGET_XACT_ENABLE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "DAA_SETAASA_ENABLE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "DAA_SETDASA_ENABLE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "DAA_ENTDAA_ENABLE", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 4}, {"name": "RSTACT_DEFBYTE_02", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 9}, {"name": "STBY_CR_ENABLE_INIT", "bits": 2, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                                                             |
|:------:|:------:|:-------:|:-----------------------------------------------------------------|
| 31:30  |   rw   |   0x0   | [STBY_CR_ENABLE_INIT](#stby_cr_control--stby_cr_enable_init)     |
| 29:21  |        |         | Reserved                                                         |
|   20   |   rw   |   0x0   | [RSTACT_DEFBYTE_02](#stby_cr_control--rstact_defbyte_02)         |
| 19:16  |        |         | Reserved                                                         |
|   15   |   rw   |   0x0   | [DAA_ENTDAA_ENABLE](#stby_cr_control--daa_entdaa_enable)         |
|   14   |   rw   |   0x0   | [DAA_SETDASA_ENABLE](#stby_cr_control--daa_setdasa_enable)       |
|   13   |   rw   |   0x0   | [DAA_SETAASA_ENABLE](#stby_cr_control--daa_setaasa_enable)       |
|   12   |   rw   |   0x1   | [TARGET_XACT_ENABLE](#stby_cr_control--target_xact_enable)       |
|   11   |        |         | Reserved                                                         |
|  10:8  |   rw   |   0x0   | [BCAST_CCC_IBI_RING](#stby_cr_control--bcast_ccc_ibi_ring)       |
|  7:6   |        |         | Reserved                                                         |
|   5    |   rw   |   0x0   | [CR_REQUEST_SEND](#stby_cr_control--cr_request_send)             |
|   4    |   rw   |   0x0   | [HANDOFF_DEEP_SLEEP](#stby_cr_control--handoff_deep_sleep)       |
|   3    |   rw   |   0x1   | [PRIME_ACCEPT_GETACCCR](#stby_cr_control--prime_accept_getacccr) |
|   2    |   rw   |   0x1   | [ACR_FSM_OP_SELECT](#stby_cr_control--acr_fsm_op_select)         |
|   1    |   rw   |   0x0   | [HANDOFF_DELAY_NACK](#stby_cr_control--handoff_delay_nack)       |
|   0    |   rw   |   0x0   | [PENDING_RX_NACK](#stby_cr_control--pending_rx_nack)             |

### STBY_CR_CONTROL . STBY_CR_ENABLE_INIT
Host Controller Secondary Controller Enable.
0 - DISABLED: Secondary Controller operation is disabled.
1 - ACM_INIT: Enabled, but Host Controller initializes in Active Controller mode.
2 - SCM_RUNNING: Enabled, initializes in Standby Controller mode.
3 - SCM_HOT_JOIN: Enabled, Host Controller conditionally becomes a Hot-Joining Device before operating in Standby Controller mode.

### STBY_CR_CONTROL . RSTACT_DEFBYTE_02
RSTACT Support DefByte 0x02

### STBY_CR_CONTROL . DAA_ENTDAA_ENABLE
Dynamic Address Method Enable.

### STBY_CR_CONTROL . DAA_SETDASA_ENABLE
Dynamic Address Method Enable.

### STBY_CR_CONTROL . DAA_SETAASA_ENABLE
Dynamic Address Method Enable.

### STBY_CR_CONTROL . TARGET_XACT_ENABLE
Target Transaction Interface Servicing Enable.

### STBY_CR_CONTROL . BCAST_CCC_IBI_RING
Ring Bundle IBI Selector for Broadcast CCC Capture.

### STBY_CR_CONTROL . CR_REQUEST_SEND
Send Controller Role Request.

### STBY_CR_CONTROL . HANDOFF_DEEP_SLEEP
Handoff Deep Sleep.

### STBY_CR_CONTROL . PRIME_ACCEPT_GETACCCR
Prime to Accept Controller Role.

### STBY_CR_CONTROL . ACR_FSM_OP_SELECT
Active Controller Select.

### STBY_CR_CONTROL . HANDOFF_DELAY_NACK
Handoff Delay NACK.

### STBY_CR_CONTROL . PENDING_RX_NACK
Pending RX NACK.

## STBY_CR_DEVICE_ADDR
Standby Controller Device Address
- Offset: `0x2e0`
- Reset default: `0x0`
- Reset mask: `0x807f807f`

### Fields

```wavejson
{"reg": [{"name": "STATIC_ADDR", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 8}, {"name": "STATIC_ADDR_VALID", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "DYNAMIC_ADDR", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 8}, {"name": "DYNAMIC_ADDR_VALID", "bits": 1, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description               |
|:------:|:------:|:-------:|:-------------------|:--------------------------|
|   31   |   ro   |   0x0   | DYNAMIC_ADDR_VALID | Dynamic Address is Valid. |
| 30:23  |        |         |                    | Reserved                  |
| 22:16  |   ro   |   0x0   | DYNAMIC_ADDR       | Device Dynamic Address.   |
|   15   |   rw   |   0x0   | STATIC_ADDR_VALID  | Static Address is Valid.  |
|  14:7  |        |         |                    | Reserved                  |
|  6:0   |   rw   |   0x0   | STATIC_ADDR        | Device Static Address.    |

## STBY_CR_CAPABILITIES
Standby Controller Capabilities
- Offset: `0x2e4`
- Reset default: `0xf020`
- Reset mask: `0xf020`

### Fields

```wavejson
{"reg": [{"bits": 5}, {"name": "SIMPLE_CRR_SUPPORT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 6}, {"name": "TARGET_XACT_SUPPORT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DAA_SETAASA_SUPPORT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DAA_SETDASA_SUPPORT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "DAA_ENTDAA_SUPPORT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 16}], "config": {"lanes": 1, "fontsize": 10, "vspace": 210}}
```

|  Bits  |  Type  |  Reset  | Name                | Description                                           |
|:------:|:------:|:-------:|:--------------------|:------------------------------------------------------|
| 31:16  |        |         |                     | Reserved                                              |
|   15   |   ro   |   0x1   | DAA_ENTDAA_SUPPORT  | Dynamic Address Assignment with ENTDAA is supported.  |
|   14   |   ro   |   0x1   | DAA_SETDASA_SUPPORT | Dynamic Address Assignment with SETDASA is supported. |
|   13   |   ro   |   0x1   | DAA_SETAASA_SUPPORT | Dynamic Address Assignment with SETAASA is supported. |
|   12   |   ro   |   0x1   | TARGET_XACT_SUPPORT | I3C Target Transaction Interface is supported.        |
|  11:6  |        |         |                     | Reserved                                              |
|   5    |   ro   |   0x1   | SIMPLE_CRR_SUPPORT  | Simple Controller Role Request is supported.          |
|  4:0   |        |         |                     | Reserved                                              |

## STBY_CR_STATUS
Standby Controller Status
- Offset: `0x2ec`
- Reset default: `0x0`
- Reset mask: `0x1e4`

### Fields

```wavejson
{"reg": [{"bits": 2}, {"name": "AC_CURRENT_OWN", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "SIMPLE_CRR_STATUS", "bits": 3, "attr": ["ro"], "rotate": -90}, {"name": "HJ_REQ_STATUS", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 23}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                            |
|:------:|:------:|:-------:|:------------------|:---------------------------------------|
|  31:9  |        |         |                   | Reserved                               |
|   8    |   ro   |   0x0   | HJ_REQ_STATUS     | Hot-Join Request Status.               |
|  7:5   |   ro   |   0x0   | SIMPLE_CRR_STATUS | Simple Controller Role Request Status. |
|  4:3   |        |         |                   | Reserved                               |
|   2    |   ro   |   0x0   | AC_CURRENT_OWN    | Active Controller.                     |
|  1:0   |        |         |                   | Reserved                               |

## STBY_CR_DEVICE_CHAR
Standby Controller Device Characteristics
- Offset: `0x2f0`
- Reset default: `0x60000000`
- Reset mask: `0xfffffffe`

### Fields

```wavejson
{"reg": [{"bits": 1}, {"name": "PID_HI", "bits": 15, "attr": ["rw"], "rotate": 0}, {"name": "DCR", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "BCR_VAR", "bits": 5, "attr": ["rw"], "rotate": 0}, {"name": "BCR_FIXED", "bits": 3, "attr": ["ro"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 110}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                            |
|:------:|:------:|:-------:|:----------|:---------------------------------------|
| 31:29  |   ro   |   0x3   | BCR_FIXED | Bus Characteristics Register Fixed.    |
| 28:24  |   rw   |   0x0   | BCR_VAR   | Bus Characteristics Register Variable. |
| 23:16  |   rw   |   0x0   | DCR       | Device Characteristics Register.       |
|  15:1  |   rw   |   0x0   | PID_HI    | Device Provisioned ID High.            |

## STBY_CR_DEVICE_PID_LO
Standby Controller PID Low
- Offset: `0x2f4`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "PID_LO", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                |
|:------:|:------:|:-------:|:-------|:---------------------------|
|  31:0  |   rw   |   0x0   | PID_LO | Device Provisioned ID Low. |

## STBY_CR_INTR_STATUS
Standby Controller Interrupt Status
- Offset: `0x2f8`
- Reset default: `0x0`
- Reset mask: `0xf7c0f`

### Fields

```wavejson
{"reg": [{"name": "ACR_HANDOFF_OK_REMAIN_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ACR_HANDOFF_OK_PRIMED_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ACR_HANDOFF_ERR_FAIL_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ACR_HANDOFF_ERR_M3_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 6}, {"name": "CRR_RESPONSE_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "STBY_CR_DYN_ADDR_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "STBY_CR_ACCEPT_NACKED_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "STBY_CR_ACCEPT_OK_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "STBY_CR_ACCEPT_ERR_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 1}, {"name": "STBY_CR_OP_RSTACT_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "CCC_PARAM_MODIFIED_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "CCC_UNHANDLED_NACK_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "CCC_FATAL_RSTDAA_ERR_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 280}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                      |
|:------:|:------:|:-------:|:---------------------------|:-----------------------------------------------------------------|
| 31:20  |        |         |                            | Reserved                                                         |
|   19   |  rw1c  |   0x0   | CCC_FATAL_RSTDAA_ERR_STAT  | CCC Fatal RSTDAA Error Status.                                   |
|   18   |  rw1c  |   0x0   | CCC_UNHANDLED_NACK_STAT    | CCC Unhandled NACK Status.                                       |
|   17   |  rw1c  |   0x0   | CCC_PARAM_MODIFIED_STAT    | CCC Parameter Modified Status.                                   |
|   16   |  rw1c  |   0x0   | STBY_CR_OP_RSTACT_STAT     | Secondary Controller Operation Reset Action.                     |
|   15   |        |         |                            | Reserved                                                         |
|   14   |  rw1c  |   0x0   | STBY_CR_ACCEPT_ERR_STAT    | Secondary Controller Transition Error Status.                    |
|   13   |  rw1c  |   0x0   | STBY_CR_ACCEPT_OK_STAT     | Secondary Controller Transition OK Status.                       |
|   12   |  rw1c  |   0x0   | STBY_CR_ACCEPT_NACKED_STAT | Secondary Controller Transition NACKed.                          |
|   11   |  rw1c  |   0x0   | STBY_CR_DYN_ADDR_STAT      | Secondary Controller Dynamic Address Status.                     |
|   10   |  rw1c  |   0x0   | CRR_RESPONSE_STAT          | Controller Role Request Response Status.                         |
|  9:4   |        |         |                            | Reserved                                                         |
|   3    |  rw1c  |   0x0   | ACR_HANDOFF_ERR_M3_STAT    | Controller Role Handoff Error Type CE3 Recovery.                 |
|   2    |  rw1c  |   0x0   | ACR_HANDOFF_ERR_FAIL_STAT  | Controller Role Handoff Error Due To Failure.                    |
|   1    |  rw1c  |   0x0   | ACR_HANDOFF_OK_PRIMED_STAT | Controller Role Handoff OK and Primed to Accept.                 |
|   0    |  rw1c  |   0x0   | ACR_HANDOFF_OK_REMAIN_STAT | Controller Role Handoff OK and Will Remain Secondary Controller. |

## STBY_CR_INTR_SIGNAL_ENABLE
Standby Controller Interrupt Signal Enable
- Offset: `0x300`
- Reset default: `0xc0000`
- Reset mask: `0xf7c0f`

### Fields

```wavejson
{"reg": [{"name": "ACR_HANDOFF_OK_REMAIN_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ACR_HANDOFF_OK_PRIMED_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ACR_HANDOFF_ERR_FAIL_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ACR_HANDOFF_ERR_M3_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 6}, {"name": "CRR_RESPONSE_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "STBY_CR_DYN_ADDR_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "STBY_CR_ACCEPT_NACKED_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "STBY_CR_ACCEPT_OK_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "STBY_CR_ACCEPT_ERR_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "STBY_CR_OP_RSTACT_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CCC_PARAM_MODIFIED_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CCC_UNHANDLED_NACK_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "CCC_FATAL_RSTDAA_ERR_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 330}}
```

|  Bits  |  Type  |  Reset  | Name                            | Description                                                         |
|:------:|:------:|:-------:|:--------------------------------|:--------------------------------------------------------------------|
| 31:20  |        |         |                                 | Reserved                                                            |
|   19   |   rw   |   0x1   | CCC_FATAL_RSTDAA_ERR_SIGNAL_EN  | CCC Fatal RSTDAA Error Signal Enable.                               |
|   18   |   rw   |   0x1   | CCC_UNHANDLED_NACK_SIGNAL_EN    | CCC Unhandled NACK Signal Enable.                                   |
|   17   |   rw   |   0x0   | CCC_PARAM_MODIFIED_SIGNAL_EN    | CCC Parameter Modified Signal Enable.                               |
|   16   |   rw   |   0x0   | STBY_CR_OP_RSTACT_SIGNAL_EN     | Secondary Controller Operation Reset Action Signal Enable.          |
|   15   |        |         |                                 | Reserved                                                            |
|   14   |   rw   |   0x0   | STBY_CR_ACCEPT_ERR_SIGNAL_EN    | Secondary Controller Transition Error Signal Enable.                |
|   13   |   rw   |   0x0   | STBY_CR_ACCEPT_OK_SIGNAL_EN     | Secondary Controller Transition OK Signal Enable.                   |
|   12   |   rw   |   0x0   | STBY_CR_ACCEPT_NACKED_SIGNAL_EN | Secondary Controller Transition NACKed Signal Enable.               |
|   11   |   rw   |   0x0   | STBY_CR_DYN_ADDR_SIGNAL_EN      | Secondary Controller Dynamic Address Signal Enable.                 |
|   10   |   rw   |   0x0   | CRR_RESPONSE_SIGNAL_EN          | Controller Role Request Response Signal Enable.                     |
|  9:4   |        |         |                                 | Reserved                                                            |
|   3    |   rw   |   0x0   | ACR_HANDOFF_ERR_M3_SIGNAL_EN    | Controller Role Handoff Error Type CE3 Recovery Signal Enable.      |
|   2    |   rw   |   0x0   | ACR_HANDOFF_ERR_FAIL_SIGNAL_EN  | Controller Role Handoff Error Due To Failure Signal Enable.         |
|   1    |   rw   |   0x0   | ACR_HANDOFF_OK_PRIMED_SIGNAL_EN | Controller Role Handoff OK and Primed to Accept Signal Enable.      |
|   0    |   rw   |   0x0   | ACR_HANDOFF_OK_REMAIN_SIGNAL_EN | Controller Role Handoff OK and Will Remain Secondary Signal Enable. |

## STBY_CR_INTR_FORCE
Standby Controller Interrupt Force
- Offset: `0x304`
- Reset default: `0x0`
- Reset mask: `0xf7c00`

### Fields

```wavejson
{"reg": [{"bits": 10}, {"name": "CRR_RESPONSE_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "STBY_CR_DYN_ADDR_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "STBY_CR_ACCEPT_NACKED_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "STBY_CR_ACCEPT_OK_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "STBY_CR_ACCEPT_ERR_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 1}, {"name": "STBY_CR_OP_RSTACT_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "CCC_PARAM_MODIFIED_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "CCC_UNHANDLED_NACK_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "CCC_FATAL_RSTDAA_ERR_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 12}], "config": {"lanes": 1, "fontsize": 10, "vspace": 290}}
```

|  Bits  |  Type  |  Reset  | Name                        | Description                                        |
|:------:|:------:|:-------:|:----------------------------|:---------------------------------------------------|
| 31:20  |        |         |                             | Reserved                                           |
|   19   |   wo   |   0x0   | CCC_FATAL_RSTDAA_ERR_FORCE  | Force CCC Fatal RSTDAA Error.                      |
|   18   |   wo   |   0x0   | CCC_UNHANDLED_NACK_FORCE    | Force CCC Unhandled NACK.                          |
|   17   |   wo   |   0x0   | CCC_PARAM_MODIFIED_FORCE    | Force CCC Parameter Modified.                      |
|   16   |   wo   |   0x0   | STBY_CR_OP_RSTACT_FORCE     | Force Secondary Controller Operation Reset Action. |
|   15   |        |         |                             | Reserved                                           |
|   14   |   wo   |   0x0   | STBY_CR_ACCEPT_ERR_FORCE    | Force Secondary Controller Transition Error.       |
|   13   |   wo   |   0x0   | STBY_CR_ACCEPT_OK_FORCE     | Force Secondary Controller Transition OK.          |
|   12   |   wo   |   0x0   | STBY_CR_ACCEPT_NACKED_FORCE | Force Secondary Controller Transition NACKed.      |
|   11   |   wo   |   0x0   | STBY_CR_DYN_ADDR_FORCE      | Force Secondary Controller Dynamic Address Status. |
|   10   |   wo   |   0x0   | CRR_RESPONSE_FORCE          | Force Controller Role Request Response.            |
|  9:0   |        |         |                             | Reserved                                           |

## STBY_CR_CCC_CONFIG_GETCAPS
Standby Controller CCC Auto-Response Config Get Capabilities
- Offset: `0x308`
- Reset default: `0x0`
- Reset mask: `0xf07`

### Fields

```wavejson
{"reg": [{"name": "F2_CRCAP1_BUS_CONFIG", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 5}, {"name": "F2_CRCAP2_DEV_INTERACT", "bits": 4, "attr": ["rw"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 240}}
```

|  Bits  |  Type  |  Reset  | Name                   | Description                |
|:------:|:------:|:-------:|:-----------------------|:---------------------------|
| 31:12  |        |         |                        | Reserved                   |
|  11:8  |   rw   |   0x0   | F2_CRCAP2_DEV_INTERACT | GETCAPS CCC CRCAPS Byte 2. |
|  7:3   |        |         |                        | Reserved                   |
|  2:0   |   rw   |   0x0   | F2_CRCAP1_BUS_CONFIG   | GETCAPS CCC CRCAPS Byte 1. |

## STBY_CR_CCC_CONFIG_RSTACT_PARAMS
Standby Controller CCC Auto-Response Config Target Reset Action
- Offset: `0x30c`
- Reset default: `0x80000000`
- Reset mask: `0x80ffffff`

### Fields

```wavejson
{"reg": [{"name": "RST_ACTION", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "RESET_TIME_PERIPHERAL", "bits": 8, "attr": ["rw"], "rotate": -90}, {"name": "RESET_TIME_TARGET", "bits": 8, "attr": ["rw"], "rotate": -90}, {"bits": 7}, {"name": "RESET_DYNAMIC_ADDR", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                               |
|:------:|:------:|:-------:|:----------------------|:------------------------------------------|
|   31   |   rw   |   0x1   | RESET_DYNAMIC_ADDR    | Reset Dynamic Address After Target Reset. |
| 30:24  |        |         |                       | Reserved                                  |
| 23:16  |   rw   |   0x0   | RESET_TIME_TARGET     | Time to Reset Target.                     |
|  15:8  |   rw   |   0x0   | RESET_TIME_PERIPHERAL | Time to Reset Peripheral.                 |
|  7:0   |   ro   |   0x0   | RST_ACTION            | Defining Byte of the RSTACT CCC.          |

## TTI_EXTCAP_HEADER
Target Transaction Interface Extended Capability Header
- Offset: `0x310`
- Reset default: `0x59c8`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "CAP_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CAP_LENGTH", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                            |
|:------:|:------:|:-------:|:-----------|:---------------------------------------|
| 31:24  |        |         |            | Reserved                               |
|  23:8  |   ro   |  0x59   | CAP_LENGTH | Capability Structure Length in DWORDs. |
|  7:0   |   ro   |  0xc8   | CAP_ID     | Extended Capability ID                 |

## TARG_INTR_STATUS
Target Interrupt Status.
- Offset: `0x314`
- Reset default: `0x0`
- Reset mask: `0x800f0f7f`

### Fields

```wavejson
{"reg": [{"name": "RX_DESC_READY_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "IBI_STATUS_THLD_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ASYNC_EVT_READY_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "TRANSFER_ABORT_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "TRANSFER_ERR_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "RX_BUFFER_OVF_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "ASYNC_EVT_OVF_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 1}, {"name": "TX0_THLD_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "TX1_THLD_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "TX2_THLD_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "TX3_THLD_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 4}, {"name": "TX0_DESC_READY_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "TX1_DESC_READY_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "TX2_DESC_READY_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "TX3_DESC_READY_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"bits": 11}, {"name": "TE_STAT", "bits": 1, "attr": ["rw1c"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 220}}
```

|  Bits  |  Type  |  Reset  | Name                 | Description                                                                                                                                                              |
|:------:|:------:|:-------:|:---------------------|:-------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|   31   |  rw1c  |   0x0   | TE_STAT              | Target Error Status.                                                                                                                                                     |
| 30:20  |        |         |                      | Reserved                                                                                                                                                                 |
|   19   |  rw1c  |   0x0   | TX3_DESC_READY_STAT  | Target 3 Tx Descriptor Queue Ready Status. Asserted when the Tx Descriptor Queue has at least the requested amount of space, see `TARG_TX_THLD_CTRL.TX_DESC_EMPTY_THLD`. |
|   18   |  rw1c  |   0x0   | TX2_DESC_READY_STAT  | Target 2 Tx Descriptor Queue Ready Status. Asserted when the Tx Descriptor Queue has at least the requested amount of space, see `TARG_TX_THLD_CTRL.TX_DESC_EMPTY_THLD`. |
|   17   |  rw1c  |   0x0   | TX1_DESC_READY_STAT  | Target 1 Tx Descriptor Queue Ready Status. Asserted when the Tx Descriptor Queue has at least the requested amount of space, see `TARG_TX_THLD_CTRL.TX_DESC_EMPTY_THLD`. |
|   16   |  rw1c  |   0x0   | TX0_DESC_READY_STAT  | Target 0 Tx Descriptor Queue Ready Status. Asserted when the Tx Descriptor Queue has at least the requested amount of space, see `TARG_TX_THLD_CTRL.TX_DESC_EMPTY_THLD`. |
| 15:12  |        |         |                      | Reserved                                                                                                                                                                 |
|   11   |  rw1c  |   0x0   | TX3_THLD_STAT        | Target 3 Tx Data Buffer Threshold Status. Asserted when the requested amount of space is available in the Tx Data Buffer, see `TARG_TX_THLD_CTRL.TX_BUF_FREE_THLD`.      |
|   10   |  rw1c  |   0x0   | TX2_THLD_STAT        | Target 2 Tx Data Buffer Threshold Status. Asserted when the requested amount of space is available in the Tx Data Buffer, see `TARG_TX_THLD_CTRL.TX_BUF_FREE_THLD`.      |
|   9    |  rw1c  |   0x0   | TX1_THLD_STAT        | Target 1 Tx Data Buffer Threshold Status. Asserted when the requested amount of space is available in the Tx Data Buffer, see `TARG_TX_THLD_CTRL.TX_BUF_FREE_THLD`.      |
|   8    |  rw1c  |   0x0   | TX0_THLD_STAT        | Target 0 Tx Data Buffer Threshold Status. Asserted when the requested amount of space is available in the Tx Data Buffer, see `TARG_TX_THLD_CTRL.TX_BUF_FREE_THLD`.      |
|   7    |        |         |                      | Reserved                                                                                                                                                                 |
|   6    |  rw1c  |   0x0   | ASYNC_EVT_OVF_STAT   | Asynchronous Event Queue Overflow Status.                                                                                                                                |
|   5    |  rw1c  |   0x0   | RX_BUFFER_OVF_STAT   | Rx Data Buffer Overflow Status.                                                                                                                                          |
|   4    |  rw1c  |   0x0   | TRANSFER_ERR_STAT    | Transfer Error Status.                                                                                                                                                   |
|   3    |  rw1c  |   0x0   | TRANSFER_ABORT_STAT  | Transfer Abort Status.                                                                                                                                                   |
|   2    |  rw1c  |   0x0   | ASYNC_EVT_READY_STAT | Asynchronous Event Queue Ready Status.                                                                                                                                   |
|   1    |  rw1c  |   0x0   | IBI_STATUS_THLD_STAT | IBI Status Threshold Status.                                                                                                                                             |
|   0    |  rw1c  |   0x0   | RX_DESC_READY_STAT   | Rx Descriptor Queue Ready Status.                                                                                                                                        |

## TARG_INTR_STATUS_ENABLE
Target Interrupt Status Enable.
- Offset: `0x318`
- Reset default: `0x0`
- Reset mask: `0x800f0f7f`

### Fields

```wavejson
{"reg": [{"name": "RX_DESC_READY_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "IBI_STATUS_THLD_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ASYNC_EVT_READY_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TRANSFER_ABORT_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TRANSFER_ERR_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RX_BUFFER_OVF_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ASYNC_EVT_OVF_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "TX0_THLD_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX1_THLD_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX2_THLD_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX3_THLD_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 4}, {"name": "TX0_DESC_READY_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX1_DESC_READY_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX2_DESC_READY_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX3_DESC_READY_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 11}, {"name": "TE_STAT_EN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 250}}
```

|  Bits  |  Type  |  Reset  | Name                    | Description                                       |
|:------:|:------:|:-------:|:------------------------|:--------------------------------------------------|
|   31   |   rw   |   0x0   | TE_STAT_EN              | Target Error Status Enable.                       |
| 30:20  |        |         |                         | Reserved                                          |
|   19   |   rw   |   0x0   | TX3_DESC_READY_STAT_EN  | Target 3 Tx Descriptor Queue Ready Status Enable. |
|   18   |   rw   |   0x0   | TX2_DESC_READY_STAT_EN  | Target 2 Tx Descriptor Queue Ready Status Enable. |
|   17   |   rw   |   0x0   | TX1_DESC_READY_STAT_EN  | Target 1 Tx Descriptor Queue Ready Status Enable. |
|   16   |   rw   |   0x0   | TX0_DESC_READY_STAT_EN  | Target 0 Tx Descriptor Queue Ready Status Enable. |
| 15:12  |        |         |                         | Reserved                                          |
|   11   |   rw   |   0x0   | TX3_THLD_STAT_EN        | Target 3 Tx Data Buffer Threshold Status Enable.  |
|   10   |   rw   |   0x0   | TX2_THLD_STAT_EN        | Target 2 Tx Data Buffer Threshold Status Enable.  |
|   9    |   rw   |   0x0   | TX1_THLD_STAT_EN        | Target 1 Tx Data Buffer Threshold Status Enable.  |
|   8    |   rw   |   0x0   | TX0_THLD_STAT_EN        | Target 0 Tx Data Buffer Threshold Status Enable.  |
|   7    |        |         |                         | Reserved                                          |
|   6    |   rw   |   0x0   | ASYNC_EVT_OVF_STAT_EN   | Asynchronous Event Queue Overflow Status Enable.  |
|   5    |   rw   |   0x0   | RX_BUFFER_OVF_STAT_EN   | Rx Data Buffer Overflow Status Enable.            |
|   4    |   rw   |   0x0   | TRANSFER_ERR_STAT_EN    | Transfer Error Status Enable.                     |
|   3    |   rw   |   0x0   | TRANSFER_ABORT_STAT_EN  | Transfer Abort Status Enable.                     |
|   2    |   rw   |   0x0   | ASYNC_EVT_READY_STAT_EN | Asynchronous Event Queue Ready Status Enable.     |
|   1    |   rw   |   0x0   | IBI_STATUS_THLD_STAT_EN | IBI Status Threshold Status Enable.               |
|   0    |   rw   |   0x0   | RX_DESC_READY_STAT_EN   | Rx Descriptor Queue Ready Status Enable.          |

## TARG_INTR_SIGNAL_ENABLE
Target Interrupt Signal Enable.
- Offset: `0x31c`
- Reset default: `0x0`
- Reset mask: `0x800f0f7f`

### Fields

```wavejson
{"reg": [{"name": "RX_DESC_READY_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "IBI_STATUS_THLD_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ASYNC_EVT_READY_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TRANSFER_ABORT_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TRANSFER_ERR_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "RX_BUFFER_OVF_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ASYNC_EVT_OVF_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "TX0_THLD_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX1_THLD_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX2_THLD_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX3_THLD_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 4}, {"name": "TX0_DESC_READY_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX1_DESC_READY_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX2_DESC_READY_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX3_DESC_READY_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 11}, {"name": "TE_SIGNAL_EN", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 270}}
```

|  Bits  |  Type  |  Reset  | Name                      | Description                                       |
|:------:|:------:|:-------:|:--------------------------|:--------------------------------------------------|
|   31   |   rw   |   0x0   | TE_SIGNAL_EN              | Target Error Signal Enable.                       |
| 30:20  |        |         |                           | Reserved                                          |
|   19   |   rw   |   0x0   | TX3_DESC_READY_SIGNAL_EN  | Target 3 Tx Descriptor Queue Ready Signal Enable. |
|   18   |   rw   |   0x0   | TX2_DESC_READY_SIGNAL_EN  | Target 2 Tx Descriptor Queue Ready Signal Enable. |
|   17   |   rw   |   0x0   | TX1_DESC_READY_SIGNAL_EN  | Target 1 Tx Descriptor Queue Ready Signal Enable. |
|   16   |   rw   |   0x0   | TX0_DESC_READY_SIGNAL_EN  | Target 0 Tx Descriptor Queue Ready Signal Enable. |
| 15:12  |        |         |                           | Reserved                                          |
|   11   |   rw   |   0x0   | TX3_THLD_SIGNAL_EN        | Target 3 Tx Data Buffer Threshold Signal Enable.  |
|   10   |   rw   |   0x0   | TX2_THLD_SIGNAL_EN        | Target 2 Tx Data Buffer Threshold Signal Enable.  |
|   9    |   rw   |   0x0   | TX1_THLD_SIGNAL_EN        | Target 1 Tx Data Buffer Threshold Signal Enable.  |
|   8    |   rw   |   0x0   | TX0_THLD_SIGNAL_EN        | Target 0 Tx Data Buffer Threshold Signal Enable.  |
|   7    |        |         |                           | Reserved                                          |
|   6    |   rw   |   0x0   | ASYNC_EVT_OVF_SIGNAL_EN   | Asynchronous Event Queue Overflow Signal Enable.  |
|   5    |   rw   |   0x0   | RX_BUFFER_OVF_SIGNAL_EN   | Rx Data Buffer Overflow Signal Enable.            |
|   4    |   rw   |   0x0   | TRANSFER_ERR_SIGNAL_EN    | Transfer Error Signal Enable.                     |
|   3    |   rw   |   0x0   | TRANSFER_ABORT_SIGNAL_EN  | Transfer Abort Signal Enable.                     |
|   2    |   rw   |   0x0   | ASYNC_EVT_READY_SIGNAL_EN | Asynchronous Event Queue Ready Signal Enable.     |
|   1    |   rw   |   0x0   | IBI_STATUS_THLD_SIGNAL_EN | IBI Status Threshold Signal Enable.               |
|   0    |   rw   |   0x0   | RX_DESC_READY_SIGNAL_EN   | Rx Descriptor Queue Ready Signal Enable.          |

## TARG_INTR_FORCE
Target Interrupt Force.
- Offset: `0x320`
- Reset default: `0x0`
- Reset mask: `0x800f0f7f`

### Fields

```wavejson
{"reg": [{"name": "RX_DESC_READY_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "IBI_THLD_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "ASYNC_EVT_READY_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TRANSFER_ABORT_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TRANSFER_ERR_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "RX_BUFFER_OVF_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "ASYNC_EVT_OVF_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 1}, {"name": "TX0_THLD_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TX1_THLD_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TX2_THLD_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TX3_THLD_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 4}, {"name": "TX0_DESC_READY_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TX1_DESC_READY_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TX2_DESC_READY_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"name": "TX3_DESC_READY_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}, {"bits": 11}, {"name": "TE_FORCE", "bits": 1, "attr": ["wo"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                               |
|:------:|:------:|:-------:|:----------------------|:------------------------------------------|
|   31   |   wo   |   0x0   | TE_FORCE              | Force Target Error.                       |
| 30:20  |        |         |                       | Reserved                                  |
|   19   |   wo   |   0x0   | TX3_DESC_READY_FORCE  | Force Target 3 Tx Descriptor Queue Ready. |
|   18   |   wo   |   0x0   | TX2_DESC_READY_FORCE  | Force Target 2 Tx Descriptor Queue Ready. |
|   17   |   wo   |   0x0   | TX1_DESC_READY_FORCE  | Force Target 1 Tx Descriptor Queue Ready. |
|   16   |   wo   |   0x0   | TX0_DESC_READY_FORCE  | Force Target 0 Tx Descriptor Queue Ready. |
| 15:12  |        |         |                       | Reserved                                  |
|   11   |   wo   |   0x0   | TX3_THLD_FORCE        | Force Target 3 Tx Data Buffer Threshold.  |
|   10   |   wo   |   0x0   | TX2_THLD_FORCE        | Force Target 2 Tx Data Buffer Threshold.  |
|   9    |   wo   |   0x0   | TX1_THLD_FORCE        | Force Target 1 Tx Data Buffer Threshold.  |
|   8    |   wo   |   0x0   | TX0_THLD_FORCE        | Force Target 0 Tx Data Buffer Threshold.  |
|   7    |        |         |                       | Reserved                                  |
|   6    |   wo   |   0x0   | ASYNC_EVT_OVF_FORCE   | Force Asynchronous Event Queue Overflow.  |
|   5    |   wo   |   0x0   | RX_BUFFER_OVF_FORCE   | Force Rx Data Buffer Overflow.            |
|   4    |   wo   |   0x0   | TRANSFER_ERR_FORCE    | Force Transfer Error.                     |
|   3    |   wo   |   0x0   | TRANSFER_ABORT_FORCE  | Force Transfer Abort.                     |
|   2    |   wo   |   0x0   | ASYNC_EVT_READY_FORCE | Force Asynchronous Event Queue Ready.     |
|   1    |   wo   |   0x0   | IBI_THLD_FORCE        | Force IBI Status Threshold.               |
|   0    |   wo   |   0x0   | RX_DESC_READY_FORCE   | Force Rx Descriptor Queue Ready.          |

## TARG_PIO_CONTROL
Target PIO mode Control register.
- Offset: `0x324`
- Reset default: `0x0`
- Reset mask: `0xf0f0003`

### Fields

```wavejson
{"reg": [{"name": "IBI_SUSPENDED", "bits": 1, "attr": ["rw1c"], "rotate": -90}, {"name": "IBI_ABORT", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 14}, {"name": "SUSPENDED", "bits": 4, "attr": ["rw1c"], "rotate": -90}, {"bits": 4}, {"name": "ABORT", "bits": 4, "attr": ["rw"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name                                              |
|:------:|:------:|:-------:|:--------------------------------------------------|
| 31:28  |        |         | Reserved                                          |
| 27:24  |   rw   |   0x0   | [ABORT](#targ_pio_control--abort)                 |
| 23:20  |        |         | Reserved                                          |
| 19:16  |  rw1c  |   0x0   | [SUSPENDED](#targ_pio_control--suspended)         |
|  15:2  |        |         | Reserved                                          |
|   1    |   rw   |   0x0   | [IBI_ABORT](#targ_pio_control--ibi_abort)         |
|   0    |  rw1c  |   0x0   | [IBI_SUSPENDED](#targ_pio_control--ibi_suspended) |

### TARG_PIO_CONTROL . ABORT
Allows software to abort transmission for each Virtual Target in turn.
Writing 1 to the corresponding bit will abort any in-progress transmission from that Virtual Target.
Transmission will enter the Suspended state and will not resume until the Suspended state is cleared.

### TARG_PIO_CONTROL . SUSPENDED
Indicates, for each Virtual Target in turn, whether transmission has been suspended.
If an error occurs during transmission, the corresponding bit will be set automatically by hardware.
Software use of the Abort mechanism described above also causes this bit to become set.
It remains asserted until the software writes a 1 to clear this bit.

### TARG_PIO_CONTROL . IBI_ABORT
Allows software to abort transmission of In-Band Interrupts.
Writing 1 to this bit will abort any in-progress IBI transmission.
IBI transmission will enter the Suspended stateand will not resume until the Suspended state is cleared.

### TARG_PIO_CONTROL . IBI_SUSPENDED
Indicates whether transmission of In-Band Interrupts has been suspended.
If an error occurs during transmission, this bit will be set automatically by hardware.
Software use of the IBI Abort mechanism described above also causes this bit to become set.
It remains asserted until the software writes a 1 to clear this bit.

## TARG_ASYNC_EVT_CONTROL
Target Asynchronous Event Queue Control.
- Offset: `0x328`
- Reset default: `0x0`
- Reset mask: `0x800000ff`

### Fields

```wavejson
{"reg": [{"name": "BCST_CCC", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "DIR_SET_CCC", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "DIR_GET_CCC", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX_NOTIFY", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "IBI_NOTIFY", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "TX_SUSPEND", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "IBI_SUSPEND", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "BUS_EVENTS", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 23}, {"name": "RESET", "bits": 1, "attr": ["rw1c"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 130}}
```

|  Bits  |  Type  |  Reset  | Name        | Description                                          |
|:------:|:------:|:-------:|:------------|:-----------------------------------------------------|
|   31   |  rw1c  |   0x0   | RESET       | Write 1 to reset the Asynchronous Event Queue.       |
|  30:8  |        |         |             | Reserved                                             |
|   7    |   rw   |   0x0   | BUS_EVENTS  | Report I3C Bus Events.                               |
|   6    |   rw   |   0x0   | IBI_SUSPEND | Report Suspension of In-Band Interrupt transmission. |
|   5    |   rw   |   0x0   | TX_SUSPEND  | Report Suspension of Target transmissions.           |
|   4    |   rw   |   0x0   | IBI_NOTIFY  | Notify results of In-Band Interrupt transmissions.   |
|   3    |   rw   |   0x0   | TX_NOTIFY   | Notify results of Target transmissions.              |
|   2    |   rw   |   0x0   | DIR_GET_CCC | Capture `Direct GET` CCC traffic.                    |
|   1    |   rw   |   0x0   | DIR_SET_CCC | Capture `Direct SET` CCC traffic.                    |
|   0    |   rw   |   0x0   | BCST_CCC    | Capture `Broadcast CCC` traffic.                     |

## TARG_ERROR
Target Error counts.
- Offset: `0x32c`
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "TE0", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "TE1", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "TE2", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "TE3", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "TE4", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "TE5", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "TE6", "bits": 4, "attr": ["rw1c"], "rotate": 0}, {"name": "DBR", "bits": 4, "attr": ["rw1c"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                               |
|:------:|:------:|:-------:|:-------|:--------------------------------------------------------------------------|
| 31:28  |  rw1c  |   0x0   | DBR    | Count of Dead Bus Recovery attempts. Write 4'hf to clear the error count. |
| 27:24  |  rw1c  |   0x0   | TE6    | Count of type 6 Target Errors. Write 4'hf to clear the error count.       |
| 23:20  |  rw1c  |   0x0   | TE5    | Count of type 5 Target Errors. Write 4'hf to clear the error count.       |
| 19:16  |  rw1c  |   0x0   | TE4    | Count of type 4 Target Errors. Write 4'hf to clear the error count.       |
| 15:12  |  rw1c  |   0x0   | TE3    | Count of type 3 Target Errors. Write 4'hf to clear the error count.       |
|  11:8  |  rw1c  |   0x0   | TE2    | Count of type 2 Target Errors. Write 4'hf to clear the error count.       |
|  7:4   |  rw1c  |   0x0   | TE1    | Count of type 1 Target Errors. Write 4'hf to clear the error count.       |
|  3:0   |  rw1c  |   0x0   | TE0    | Count of type 0 Target Errors. Write 4'hf to clear the error count.       |

## TARG_QUEUE_THLD_CTRL
Target-side control register for setting queue interrupt thresholds.
- Offset: `0x330`
- Reset default: `0x1000100`
- Reset mask: `0xff00ff00`

### Fields

```wavejson
{"reg": [{"bits": 8}, {"name": "RX_DESC_THLD", "bits": 8, "attr": ["rw"], "rotate": 0}, {"bits": 8}, {"name": "IBI_STATUS_THLD", "bits": 8, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 170}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                                                                                                      |
|:------:|:------:|:-------:|:----------------|:-------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:24  |   rw   |   0x1   | IBI_STATUS_THLD | IBI Status Threshold. Interrupt is issued when the IBI Status Descriptor Queue contains at least N entries. 0: Do not raise any interrupts.      |
| 23:16  |        |         |                 | Reserved                                                                                                                                         |
|  15:8  |   rw   |   0x1   | RX_DESC_THLD    | Rx Descriptor Queue Threshold. Interrupt is issued when the Rx Descriptor Queue contains at least N descriptors. 0: Do not raise any interrupts. |
|  7:0   |        |         |                 | Reserved                                                                                                                                         |

## TARG_QUEUE_STATUS_LEVEL
Target-side queue levels.
- Offset: `0x334`
- Reset default: `0x0`
- Reset mask: `0xfff0fff`

### Fields

```wavejson
{"reg": [{"name": "RX_DESC_LVL", "bits": 12, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "ASYNC_EVT_LVL", "bits": 12, "attr": ["ro"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name          | Description                                                   |
|:------:|:------:|:-------:|:--------------|:--------------------------------------------------------------|
| 31:28  |        |         |               | Reserved                                                      |
| 27:16  |   ro   |   0x0   | ASYNC_EVT_LVL | The number of Asynchronous Event descriptors in the queue.    |
| 15:12  |        |         |               | Reserved                                                      |
|  11:0  |   ro   |   0x0   | RX_DESC_LVL   | The number of descriptors present in the Rx Descriptor queue. |

## TARG_BUF_THLD_CTRL
Target-side control register for setting buffer interrupt thresholds.
- Offset: `0x338`
- Reset default: `0x10000001`
- Reset mask: `0x70000fff`

### Fields

```wavejson
{"reg": [{"name": "RX_SEGMENT_SIZE", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 16}, {"name": "RX_START_THLD", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 1}], "config": {"lanes": 1, "fontsize": 10, "vspace": 150}}
```

|  Bits  |  Type  |  Reset  | Name            | Description                                                                                                                                                                                                                                          |
|:------:|:------:|:-------:|:----------------|:-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
|   31   |        |         |                 | Reserved                                                                                                                                                                                                                                             |
| 30:28  |   rw   |   0x1   | RX_START_THLD   | Receive Start Threshold in DWORDs. Wait until there are at least 2^(N+1) DWORD available before accepting a Private Write transfer. If the Active Controller attempts to perform a write transfer when this condition is not met, it will be NACKed. |
| 27:12  |        |         |                 | Reserved                                                                                                                                                                                                                                             |
|  11:0  |   rw   |   0x1   | RX_SEGMENT_SIZE | Maximum length of received data segment, minus 1. Received data is divided into DWORDs of no more than this length.                                                                                                                                  |

## TARG_BUF_STATUS_LEVEL
Target-side data buffer levels.
- Offset: `0x33c`
- Reset default: `0x0`
- Reset mask: `0xfff0fff`

### Fields

```wavejson
{"reg": [{"name": "RX_BUF_LVL", "bits": 12, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "IBI_FREE_LVL", "bits": 12, "attr": ["ro"], "rotate": 0}, {"bits": 4}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                              |
|:------:|:------:|:-------:|:-------------|:---------------------------------------------------------|
| 31:28  |        |         |              | Reserved                                                 |
| 27:16  |   ro   |    x    | IBI_FREE_LVL | The available space (in DWORDs) in the Target IBI queue. |
| 15:12  |        |         |              | Reserved                                                 |
|  11:0  |   ro   |    x    | RX_BUF_LVL   | The number of DWORDs of data present in the Rx Buffer.   |

## TARG_RW_LEN
Target Read/Write Length.
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| TARG_RW_LEN_0 | 0x340    |
| TARG_RW_LEN_1 | 0x344    |
| TARG_RW_LEN_2 | 0x348    |
| TARG_RW_LEN_3 | 0x34c    |


### Fields

```wavejson
{"reg": [{"name": "MRL", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "MWL", "bits": 16, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                              |
|:------:|:------:|:-------:|:-------|:-----------------------------------------|
| 31:16  |   rw   | 0xffff  | MWL    | Maximum Write transfer Length, in bytes. |
|  15:0  |   rw   | 0xffff  | MRL    | Maximum Read transfer Length, in bytes.  |

## TARG_IBI_LEN
Target IBI payload Length.
- Offset: `0x350`
- Reset default: `0xffffffff`
- Reset mask: `0xffffffff`

### Fields

```wavejson
{"reg": [{"name": "IBI_LEN_0", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "IBI_LEN_1", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "IBI_LEN_2", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "IBI_LEN_3", "bits": 8, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name      | Description                                   |
|:------:|:------:|:-------:|:----------|:----------------------------------------------|
| 31:24  |   rw   |  0xff   | IBI_LEN_3 | Maximum length of IBI data payload, in bytes. |
| 23:16  |   rw   |  0xff   | IBI_LEN_2 | Maximum length of IBI data payload, in bytes. |
|  15:8  |   rw   |  0xff   | IBI_LEN_1 | Maximum length of IBI data payload, in bytes. |
|  7:0   |   rw   |  0xff   | IBI_LEN_0 | Maximum length of IBI data payload, in bytes. |

## TARG_EVENT_ENABLE
Target Event enables.
- Reset default: `0x7`
- Reset mask: `0x7`

### Instances

| Name                | Offset   |
|:--------------------|:---------|
| TARG_EVENT_ENABLE_0 | 0x354    |
| TARG_EVENT_ENABLE_1 | 0x358    |
| TARG_EVENT_ENABLE_2 | 0x35c    |
| TARG_EVENT_ENABLE_3 | 0x360    |


### Fields

```wavejson
{"reg": [{"name": "ENINT", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ENCR", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ENHJ", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 29}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                                                     |
|:------:|:------:|:-------:|:-------|:----------------------------------------------------------------|
|  31:3  |        |         |        | Reserved                                                        |
|   2    |   ro   |   0x1   | ENHJ   | If 1 then Hot-Join requests are enabled for this Target.        |
|   1    |   ro   |   0x1   | ENCR   | If 1 then Controller Role Requests are enabled for this Target. |
|   0    |   ro   |   0x1   | ENINT  | If 1 then In-Band Interrupts are enabled for this Target.       |

## TARG_STATE_DEBUG
Target State Debug
- Offset: `0x364`
- Reset default: `0x3`
- Reset mask: `0xfffff303`

### Fields

```wavejson
{"reg": [{"name": "SCL_LINE_SIGNAL_LEVEL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "SDA_LINE_SIGNAL_LEVEL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 6}, {"name": "BUS_AVAIL", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "BUS_IDLE", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 2}, {"name": "BUS_MODE", "bits": 4, "attr": ["ro"], "rotate": -90}, {"name": "FSM_STATE", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "TRX_STATE", "bits": 8, "attr": ["ro"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 230}}
```

|  Bits  |  Type  |  Reset  | Name                  | Description                                                         |
|:------:|:------:|:-------:|:----------------------|:--------------------------------------------------------------------|
| 31:24  |   ro   |   0x0   | TRX_STATE             | Transceiver state.                                                  |
| 23:16  |   ro   |   0x0   | FSM_STATE             | Core FSM state.                                                     |
| 15:12  |   ro   |   0x0   | BUS_MODE              | Current bus mode.                                                   |
| 11:10  |        |         |                       | Reserved                                                            |
|   9    |   ro   |   0x0   | BUS_IDLE              | Reports whether the Bus Idle condition is met at this instant.      |
|   8    |   ro   |   0x0   | BUS_AVAIL             | Reports whether the Bus Available condition is met at this instant. |
|  7:2   |        |         |                       | Reserved                                                            |
|   1    |   ro   |   0x1   | SDA_LINE_SIGNAL_LEVEL | SDA Line Signal Level.                                              |
|   0    |   ro   |   0x1   | SCL_LINE_SIGNAL_LEVEL | SCL Line Signal Level.                                              |

## TARG_ENABLE
Enable signals for individual virtual targets.
- Offset: `0x368`
- Reset default: `0x0`
- Reset mask: `0xf`

### Fields

```wavejson
{"reg": [{"name": "ENABLE_0", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ENABLE_1", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ENABLE_2", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "ENABLE_3", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 28}], "config": {"lanes": 1, "fontsize": 10, "vspace": 100}}
```

|  Bits  |  Type  |  Reset  | Name     | Description                                                                                                    |
|:------:|:------:|:-------:|:---------|:---------------------------------------------------------------------------------------------------------------|
|  31:4  |        |         |          | Reserved                                                                                                       |
|   3    |   rw   |   0x0   | ENABLE_3 | Enable virtual target. A disabled target will not participate in address assignment or respond to bus traffic. |
|   2    |   rw   |   0x0   | ENABLE_2 | Enable virtual target. A disabled target will not participate in address assignment or respond to bus traffic. |
|   1    |   rw   |   0x0   | ENABLE_1 | Enable virtual target. A disabled target will not participate in address assignment or respond to bus traffic. |
|   0    |   rw   |   0x0   | ENABLE_0 | Enable virtual target. A disabled target will not participate in address assignment or respond to bus traffic. |

## TARG_GROUP
Group addressing configuration.
- Reset default: `0x0`
- Reset mask: `0xf7f`

### Instances

| Name         | Offset   |
|:-------------|:---------|
| TARG_GROUP_0 | 0x36c    |
| TARG_GROUP_1 | 0x370    |
| TARG_GROUP_2 | 0x374    |
| TARG_GROUP_3 | 0x378    |
| TARG_GROUP_4 | 0x37c    |
| TARG_GROUP_5 | 0x380    |
| TARG_GROUP_6 | 0x384    |
| TARG_GROUP_7 | 0x388    |


### Fields

```wavejson
{"reg": [{"name": "GROUP_ADDR", "bits": 7, "attr": ["ro"], "rotate": 0}, {"bits": 1}, {"name": "TARGETS", "bits": 4, "attr": ["ro"], "rotate": -90}, {"bits": 20}], "config": {"lanes": 1, "fontsize": 10, "vspace": 90}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                                                                                                                                         |
|:------:|:------:|:-------:|:-----------|:----------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:12  |        |         |            | Reserved                                                                                                                                            |
|  11:8  |   ro   |   0x0   | TARGETS    | The set of virtual targets subscribed to this group address. If zero, this entry in the list of group addresses is unused.                          |
|   7    |        |         |            | Reserved                                                                                                                                            |
|  6:0   |   ro   |   0x0   | GROUP_ADDR | Group address, iff the entry is used. If zero, and TARGETS is non-zero, all I3C traffic will be captured as if addressed to the selected Target(s). |

## TARG_TX_THLD_CTRL
Target control register for setting Tx thresholds.
- Reset default: `0x10010001`
- Reset mask: `0xf0ff0fff`

### Instances

| Name                | Offset   |
|:--------------------|:---------|
| TARG_TX_THLD_CTRL_0 | 0x38c    |
| TARG_TX_THLD_CTRL_1 | 0x390    |
| TARG_TX_THLD_CTRL_2 | 0x394    |
| TARG_TX_THLD_CTRL_3 | 0x398    |


### Fields

```wavejson
{"reg": [{"name": "TX_BUF_FREE_THLD", "bits": 12, "attr": ["rw"], "rotate": 0}, {"bits": 4}, {"name": "TX_DESC_EMPTY_THLD", "bits": 8, "attr": ["rw"], "rotate": -90}, {"bits": 4}, {"name": "TX_START_THLD", "bits": 4, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description                                                                                                                                                 |
|:------:|:------:|:-------:|:-------------------|:------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:28  |   rw   |   0x1   | TX_START_THLD      | Transmit (Transfer) Start Threshold in DWORDs. Wait until there are at least 2^(N+1) DWORDs of data available before responding to a Read Transfer request. |
| 27:24  |        |         |                    | Reserved                                                                                                                                                    |
| 23:16  |   rw   |   0x1   | TX_DESC_EMPTY_THLD | Tx Descriptor Queue Threshold. Interrupt is issued when the Tx Descriptor Queue contains at least N empty entries. 0: Do not raise an interrupt.            |
| 15:12  |        |         |                    | Reserved                                                                                                                                                    |
|  11:0  |   rw   |   0x1   | TX_BUF_FREE_THLD   | Transmit Buffer Threshold. Interrupt triggers when there are at least N DWORDs of free space in the Tx Data Buffer. 0: Do not raise an interrupt.           |

## TARG_TX_QUEUE_STATUS_LEVEL
Target status register reporting transmit queue levels.
- Reset default: `0x0`
- Reset mask: `0xff0fff`

### Instances

| Name                         | Offset   |
|:-----------------------------|:---------|
| TARG_TX_QUEUE_STATUS_LEVEL_0 | 0x39c    |
| TARG_TX_QUEUE_STATUS_LEVEL_1 | 0x3a0    |
| TARG_TX_QUEUE_STATUS_LEVEL_2 | 0x3a4    |
| TARG_TX_QUEUE_STATUS_LEVEL_3 | 0x3a8    |


### Fields

```wavejson
{"reg": [{"name": "TX_BUF_FREE_LVL", "bits": 12, "attr": ["ro"], "rotate": 0}, {"bits": 4}, {"name": "TX_DESC_FREE_LVL", "bits": 8, "attr": ["ro"], "rotate": -90}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 180}}
```

|  Bits  |  Type  |  Reset  | Name             | Description                                     |
|:------:|:------:|:-------:|:-----------------|:------------------------------------------------|
| 31:24  |        |         |                  | Reserved                                        |
| 23:16  |   ro   |   0x0   | TX_DESC_FREE_LVL | The number of free Tx Descriptor Queue entries. |
| 15:12  |        |         |                  | Reserved                                        |
|  11:0  |   ro   |   0x0   | TX_BUF_FREE_LVL  | The number of free DWORDs in the Tx Buffer.     |

## TARG_ADDR
Target address on the I3C bus.
- Reset default: `0x0`
- Reset mask: `0x807f807f`

### Instances

| Name        | Offset   |
|:------------|:---------|
| TARG_ADDR_0 | 0x3ac    |
| TARG_ADDR_1 | 0x3b0    |
| TARG_ADDR_2 | 0x3b4    |
| TARG_ADDR_3 | 0x3b8    |


### Fields

```wavejson
{"reg": [{"name": "STATIC_ADDR", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 8}, {"name": "STATIC_ADDR_VALID", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "DYNAMIC_ADDR", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 8}, {"name": "DYNAMIC_ADDR_VALID", "bits": 1, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 200}}
```

|  Bits  |  Type  |  Reset  | Name               | Description               |
|:------:|:------:|:-------:|:-------------------|:--------------------------|
|   31   |   rw   |   0x0   | DYNAMIC_ADDR_VALID | Dynamic Address is Valid. |
| 30:23  |        |         |                    | Reserved                  |
| 22:16  |   rw   |   0x0   | DYNAMIC_ADDR       | Device Dynamic Address.   |
|   15   |   rw   |   0x0   | STATIC_ADDR_VALID  | Static Addres is Valid.   |
|  14:7  |        |         |                    | Reserved                  |
|  6:0   |   rw   |   0x0   | STATIC_ADDR        | Device Static Address.    |

## TARG_CHAR
Target Characteristics.
- Reset default: `0x3e000000`
- Reset mask: `0xffffffff`

### Instances

| Name        | Offset   |
|:------------|:---------|
| TARG_CHAR_0 | 0x3bc    |
| TARG_CHAR_1 | 0x3c0    |
| TARG_CHAR_2 | 0x3c4    |
| TARG_CHAR_3 | 0x3c8    |


### Fields

```wavejson
{"reg": [{"name": "PID_HI", "bits": 16, "attr": ["rw"], "rotate": 0}, {"name": "DCR", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "BCR", "bits": 8, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                      |
|:------:|:------:|:-------:|:-------|:---------------------------------|
| 31:24  |   rw   |  0x3e   | BCR    | Bus Characteristics Register.    |
| 23:16  |   rw   |   0x0   | DCR    | Device Characteristics Register. |
|  15:0  |   rw   |   0x0   | PID_HI | High part of Provisioned ID.     |

## TARG_PID_LO
Low part of Target Provisioned ID.
- Reset default: `0x0`
- Reset mask: `0xffffffff`

### Instances

| Name          | Offset   |
|:--------------|:---------|
| TARG_PID_LO_0 | 0x3cc    |
| TARG_PID_LO_1 | 0x3d0    |
| TARG_PID_LO_2 | 0x3d4    |
| TARG_PID_LO_3 | 0x3d8    |


### Fields

```wavejson
{"reg": [{"name": "PID_LO", "bits": 32, "attr": ["rw"], "rotate": 0}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name   | Description                 |
|:------:|:------:|:-------:|:-------|:----------------------------|
|  31:0  |   rw   |   0x0   | PID_LO | Low part of Provisioned ID. |

## TARG_CAPS
Target Capabilities.
- Reset default: `0x0`
- Reset mask: `0x1f37`

### Instances

| Name        | Offset   |
|:------------|:---------|
| TARG_CAPS_0 | 0x3dc    |
| TARG_CAPS_1 | 0x3e0    |
| TARG_CAPS_2 | 0x3e4    |
| TARG_CAPS_3 | 0x3e8    |


### Fields

```wavejson
{"reg": [{"name": "VTCAP1_TYPE", "bits": 3, "attr": ["rw"], "rotate": -90}, {"bits": 1}, {"name": "VTCAP1_SIDE_FX", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VTCAP1_SHARED_DET", "bits": 1, "attr": ["rw"], "rotate": -90}, {"bits": 2}, {"name": "VTCAP2_IRQ", "bits": 2, "attr": ["rw"], "rotate": -90}, {"name": "VTCAP2_ADDR_REMAP", "bits": 1, "attr": ["rw"], "rotate": -90}, {"name": "VTCAP2_BUS_CTX", "bits": 2, "attr": ["rw"], "rotate": -90}, {"bits": 19}], "config": {"lanes": 1, "fontsize": 10, "vspace": 190}}
```

|  Bits  |  Type  |  Reset  | Name              | Description                 |
|:------:|:------:|:-------:|:------------------|:----------------------------|
| 31:13  |        |         |                   | Reserved                    |
| 12:11  |   rw   |   0x0   | VTCAP2_BUS_CTX    | Bus Context and Conditions. |
|   10   |   rw   |   0x0   | VTCAP2_ADDR_REMAP | Address Remapping.          |
|  9:8   |   rw   |   0x0   | VTCAP2_IRQ        | Interrupt Requests.         |
|  7:6   |        |         |                   | Reserved                    |
|   5    |   rw   |   0x0   | VTCAP1_SHARED_DET | Shared Peripheral Detect.   |
|   4    |   rw   |   0x0   | VTCAP1_SIDE_FX    | Side Effects.               |
|   3    |        |         |                   | Reserved                    |
|  2:0   |   rw   |   0x0   | VTCAP1_TYPE       | Virtual Target Type.        |

## TARG_INFO
Target information.
- Reset default: `0x2020`
- Reset mask: `0x383b`

### Instances

| Name        | Offset   |
|:------------|:---------|
| TARG_INFO_0 | 0x3ec    |
| TARG_INFO_1 | 0x3f0    |
| TARG_INFO_2 | 0x3f4    |
| TARG_INFO_3 | 0x3f8    |


### Fields

```wavejson
{"reg": [{"name": "AS", "bits": 2, "attr": ["ro"], "rotate": 0}, {"bits": 1}, {"name": "ENDXFER_WR_NACK", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ENDXFER_WR_EARLY_TERM", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ENDXFER_CRC_EARLY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 5}, {"name": "ENDXFER_CAND_WR_NACK", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ENDXFER_CAND_WR_EARLY_TERM", "bits": 1, "attr": ["ro"], "rotate": -90}, {"name": "ENDXFER_CAND_CRC_EARLY", "bits": 1, "attr": ["ro"], "rotate": -90}, {"bits": 18}], "config": {"lanes": 1, "fontsize": 10, "vspace": 280}}
```

|  Bits  |  Type  |  Reset  | Name                       | Description                                                           |
|:------:|:------:|:-------:|:---------------------------|:----------------------------------------------------------------------|
| 31:14  |        |         |                            | Reserved                                                              |
|   13   |   ro   |   0x1   | ENDXFER_CAND_CRC_EARLY     | Candidate setting for 'CRC Word Indicator.'                           |
|   12   |   ro   |   0x0   | ENDXFER_CAND_WR_EARLY_TERM | Candidate setting for 'Enable WRITE Early Termination Request.'       |
|   11   |   ro   |   0x0   | ENDXFER_CAND_WR_NACK       | Candidate setting for 'Enable ACK/NACK Capability for WRITE Command.' |
|  10:6  |        |         |                            | Reserved                                                              |
|   5    |   ro   |   0x1   | ENDXFER_CRC_EARLY          | CRC Word Indicator.                                                   |
|   4    |   ro   |   0x0   | ENDXFER_WR_EARLY_TERM      | Enable WRITE Early Termination Request.                               |
|   3    |   ro   |   0x0   | ENDXFER_WR_NACK            | Enable ACK/NACK Capability for WRITE Command.                         |
|   2    |        |         |                            | Reserved                                                              |
|  1:0   |   ro   |   0x0   | AS                         | Activity State (ENTASn).                                              |

## TARG_MAX_RDWR
Target Maximum Read/Write Rate and Turnaround.
- Reset default: `0x10000`
- Reset mask: `0xffffff7f`

### Instances

| Name            | Offset   |
|:----------------|:---------|
| TARG_MAX_RDWR_0 | 0x3fc    |
| TARG_MAX_RDWR_1 | 0x400    |
| TARG_MAX_RDWR_2 | 0x404    |
| TARG_MAX_RDWR_3 | 0x408    |


### Fields

```wavejson
{"reg": [{"name": "MAXRD", "bits": 7, "attr": ["rw"], "rotate": 0}, {"bits": 1}, {"name": "MAXWR", "bits": 8, "attr": ["rw"], "rotate": 0}, {"name": "RDTURN_VAL", "bits": 12, "attr": ["rw"], "rotate": 0}, {"name": "RDTURN_SCALE", "bits": 4, "attr": ["rw"], "rotate": -90}], "config": {"lanes": 1, "fontsize": 10, "vspace": 140}}
```

|  Bits  |  Type  |  Reset  | Name         | Description                                                                                                                                                                           |
|:------:|:------:|:-------:|:-------------|:--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| 31:28  |   rw   |   0x0   | RDTURN_SCALE | Maximum Read Turnaround Time Scale. This value scales the Turnaround Time Value, giving the Maximum Read Turnaround Time in microseconds. max time = RDTURN_VAL << (RDTURN_SCALE + 1) |
| 27:16  |   rw   |   0x1   | RDTURN_VAL   | Maximum Read Turnaround Time Value.                                                                                                                                                   |
|  15:8  |   rw   |   0x0   | MAXWR        | Maximum Write Settings.                                                                                                                                                               |
|   7    |        |         |              | Reserved                                                                                                                                                                              |
|  6:0   |   rw   |   0x0   | MAXRD        | Maximum Read Settings                                                                                                                                                                 |

## TTI_PORTS
TTI ports, occupying successive word addresses:

- Rx Descriptor Queue.
- Rx Data Buffer.
- IBI Status Descriptor.
- IBI Data Buffer.
- Asynchronous Event Queue.
- Target 0-3 Tx Descriptor Queue.
- Target 0-3 Tx Data Buffer.

- Word Aligned Offset Range: `0x440`to`0x470`
- Size (words): `13`
- Access: `rw`
- Byte writes are *not* supported.

## TARGEXT_EXTCAP_HEADER
Target Extension Extended Capability Header
- Offset: `0x474`
- Reset default: `0x1c0`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "CAP_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CAP_LENGTH", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                            |
|:------:|:------:|:-------:|:-----------|:---------------------------------------|
| 31:24  |        |         |            | Reserved                               |
|  23:8  |   ro   |   0x1   | CAP_LENGTH | Capability Structure Length in DWORDs. |
|  7:0   |   ro   |  0xc0   | CAP_ID     | Extended Capability ID                 |

## TERM_EXTCAP_HEADER
Terminating Extended Capability Header
- Offset: `0x478`
- Reset default: `0x100`
- Reset mask: `0xffffff`

### Fields

```wavejson
{"reg": [{"name": "CAP_ID", "bits": 8, "attr": ["ro"], "rotate": 0}, {"name": "CAP_LENGTH", "bits": 16, "attr": ["ro"], "rotate": 0}, {"bits": 8}], "config": {"lanes": 1, "fontsize": 10, "vspace": 80}}
```

|  Bits  |  Type  |  Reset  | Name       | Description                            |
|:------:|:------:|:-------:|:-----------|:---------------------------------------|
| 31:24  |        |         |            | Reserved                               |
|  23:8  |   ro   |   0x1   | CAP_LENGTH | Capability Structure Length in DWORDs. |
|  7:0   |   ro   |   0x0   | CAP_ID     | Extended Capability ID                 |

## DAT
Device Address Table.

- Word Aligned Offset Range: `0xa00`to`0xafc`
- Size (words): `64`
- Access: `rw`
- Byte writes are *not* supported.

## DCT
Device Characteristics Table.

- Word Aligned Offset Range: `0xc00`to`0xdfc`
- Size (words): `128`
- Access: `rw`
- Byte writes are *not* supported.

## BUFFER
Software-managed 4KiB message buffer used for transmitting and receiving messages.

This may be used diagnostically when the I3C Controller and/or Target(s) are enabled.
It may be employed as additional system RAM when the I3C block is completely disabled.

- Word Aligned Offset Range: `0x1000`to`0x1ffc`
- Size (words): `1024`
- Access: `rw`
- Byte writes are  supported.


<!-- END CMDGEN -->
