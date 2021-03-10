// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
## PINMUX register template
##
## Parameter (given by Python tool)
##  - n_mio_periph_in:     Number of muxed peripheral inputs
##  - n_mio_periph_out:    Number of muxed peripheral outputs
##  - n_mio_pads:          Number of muxed IO pads
##  - n_dio_periph_in:     Number of dedicated peripheral inputs
##  - n_dio_periph_out:    Number of dedicated peripheral outputs
##  - n_dio_pads:          Number of dedicated IO pads
##  - n_wkup_detect:       Number of wakeup condition detectors
##  - wkup_cnt_width:      Width of wakeup counters
##  - attr_dw:             Width of wakeup counters
{
  name: "PINMUX",
  clock_primary: "clk_i",
  reset_primary: "rst_ni",
  other_clock_list: [
    "clk_aon_i",
  ],
  other_reset_list:
  [
    "rst_aon_ni"
  ],
  bus_interfaces: [
    { protocol: "tlul", direction: "device" }
  ],
  regwidth: "32",

  wakeup_list: [
    { name: "aon_wkup_req",
      desc: "pin wake request"
    },
    { name: "usb_wkup_req",
      desc: "usb wake request"
    },
  ],

  inter_signal_list: [
    // Life cycle inputs
    { struct:  "lc_tx"
      type:    "uni"
      name:    "lc_hw_debug_en"
      act:     "rcv"
      default: "lc_ctrl_pkg::Off"
      package: "lc_ctrl_pkg"
    }
    { struct:  "lc_tx"
      type:    "uni"
      name:    "lc_dft_en"
      act:     "rcv"
      default: "lc_ctrl_pkg::Off"
      package: "lc_ctrl_pkg"
    }
    // JTAG TAPs
    { struct:  "jtag"
      type:    "req_rsp"
      name:    "lc_jtag"
      act:     "req"
      package: "jtag_pkg"
    }
    { struct:  "jtag"
      type:    "req_rsp"
      name:    "rv_jtag"
      act:     "req"
      package: "jtag_pkg"
    }
    { struct:  "jtag"
      type:    "req_rsp"
      name:    "dft_jtag"
      act:     "req"
      package: "jtag_pkg"
    }
    // Testmode signals to AST
    { struct:  "dft_strap_test_req",
      type:    "uni",
      name:    "dft_strap_test",
      act:     "req",
      package: "pinmux_pkg",
      default: "'0"
    }
    // Define pwr mgr <-> pinmux signals
    { struct:  "logic",
      type:    "uni",
      name:    "sleep_en",
      act:     "rcv",
      package: "",
      default: "1'b0"
    },
    { struct:  "logic",
      type:    "uni",
      name:    "strap_en",
      act:     "rcv",
      package: "",
      default: "1'b0"
    },
    { struct:  "logic",
      type:    "uni",
      name:    "aon_wkup_req",
      act:     "req",
      package: "",
      default: "1'b0"
    },
    { struct:  "logic",
      type:    "uni",
      name:    "usb_wkup_req",
      act:     "req",
      package: "",
      default: "1'b0"
    },
    { name:    "usb_out_of_rst",
      type:    "uni",
      act:     "rcv",
      package: "",
      struct:  "logic",
      width:   "1"
    },
    { name:    "usb_aon_wake_en",
      type:    "uni",
      act:     "rcv",
      package: "",
      struct:  "logic",
      width:   "1"
    },
    { name:    "usb_aon_wake_ack",
      type:    "uni",
      act:     "rcv",
      package: "",
      struct:  "logic",
      width:   "1"
    },
    { name:    "usb_suspend",
      type:    "uni",
      act:     "rcv",
      package: "",
      struct:  "logic",
      width:   "1"
    },
    { name:    "usb_state_debug",
      type:    "uni",
      act:     "req",
      package: "usbdev_pkg",
      struct:  "awk_state",
    },
  ]

  param_list: [
    { name: "AttrDw",
      desc: "Pad attribute data width",
      type: "int",
      default: "${attr_dw}",
      local: "true"
    },
    { name: "NMioPeriphIn",
      desc: "Number of muxed peripheral inputs",
      type: "int",
      default: "${n_mio_periph_in}",
      local: "true"
    },
    { name: "NMioPeriphOut",
      desc: "Number of muxed peripheral outputs",
      type: "int",
      default: "${n_mio_periph_out}",
      local: "true"
    },
    { name: "NMioPads",
      desc: "Number of muxed IO pads",
      type: "int",
      default: "${n_mio_pads}",
      local: "true"
    },
    { name: "NDioPads",
      desc: "Number of dedicated IO pads",
      type: "int",
      default: "${n_dio_pads}",
      local: "true"
    },
    { name: "NWkupDetect",
      desc: "Number of wakeup detectors",
      type: "int",
      default: "${n_wkup_detect}",
      local: "true"
    },
    { name: "WkupCntWidth",
      desc: "Number of wakeup counter bits",
      type: "int",
      default: "${wkup_cnt_width}",
      local: "true"
    },
    { name: "NUsbDevPads",
      desc: "Number of usbdev pins",
      type: "int",
      default: "${n_usb_pins}",
      local: "true"
    },
    { name: "NDioPadUsbDevStart",
      desc: "Start position for usbdev pins",
      type: "int",
      default: "${usb_start_pos}",
      local: "true"
    },
    { name: "UsbDpSel",
      desc: "index of usbdev_dp",
      type: "int",
      default: "${usb_dp_sel}",
      local: "true"
    },
    { name: "UsbDnSel",
      desc: "index of usbdev_dn",
      type: "int",
      default: "${usb_dn_sel}",
      local: "true"
    },
    { name: "UsbDpPullUpSel",
      desc: "index of usbdev_dp_pullup",
      type: "int",
      default: "${usb_dp_pull_sel}",
      local: "true"
    },
    { name: "UsbDnPullUpSel",
      desc: "index of usbdev_dn_pullup",
      type: "int",
      default: "${usb_dn_pull_sel}",
      local: "true"
    },
    // Since the target-specific top-levels often have slightly
    // different debug signal positions, we need a way to pass
    // this info from the target specific top-level into the pinmux
    // logic. The parameter struct below serves this purpose.
   { name: "TargetCfg",
      desc:    "Target specific pinmux configuration.",
      type:    "pinmux_pkg::target_cfg_t",
      default: "pinmux_pkg::DefaultTargetCfg",
      local:   "false",
      expose:  "true"
    },
  ],
  registers: [
//////////////////////////
// MIO Inputs           //
//////////////////////////
    { multireg: { name:     "MIO_PERIPH_INSEL_REGWEN",
                  desc:     "Register write enable for MIO peripheral input selects.",
                  count:    "NMioPeriphIn",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "none",
                  cname:    "MIO_PERIPH_INSEL",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Register write enable bit.
                              If this is cleared to 0, the corresponding MIO_PERIPH_INSEL
                              is not writable anymore.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:         "MIO_PERIPH_INSEL",
                  desc:         "For each peripheral input, this selects the muxable pad input.",
                  count:        "NMioPeriphIn",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "MIO_PERIPH_INSEL_REGWEN",
                  regwen_multi: "true",
                  cname:        "IN",
                  fields: [
                    { bits: "${(n_mio_pads+1).bit_length()-1}:0",
                      name: "IN",
                      desc: '''
                      0: tie constantly to zero, 1: tie constantly to 1,
                      >=2: MIO pads (i.e., add 2 to the native MIO pad index).
                      '''
                      resval: 0,
                    }
                  ]
                }
    },

//////////////////////////
// MIO Outputs          //
//////////////////////////
    { multireg: { name:     "MIO_OUTSEL_REGWEN",
                  desc:     "Register write enable for MIO output selects.",
                  count:    "NMioPads",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "none",
                  cname:    "MIO_OUTSEL",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Register write enable bit.
                              If this is cleared to 0, the corresponding MIO_OUTSEL
                              is not writable anymore.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:         "MIO_OUTSEL",
                  desc:         "For each muxable pad, this selects the peripheral output.",
                  count:        "NMioPads",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "MIO_OUTSEL_REGWEN",
                  regwen_multi: "true",
                  cname:        "OUT",
                  fields: [
                    { bits: "${(n_mio_periph_out+2).bit_length()-1}:0",
                      name: "OUT",
                      desc: '''
                      0: tie constantly to zero, 1: tie constantly to 1, 2: high-Z,
                      >=3: peripheral outputs (i.e., add 3 to the native peripheral pad index).
                      '''
                      resval: 2,
                    }
                  ]
                  // Random writes to this field may result in pad drive conflicts,
                  // which in turn leads to propagating Xes and assertion failures.
                  tags: ["excl:CsrNonInitTests:CsrExclWrite"]
                }
    },

//////////////////////////
// MIO PAD attributes   //
//////////////////////////
    { multireg: { name:     "MIO_PAD_ATTR_REGWEN",
                  desc:     "Register write enable for MIO PAD attributes.",
                  count:    "NMioPads",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "none",
                  cname:    "MIO_PAD",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Register write enable bit.
                              If this is cleared to 0, the corresponding !!MIO_PAD_ATTR
                              is not writable anymore.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:     "MIO_PAD_ATTR",
                  desc:     '''
                            Muxed pad attributes.
                            This register has WARL behavior since not each pad type may support
                            all attributes.
                            ''',
                  count:        "NMioPads",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hrw",
                  hwext:        "true",
                  hwqe:         "true",
                  regwen:       "MIO_PAD_ATTR_REGWEN",
                  regwen_multi: "true",
                  cname:        "MIO_PAD",
                  fields: [
                    { bits: "9:0",
                      name: "ATTR",
                      desc: '''Bit   0: input/output inversion,
                               Bit   1: Virtual open drain enable.
                               Bit   2: Pull enable.
                               Bit   3: Pull select (0: pull down, 1: pull up).
                               Bit   4: Keeper enable.
                               Bit   5: Schmitt trigger enable.
                               Bit   6: Slew rate (0: slow, 1: fast).
                               Bit 7/8: Drive strength (00: weakest, 11: strongest).
                               Bit   9: Reserved.
                      '''
                      resval: 0
                    }
                  ],
                  // these CSRs have WARL behavior and may not
                  // read back the same value that was written to them.
                  // further, they have hardware side effects since they drive the
                  // pad attributes, and hence no random data should be written to them.
                  tags: ["excl:CsrAllTests:CsrExclWrite"]
                }
    },

//////////////////////////
// DIO PAD attributes   //
//////////////////////////
    { multireg: { name:     "DIO_PAD_ATTR_REGWEN",
                  desc:     "Register write enable for DIO PAD attributes.",
                  count:    "NDioPads",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "none",
                  cname:    "DIO_PAD",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Register write enable bit.
                              If this is cleared to 0, the corresponding !!DIO_PAD_ATTR
                              is not writable anymore.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:     "DIO_PAD_ATTR",
                  desc:     '''
                            Dedicated pad attributes.
                            This register has WARL behavior since not each pad type may support
                            all attributes.
                            ''',
                  count:        "NDioPads",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hrw",
                  hwext:        "true",
                  hwqe:         "true",
                  regwen:       "DIO_PAD_ATTR_REGWEN",
                  regwen_multi: "true",
                  cname:        "DIO_PAD",
                  fields: [
                    { bits: "9:0",
                      name: "ATTR",
                      desc: '''Bit   0: input/output inversion,
                               Bit   1: Virtual open drain enable.
                               Bit   2: Pull enable.
                               Bit   3: Pull select (0: pull down, 1: pull up).
                               Bit   4: Keeper enable.
                               Bit   5: Schmitt trigger enable.
                               Bit   6: Slew rate (0: slow, 1: fast).
                               Bit 7/8: Drive strength (00: weakest, 11: strongest).
                               Bit   9: Reserved.
                      '''
                      resval: 0
                    }
                  ],
                  // these CSRs have WARL behavior and may not
                  // read back the same value that was written to them.
                  // further, they have hardware side effects since they drive the
                  // pad attributes, and hence no random data should be written to them.
                  tags: ["excl:CsrAllTests:CsrExclWrite"]
                }
    },

//////////////////////////
// MIO PAD sleep mode   //
//////////////////////////
    { multireg: { name:     "MIO_PAD_SLEEP_STATUS",
                  desc:     "Register indicating whether the corresponding pad is in sleep mode.",
                  count:    "NMioPads",
                  swaccess: "rw0c",
                  hwaccess: "hrw",
                  cname:    "MIO_PAD",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              This register is set to 1 if the deep sleep mode of the corresponding
                              pad has been enabled (!!MIO_PAD_SLEEP_EN) upon deep sleep entry.
                              The sleep mode of the corresponding pad will remain active until SW
                              clears this bit.
                              ''',
                      resval: "0",
                    }
                  ]
                }
    },
    { multireg: { name:     "MIO_PAD_SLEEP_REGWEN",
                  desc:     "Register write enable for MIO sleep value configuration.",
                  count:    "NMioPads",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "none",
                  cname:    "MIO_PAD",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Register write enable bit.
                              If this is cleared to 0, the corresponding !!MIO_OUT_SLEEP_MODE
                              is not writable anymore.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:         "MIO_PAD_SLEEP_EN",
                  desc:         '''Enables the sleep mode of the corresponding muxed pad.
                                '''
                  count:        "NMioPads",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "MIO_PAD_SLEEP_REGWEN",
                  regwen_multi: "true",
                  cname:        "OUT",
                  fields: [
                    { bits: "0",
                      name: "EN",
                      resval: 0,
                      desc: '''
                            Deep sleep mode enable.
                            If this bit is set to 1 the corresponding pad will enable the sleep behavior
                            specified in !!MIO_PAD_SLEEP_MODE upon deep sleep entry, and the corresponding bit
                            in !!MIO_PAD_SLEEP_STATUS will be set to 1.
                            The pad remains in deep sleep mode until the corresponding bit in
                            !!MIO_PAD_SLEEP_STATUS is cleared by SW.
                            Note that if an always on peripheral is connected to a specific MIO pad,
                            the corresponding !!MIO_PAD_SLEEP_EN bit should be set to 0.
                            '''
                    }
                  ]
                }
    },
    { multireg: { name:         "MIO_PAD_SLEEP_MODE",
                  desc:         '''Defines sleep behavior of the corresponding muxed pad.
                                '''
                  count:        "NMioPads",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "MIO_PAD_SLEEP_REGWEN",
                  regwen_multi: "true",
                  cname:        "OUT",
                  fields: [
                    { bits:  "1:0",
                      name:  "OUT",
                      resval: 2,
                      desc:  "Value to drive in deep sleep."
                      enum: [
                        { value: "0",
                          name: "Tie-Low",
                          desc: "The pad is driven actively to zero in deep sleep mode."
                        },
                        { value: "1",
                          name: "Tie-High",
                          desc: "The pad is driven actively to one in deep sleep mode."
                        },
                        { value: "2",
                          name: "High-Z",
                          desc: '''
                                The pad is left undriven in deep sleep mode. Note that the actual
                                driving behavior during deep sleep will then depend on the pull-up/-down
                                configuration of in !!MIO_PAD_ATTR.
                                '''
                        },
                        { value: "3",
                          name: "Keep",
                          desc: "Keep last driven value (including high-Z)."
                        },
                      ]
                    }
                  ]
                }
    },
//////////////////////////
// DIO PAD sleep mode   //
//////////////////////////
    { multireg: { name:     "DIO_PAD_SLEEP_STATUS",
                  desc:     "Register indicating whether the corresponding pad is in sleep mode.",
                  count:    "NDioPads",
                  swaccess: "rw0c",
                  hwaccess: "hrw",
                  cname:    "DIO_PAD",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              This register is set to 1 if the deep sleep mode of the corresponding
                              pad has been enabled (!!DIO_PAD_SLEEP_MODE) upon deep sleep entry.
                              The sleep mode of the corresponding pad will remain active until SW
                              clears this bit.
                              ''',
                      resval: "0",
                    }
                  ]
                }
    },
    { multireg: { name:     "DIO_PAD_SLEEP_REGWEN",
                  desc:     "Register write enable for DIO sleep value configuration.",
                  count:    "NDioPads",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "none",
                  cname:    "DIO_PAD",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Register write enable bit.
                              If this is cleared to 0, the corresponding !!DIO_PAD_SLEEP_MODE
                              is not writable anymore.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:         "DIO_PAD_SLEEP_EN",
                  desc:         '''Enables the sleep mode of the corresponding dedicated pad.
                                '''
                  count:        "NDioPads",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "DIO_PAD_SLEEP_REGWEN",
                  regwen_multi: "true",
                  cname:        "OUT",
                  fields: [
                    { bits: "0",
                      name: "EN",
                      resval: 0,
                      desc: '''
                            Deep sleep mode enable.
                            If this bit is set to 1 the corresponding pad will enable the sleep behavior
                            specified in !!DIO_PAD_SLEEP_MODE upon deep sleep entry, and the corresponding bit
                            in !!DIO_PAD_SLEEP_STATUS will be set to 1.
                            The pad remains in deep sleep mode until the corresponding bit in
                            !!DIO_PAD_SLEEP_STATUS is cleared by SW.
                            Note that if an always on peripheral is connected to a specific DIO pad,
                            the corresponding !!DIO_PAD_SLEEP_EN bit should be set to 0.
                            '''
                    }
                  ]
                }
    },
    { multireg: { name:         "DIO_PAD_SLEEP_MODE",
                  desc:         '''Defines sleep behavior of the corresponding dedicated pad.
                                '''
                  count:        "NDioPads",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "DIO_PAD_SLEEP_REGWEN",
                  regwen_multi: "true",
                  cname:        "OUT",
                  fields: [
                    { bits:  "1:0",
                      name:  "OUT",
                      resval: 2,
                      desc:  "Value to drive in deep sleep."
                      enum: [
                        { value: "0",
                          name: "Tie-Low",
                          desc: "The pad is driven actively to zero in deep sleep mode."
                        },
                        { value: "1",
                          name: "Tie-High",
                          desc: "The pad is driven actively to one in deep sleep mode."
                        },
                        { value: "2",
                          name: "High-Z",
                          desc: '''
                                The pad is left undriven in deep sleep mode. Note that the actual
                                driving behavior during deep sleep will then depend on the pull-up/-down
                                configuration of in !!DIO_PAD_ATTR.
                                '''
                        },
                        { value: "3",
                          name: "Keep",
                          desc: "Keep last driven value (including high-Z)."
                        },
                      ]
                    }
                  ]
                }
    },
////////////////////////
// Wakeup detectors   //
////////////////////////
    { multireg: { name:     "WKUP_DETECTOR_REGWEN",
                  desc:     "Register write enable for wakeup detectors.",
                  count:    "NWkupDetect",
                  compact:  "false",
                  swaccess: "rw0c",
                  hwaccess: "none",
                  cname:    "WKUP_DETECTOR",
                  fields: [
                    { bits:   "0",
                      name:   "EN",
                      desc:   '''
                              Register write enable bit.
                              If this is cleared to 0, the corresponding WKUP_DETECTOR
                              configuration is not writable anymore.
                              ''',
                      resval: "1",
                    }
                  ]
                }
    },
    { multireg: { name:         "WKUP_DETECTOR_EN",
                  desc:         "Enables for the wakeup detectors."
                  count:        "NWkupDetect",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "WKUP_DETECTOR_REGWEN",
                  regwen_multi: "true",
                  cname:        "DETECTOR",
                  fields: [
                    { bits: "0:0",
                      name: "EN",
                      resval: 0,
                      desc: '''
                      Setting this bit activates the corresponding wakeup detector.
                      The behavior is as specified in !!WKUP_DETECTOR,
                      !!WKUP_DETECTOR_CNT_TH and !!WKUP_DETECTOR_PADSEL.
                      '''
                    }
                  ]
                }

    },
    { multireg: { name:         "WKUP_DETECTOR",
                  desc:         "Configuration of wakeup condition detectors."
                  count:        "NWkupDetect",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "WKUP_DETECTOR_REGWEN",
                  regwen_multi: "true",
                  cname:        "DETECTOR",
                  fields: [
                    { bits: "2:0",
                      name: "MODE",
                      resval: 0,
                      desc: "Wakeup detection mode."
                      enum: [
                        { value: "0",
                          name: "Posedge",
                          desc: "Trigger a wakeup request when observing a positive edge."
                        },
                        { value: "1",
                          name: "Negedge",
                          desc: "Trigger a wakeup request when observing a negative edge."
                        },
                        { value: "2",
                          name: "Edge",
                          desc: "Trigger a wakeup request when observing an edge in any direction."
                        },
                        { value: "3",
                          name: "TimedHigh",
                          desc: '''
                            Trigger a wakeup request when pin is driven HIGH for a certain amount
                            of always-on clock cycles as configured in !!WKUP_DETECTOR_CNT_TH.
                            '''
                        },
                        { value: "4",
                          name: "TimedLow",
                          desc: '''
                            Trigger a wakeup request when pin is driven LOW for a certain amount
                            of always-on clock cycles as configured in !!WKUP_DETECTOR_CNT_TH.
                            '''
                        },

                      ]
                    }
                    { bits: "3",
                      name: "FILTER",
                      resval: 0,
                      desc: '''0: signal filter disabled, 1: signal filter enabled. the signal must
                        be stable for 4 always-on clock cycles before the value is being forwarded.
                        can be used for debouncing.
                        '''
                    }
                    { bits: "4",
                      name: "MIODIO",
                      resval: 0,
                      desc: '''0: select index !!WKUP_DETECTOR_PADSEL from MIO pads,
                        1: select index !!WKUP_DETECTOR_PADSEL from DIO pads.
                        '''
                    }
                  ]
                }

    },
    { multireg: { name:         "WKUP_DETECTOR_CNT_TH",
                  desc:         "Counter thresholds for wakeup condition detectors."
                  count:        "NWkupDetect",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "WKUP_DETECTOR_REGWEN",
                  regwen_multi: "true",
                  cname:        "DETECTOR",
                  fields: [
                    { bits: "WkupCntWidth-1:0",
                      name: "TH",
                      resval: 0,
                      desc: '''Counter threshold for TimedLow and TimedHigh wakeup detector modes (see !!WKUP_DETECTOR).
                      The threshold is in terms of always-on clock cycles.
                      '''
                    }
                  ]
                }

    },
    { multireg: { name:         "WKUP_DETECTOR_PADSEL",
                  desc:         "Pad selects for pad wakeup condition detectors."
                  count:        "NWkupDetect",
                  compact:      "false",
                  swaccess:     "rw",
                  hwaccess:     "hro",
                  regwen:       "WKUP_DETECTOR_REGWEN",
                  regwen_multi: "true",
                  cname:        "DETECTOR",
                  fields: [
                    { bits: "${max(2 + n_mio_pads-1, n_dio_periph_in-1).bit_length()-1}:0",
                      name: "SEL",
                      resval: 0,
                      desc: '''Selects a specific MIO or DIO pad (depending on !!WKUP_DETECTOR configuration).
                      In case of MIO, the pad select index is the same as used for !!PERIPH_INSEL, meaning that index
                      0 and 1 just select constant 0, and the MIO pads live at indices >= 2. In case of DIO pads,
                      the pad select index corresponds 1:1 to the DIO pad to be selected.
                      '''
                    }
                  ]
                }

    },
    { multireg: { name:     "WKUP_CAUSE",
                  desc:     "Cause registers for wakeup detectors."
                  count:    "NWkupDetect",
                  swaccess: "rw0c",
                  hwaccess: "hrw",
                  hwext:    "true",
                  hwqe:     "true",
                  cname:    "DETECTOR",
                  fields: [
                    { bits: "0",
                      name: "CAUSE",
                      resval: 0,
                      desc: '''Set to 1 if the corresponding detector has detected a wakeup pattern. Write 0 to clear.
                      '''
                    }
                  ]
                  // these CSRs live in the slow AON clock domain and
                  // clearing them will be very slow and the changes
                  // are not immediately visible.
                  tags: ["excl:CsrAllTests:CsrExclWriteCheck"]
                }

    },
  ],
}
