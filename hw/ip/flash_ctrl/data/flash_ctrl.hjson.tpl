// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
  page_width = (cfg.pages_per_bank-1).bit_length()
  bank_width = (cfg.banks-1).bit_length()
  total_pages = cfg.banks * cfg.pages_per_bank
  page_idx_width = (total_pages-1).bit_length()
  page_num_width = total_pages.bit_length()
  bytes_per_page = cfg.words_per_page * cfg.word_bytes
  total_byte_width = int(total_pages*bytes_per_page-1).bit_length()
  info_type_width = (cfg.info_types-1).bit_length()
  max_fifo_depth = 16
  max_fifo_width = max_fifo_depth.bit_length()
%>

{
  name:               "flash_ctrl",
  human_name:         "Flash Controller",
  one_line_desc:      "Interfaces and manages integrated non-volatile flash memory; supports scrambling, integrity, and secure wipe",
  one_paragraph_desc: '''
  Flash Controller interfaces the integrated, non-volatile flash memory with software and other hardware components in the system, such as Life Cycle Controller, Key Manager, and OTP Controller.
  It consists of the open source flash controller that interfaces with a third party flash module.
  The protocol controller handles read, program, and erase requests, as well as life cycle RMA entry.
  It supports differentiation between informational and data flash partitions, flash memory protection at page boundaries, and the handling of key manager secrets inaccessible to software.
  The actual physical controller is highly parameterized (number of banks, number of pages for each bank, number of words and word size for each page, and number of read buffers) and supports XEX scrambling configurable by software, as well as two types of ECC support configurable on a page boundary.
  '''
  // Unique comportable IP identifier defined under KNOWN_CIP_IDS in the regtool.
  cip_id:             "8",
  design_spec:        "../doc",
  dv_doc:             "../doc/dv"
  hw_checklist:       "../doc/checklist",
  sw_checklist:       "/sw/device/lib/dif/dif_flash_ctrl",
  revisions: [
      {
          version:            "0.1.0",
          life_stage:         "L1",
          design_stage:       "D1",
          verification_stage: "V1",
          commit_id:          "7049fd0d5d48e20772f8ebf32b240faa0dad5528",
      },
      {
          version:            "1.0.0",
          life_stage:         "L1",
          design_stage:       "D2S",
          verification_stage: "V2S",
          dif_stage:          "S2",
      },
  ]
  clocking: [
    {clock: "clk_i", reset: "rst_ni", primary: true},
    {clock: "clk_otp_i", reset: "rst_otp_ni"}
  ]
  bus_interfaces: [
    { protocol: "tlul", direction: "device", name: "core" }
    { protocol: "tlul", direction: "device", name: "prim" , hier_path: "u_eflash.u_flash.gen_generic.u_impl_generic.u_reg_top"}
    { protocol: "tlul", direction: "device", name: "mem" }
  ],
  available_input_list: [
    { name: "tck", desc: "jtag clock" },
    { name: "tms", desc: "jtag tms" },
    { name: "tdi", desc: "jtag input" },
  ],
  available_output_list: [
    { name: "tdo", desc: "jtag output" },
  ],
  interrupt_list: [
    { name: "prog_empty", desc: "Program FIFO empty" },
    { name: "prog_lvl",   desc: "Program FIFO drained to level" },
    { name: "rd_full",    desc: "Read FIFO full" },
    { name: "rd_lvl",     desc: "Read FIFO filled to level" },
    { name: "op_done",    desc: "Operation complete" },
    { name: "corr_err",   desc: "Correctable error encountered"},
  ],

  alert_list: [
    { name: "recov_err",
      desc: "flash recoverable errors",
    },
    { name: "fatal_std_err",
      desc: "flash standard fatal errors"
    },
    { name: "fatal_err",
      desc: "flash fatal errors"
    },
    { name: "fatal_prim_flash_alert",
      desc: "Fatal alert triggered inside the flash primitive, including fatal TL-UL bus integrity faults of the test interface."
    },
    { name: "recov_prim_flash_alert",
      desc: "Recoverable alert triggered inside the flash primitive."
    }
  ],

  // Define flash_ctrl <-> flash_phy struct package
  inter_signal_list: [
    { struct: "flash_otp_key",
      type: "req_rsp",
      name: "otp",
      act:  "req",
      package: "otp_ctrl_pkg"
    },

    { struct: "lc_tx",
      package: "lc_ctrl_pkg",
      type: "uni"
      act: "rcv"
      name: "lc_nvm_debug_en"
    },

    { struct: "mubi4"
      package: "prim_mubi_pkg"
      type: "uni"
      act: "rcv"
      name: "flash_bist_enable"
    },

    { struct: "logic"
      package: ""
      type: "uni"
      act: "rcv"
      name: "flash_power_down_h"
    },
    { struct: "logic"
      package: ""
      type: "uni"
      act: "rcv"
      name: "flash_power_ready_h"
    },
    { struct: "",
      package: "",
      width: "2",
      type: "io"
      act: "none"
      name: "flash_test_mode_a"
    },
    { struct: "",
      package: "",
      type: "io"
      act: "none"
      name: "flash_test_voltage_h"
    },

    { struct:  "lc_tx"
      type:    "uni"
      name:    "lc_creator_seed_sw_rw_en"
      act:     "rcv"
      package: "lc_ctrl_pkg"
    },

    { struct:  "lc_tx"
      type:    "uni"
      name:    "lc_owner_seed_sw_rw_en"
      act:     "rcv"
      package: "lc_ctrl_pkg"
    },

    { struct:  "lc_tx"
      type:    "uni"
      name:    "lc_iso_part_sw_rd_en"
      act:     "rcv"
      package: "lc_ctrl_pkg"
    },

    { struct:  "lc_tx"
      type:    "uni"
      name:    "lc_iso_part_sw_wr_en"
      act:     "rcv"
      package: "lc_ctrl_pkg"
    },

    { struct:  "lc_tx"
      type:    "uni"
      name:    "lc_seed_hw_rd_en"
      act:     "rcv"
      package: "lc_ctrl_pkg"
    },

    { struct:  "lc_tx"
      type:    "uni"
      name:    "lc_escalate_en"
      act:     "rcv"
      package: "lc_ctrl_pkg"
    },

    { struct:  "lc_tx"
      type:    "uni"
      name:    "rma_req"
      act:     "rcv"
      package: "lc_ctrl_pkg"
    },

    { struct:  "lc_tx"
      type:    "uni"
      name:    "rma_ack"
      act:     "req"
      package: "lc_ctrl_pkg"
    },

    { struct:  "lc_flash_rma_seed"
      type:    "uni"
      name:    "rma_seed"
      act:     "rcv"
      package: "lc_ctrl_pkg"
    },

    { struct: "pwr_flash",
      type: "uni",
      name: "pwrmgr",
      act:  "req",
      package: "pwrmgr_pkg"
    },

    { struct: "keymgr_flash",
      type: "uni",
      name: "keymgr",
      act: "req",
      package: "flash_ctrl_pkg"
    }

    { struct: "ast_obs_ctrl",
      type: "uni",
      name: "obs_ctrl",
      act: "rcv",
      package: "ast_pkg"
    }

    { struct: "logic",
      type: "uni",
      name: "fla_obs",
      act: "req",
      width: "8",
      package: ""
    }

  ],
  countermeasures: [
    { name: "REG.BUS.INTEGRITY",
      desc: '''
        End-to-end bus integrity scheme.
        Since there are multiple access points for flash, please see
        Transmission Integrity Faults in the documentation for more details.

        The bus integrity scheme for flash is different from other comportable modules.
      '''
    }
    { name: "HOST.BUS.INTEGRITY",
      desc: '''
        End-to-end bus integrity scheme.
        Since there are multiple access points for flash, please see
        Transmission Integrity Faults in the documentation for more details.

        The bus integrity scheme for flash is different from other comportable modules.
      '''
    }
    { name: "MEM.BUS.INTEGRITY",
      desc: '''
        End-to-end bus integrity scheme.
        Since there are multiple access points for flash, please see
        Transmission Integrity Faults in the documentation for more details.

        The bus integrity scheme for flash is different from other comportable modules.
      '''
    }
    { name: "SCRAMBLE.KEY.SIDELOAD",
      desc: "The scrambling key is sideloaded from OTP and thus unreadable by SW."
    }
    { name: "LC_CTRL.INTERSIG.MUBI",
      desc: '''
        Life cycle control signals are used control information partition access
        and flash debug access. See secret information partition, isolated information partitions
        and jtag connection in documentation for more details.
      '''
    }
    { name: "CTRL.CONFIG.REGWEN",
      desc: "Configurations cannot be changed when an operation is ongoing."
    }
    { name: "DATA_REGIONS.CONFIG.REGWEN",
      desc: "Each data region has a configurable regwen."
    }
    { name: "DATA_REGIONS.CONFIG.SHADOW",
      desc: "Data region configuration is shadowed."
    }
    { name: "INFO_REGIONS.CONFIG.REGWEN",
      desc: "Each info page of each type in each bank has separate regwen."
    }
    { name: "INFO_REGIONS.CONFIG.SHADOW",
      desc: "Each info page is shadowed."
    }
    { name: "BANK.CONFIG.REGWEN",
      desc: "Each bank has separate regwen for bank erase."
    }
    { name: "BANK.CONFIG.SHADOW",
      desc: "Each bank has separate regwen for bank erase."
    }
    { name: "MEM.CTRL.GLOBAL_ESC",
      desc: "Global escalation causes memory to no longer be accessible."
    }
    { name: "MEM.CTRL.LOCAL_ESC",
      desc: '''
        A subset of fatal errors cause memory to no longer be accessible.
        This subset is defined in !!STD_FAULT_STATUS.
      '''
    }
    { name: "MEM_DISABLE.CONFIG.MUBI",
      desc: '''
        Software control for flash disable is multibit.
        The register is !!DIS.
      '''
    }
    { name: "EXEC.CONFIG.REDUN",
      desc: '''
        Software control for flash enable is 32-bit constant.
        The register is !!EXEC.
      '''
    }
    { name: "MEM.SCRAMBLE",
      desc: '''
        The flash supports XEX scrambling.
        The cipher used is PRINCE.
        The scrambling scheme is enabled by software, please see flash scrambling in documentation for more details.
      '''
    }
    { name: "MEM.INTEGRITY",
      desc: '''
        The flash supports two layers of ECC integrity: one layer is for integrity,
        and the other layer is for reliability.
        These ECCs are enabled and disabled together by software.
        Please see Flash ECC in the documentation for more details.
      '''
    }
    { name: "RMA_ENTRY.MEM.SEC_WIPE",
      desc: "RMA entry entry wipes flash memory with random data."
    }
    { name: "CTRL.FSM.SPARSE",
      desc: '''
        RMA handling FSMs in flash_ctrl_lcmgr are sparsely encoded.
        FSM in flash_ctrl_arb is sparsely encoded.
      '''
    }
    { name: "PHY.FSM.SPARSE",
      desc: "PHY FSMs are sparsely encoded."
    }
    { name: "PHY_PROG.FSM.SPARSE",
      desc: "PHY program FSMs are sparsely encoded."
    }
    { name: "CTR.REDUN",
      desc: '''
        flash_ctrl_lcmgr handling counters are redundantly encoded.
        This includes seed count and address count used during seed reading phase,
        as well as word count, page count and wipe index in RMA entry phase.
      '''
    }
    { name: "PHY_ARBITER.CTRL.REDUN",
      desc: '''
        The phy arbiter for controller and host is redundant.
        The arbiter has two instance underneath that are constantly compared to each other.
      '''
    }
    { name: "PHY_HOST_GRANT.CTRL.CONSISTENCY",
      desc: '''
        The host grant is consistency checked.
        If the host is ever granted with info partition access, it is an error.
        If the host is ever granted at the same time as a program/erase operation, it is an error.
      '''
    }
    { name: "PHY_ACK.CTRL.CONSISTENCY",
      desc: '''
        If the host or controller ever receive an unexpeced transaction acknowledge, it is an error.
      '''
    }
    { name: "FIFO.CTR.REDUN",
      desc: "The FIFO pointers of several FIFOs are implemented with duplicate counters."
    }
    { name: "MEM_TL_LC_GATE.FSM.SPARSE",
      desc: "The control FSM inside the TL-UL gating primitive is sparsely encoded."
    }
    { name: "PROG_TL_LC_GATE.FSM.SPARSE",
      desc: "The control FSM inside the TL-UL gating primitive is sparsely encoded."
    }
  ]

  scan: "true",       // Enable `scanmode_i` port
  scan_en: "true",    // Enable `scan_en_i` port
  scan_reset: "true", // Enable `scan_rst_ni` port
  param_list: [
    // The reg parameters can be modified directly through top_*.hjson.
    // The template will automatically propagate the appropriate values.

    // Random netlist constants
    { name:      "RndCnstAddrKey",
      desc:      "Compile-time random bits for default address key",
      type:      "flash_ctrl_pkg::flash_key_t"
      randcount: "128",
      randtype:  "data", // randomize randcount databits
    },
    { name:      "RndCnstDataKey",
      desc:      "Compile-time random bits for default data key",
      type:      "flash_ctrl_pkg::flash_key_t"
      randcount: "128",
      randtype:  "data", // randomize randcount databits
    },
    { name:      "RndCnstAllSeeds",
      desc:      "Compile-time random bits for default seeds",
      type:      "flash_ctrl_pkg::all_seeds_t"
      randcount: "512",
      randtype:  "data", // randomize randcount databits
    },
    { name:      "RndCnstLfsrSeed",
      desc:      "Compile-time random bits for initial LFSR seed",
      type:      "flash_ctrl_pkg::lfsr_seed_t"
      randcount: "32",
      randtype:  "data",
    },
    { name:      "RndCnstLfsrPerm",
      desc:      "Compile-time random permutation for LFSR output",
      type:      "flash_ctrl_pkg::lfsr_perm_t"
      randcount: "32",
      randtype:  "perm",
    },

    { name: "RegNumBanks",
      desc: "Number of flash banks",
      type: "int",
      default: "${cfg.banks}",
      local: "true"
    },

    { name: "RegPagesPerBank",
      desc: "Number of pages per bank",
      type: "int",
      default: "${cfg.pages_per_bank}",
      local: "true"
    },

    { name: "RegBusPgmResBytes",
      desc: "Program resolution window in bytes",
      type: "int",
      default: "${cfg.pgm_resolution_bytes}",
      local: "true"
    },

    { name: "RegPageWidth",
      desc: "Number of bits needed to represent the pages within a bank",
      type: "int",
      default: "${page_width}",
      local: "true"
    },

    { name: "RegBankWidth",
      desc: "Number of bits needed to represent the number of banks",
      type: "int",
      default: "${bank_width}",
      local: "true"
    },

    { name: "NumRegions",
      desc: "Number of configurable flash regions",
      type: "int",
      default: "8",
      local: "true"
    },

    // The following parameters are derived from topgen and should not be
    // directly modified.
    { name: "NumInfoTypes",
      desc: "Number of info partition types",
      type: "int",
      default: "${cfg.info_types}",
      local: "true"
    },
    % for type in range(cfg.info_types):
    { name: "NumInfos${type}",
      desc: "Number of configurable flash info pages for info type ${type}",
      type: "int",
      default: "${cfg.infos_per_bank[type]}",
      local: "true"
    },
    % endfor

    { name: "WordsPerPage",
      desc: "Number of words per page",
      type: "int",
      default: "${cfg.words_per_page}",
      local: "true"
    },

    { name: "BytesPerWord",
      desc: "Number of bytes per word",
      type: "int",
      default: "${cfg.word_bytes}",
      local: "true"
    },

    { name: "BytesPerPage",
      desc: "Number of bytes per page",
      type: "int",
      default: "${cfg.bytes_per_page}",
      local: "true"
    },

    { name: "BytesPerBank",
      desc: "Number of bytes per bank",
      type: "int",
      default: "${cfg.bytes_per_bank}",
      local: "true"
    },

    // hex value of 0xa26a38f7
    { name:      "ExecEn",
      desc:      "Constant value that enables flash execution",
      type:      "int unsigned"
      default:   "${int("0xa26a38f7", 16)}",
      local:     "true"
    },

    { name:      "SecScrambleEn",
      desc:      "Compile-time option to enable flash scrambling",
      type:      "bit",
      default:   "1",
      local:     "false",
      expose:    "true",
    },

    // Program FIFO depth
    { name:      "ProgFifoDepth",
      desc:      "Depth of program fifo",
      type:      "int"
      default:   "${max_fifo_depth}",
      local:     "false",
      expose:    "true"
    },

    { name:      "RdFifoDepth",
      desc:      "Depth of read fifo",
      type:      "int"
      default:   "${max_fifo_depth}",
      local:     "false",
      expose:    "true"
    },

    // Maximum FIFO depth allowed
    { name:      "MaxFifoDepth",
      desc:      "Maximum depth for read / program fifos",
      type:      "int"
      default:   "${max_fifo_depth}",
    },

    { name:      "MaxFifoWidth",
      desc:      "Maximum depth for read / program fifos",
      type:      "int"
      default:   "${max_fifo_width}",
    },
  ],

  regwidth: "32",
  registers: {
    core: [
      { name: "DIS",
        desc: "Disable flash functionality",
        swaccess: "rw0c",
        hwaccess: "hro",
        fields: [
          { bits: "3:0",
            name: "VAL",
            mubi: true,
            desc: '''
               Disables flash functionality completely.
               This is a shortcut mechanism used by the software to completely
               kill flash in case of emergency.

               Since this register is rw0c instead of rw, to disable, write any value in the form of
               0xxx or xxx0, where x could be either 0 or 1.

              '''
            resval: false,
          },
        ]
        tags: [// Dont touch disable, it has several side effects on the system
               "excl:CsrAllTests:CsrExclWrite"],
      },

      { name: "EXEC",
        desc: "Controls whether flash can be used for code execution fetches",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "31:0",
            name: "EN",
            desc: '''
              A value of 0xa26a38f7 allows flash to be used for code execution.
              Any other value prevents code execution.
            '''
            resval: 0
          },
        ]
      },

      { name: "INIT",
        desc: "Controller init register",
        swaccess: "rw1s",
        hwaccess: "hro",
        fields: [
          { bits: "0",
            name: "VAL",
            desc: '''
              Initializes the flash controller.

              During the initialization process, the flash controller requests the address and data
              scramble keys and reads out the root seeds stored in flash before allowing other usage
              of the flash controller.

              When the initialization sequence is complete, the flash read buffers are enabled
              and turned on.
              '''
            resval: "0"
            tags: [// Dont init flash, it has several side effects on the status bits
                   "excl:CsrAllTests:CsrExclWrite"],
          },
        ]
      },

      { name: "CTRL_REGWEN",
        swaccess: "ro",
        hwaccess: "hwo",
        hwext: "true",
        desc: '''
        Controls the configurability of the !!CONTROL register.

        This register ensures the contents of !!CONTROL cannot be changed by software once a flash
        operation has begun.

        It unlocks whenever the existing flash operation completes, regardless of success or error.
        ''',

        fields: [
          { bits: "0",
            name: "EN",
            desc: '''
              Configuration enable.

              This bit defaults to 1 and is set to 0 by hardware when flash operation is initiated.
              When the controller completes the flash operation, this bit is set
              back to 1 to allow software configuration of !!CONTROL
            ''',
            resval: "1",
          },
        ]
        tags: [// This regwen is completely under HW management and thus cannot be manipulated
               // by software.
               "excl:CsrNonInitTests:CsrExclCheck"]
      },


      { name: "CONTROL",
        desc: "Control register",
        regwen: "CTRL_REGWEN",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "0",
            hwaccess: "hrw",
            name: "START",
            desc: '''
              Start flash transaction.  This bit shall only be set at the same time or after the other
              fields of the !!CONTROL register and !!ADDR have been programmed.
              '''
            resval: "0"
            tags: [// Dont enable flash - it causes several side-effects.
                   "excl:CsrAllTests:CsrExclWrite"],
          },
          { bits: "5:4",
            name: "OP",
            desc: "Flash operation selection",
            resval: "0"
            enum: [
              { value: "0",
                name: "Read",
                desc: '''
                  Flash Read.

                  Read desired number of flash words
                  '''
              },
              { value: "1",
                name: "Prog",
                desc: '''
                  Flash Program.

                  Program desired number of flash words
                  '''
              },
              { value: "2",
                name: "Erase",
                desc: '''
                  Flash Erase Operation.

                  See ERASE_SEL for details on erase operation
                  '''
              },
            ]
          },

          { bits: "6",
            name: "PROG_SEL",
            desc: "Flash program operation type selection",
            resval: "0"
            enum: [
              { value: "0",
                name: "Normal program",
                desc: '''
                  Normal program operation to the flash
                  '''
              },
              { value: "1",
                name: "Program repair",
                desc: '''
                  Repair program operation to the flash.  Whether this is actually
                  supported depends on the underlying flash memory.
                  '''
              },
            ]
          },

          { bits: "7",
            name: "ERASE_SEL",
            desc: "Flash erase operation type selection",
            resval: "0"
            enum: [
              { value: "0",
                name: "Page Erase",
                desc: '''
                  Erase 1 page of flash
                  '''
              },
              { value: "1",
                name: "Bank Erase",
                desc: '''
                  Erase 1 bank of flash
                  '''
              },
            ]
          },
          { bits: "8",
            name: "PARTITION_SEL",
            desc: '''
              When doing a read, program or page erase operation, selects either info or data partition for operation.
              When 0, select data partition - this is the portion of flash that is accessible both by the host and by the controller.
              When 1, select info partition - this is the portion of flash that is only accessible by the controller.

              When doing a bank erase operation, selects info partition also for erase.
              When 0, bank erase only erases data partition.
              When 1, bank erase erases data partition and info partition.
            '''
            resval: "0"
          },
          { bits: "${9 + info_type_width -1}:9",
            name: "INFO_SEL",
            desc: '''
              Informational partions can have multiple types.

              This field selects the info type to be accessed.
            '''
            resval: "0"
          },
          { bits: "27:16",
            name: "NUM",
            desc: '''
	      One fewer than the number of bus words the flash operation should read or program.
	      For example, to read 10 words, software should program this field with the value 9.
	    '''
            resval: "0"
          },
        ]
      },
      { name: "ADDR",
        desc: "Address for flash operation",
        swaccess: "rw",
        hwaccess: "hro",
        regwen: "CTRL_REGWEN",
        resval: "0",
        fields: [
          { bits: "${total_byte_width-1}:0",
            name: "START",
            desc: '''
              Start address of a flash transaction.  This is a byte address relative to the flash
              only.  Ie, an address of 0 will access address 0 of the requested partition.

              For read operations, the flash controller will truncate to the closest, lower word
              aligned address.  For example, if 0x13 is supplied, the controller will perform a
              read at address 0x10.

              Program operations behave similarly, the controller does not have read modified write
              support.

              For page erases, the controller will truncate to the closest lower page aligned
              address.  Similarly for bank erases, the controller will truncate to the closest
              lower bank aligned address.
              '''
            resval: "0"
          },
        ]
      },

      // Program type
      { name: "PROG_TYPE_EN",
        desc: "Enable different program types",
        regwen: "CTRL_REGWEN",
        swaccess: "rw0c",
        hwaccess: "hro",
        fields: [
          { bits: "0",
            resval: "1",
            name: "NORMAL",
            desc: '''
              Normal prog type available
              '''
          },
          { bits: "1",
            resval: "1",
            name: "REPAIR",
            desc: '''
              Repair prog type available
              '''
          },
        ]
      },

      // erase suspend support
      { name: "ERASE_SUSPEND",
        desc: "Suspend erase",
        swaccess: "rw",
        hwaccess: "hrw",
        fields: [
          { bits: "0",
            resval: "0",
            name: "REQ",
            desc: '''
              When 1, request erase suspend.
              If no erase ongoing, the request is immediately cleared by hardware
              If erase ongoing, the request is fed to the flash_phy and cleared when the suspend is handled.
              '''
          },
        ],
        tags: [// Erase suspend must be directly tested
          "excl:CsrAllTests:CsrExclWrite"],
      },

      // Data partition memory properties region setup
      { multireg: {
          cname: "FLASH_CTRL",
          name: "REGION_CFG_REGWEN"
          desc: "Memory region registers configuration enable.",
          count: "NumRegions",
          swaccess: "rw0c",
          hwaccess: "none",
          compact: false,
          fields: [
              { bits: "0",
                name: "REGION",
                resval: "1"
                desc: "Region register write enable.  Once set to 0, it can longer be configured to 1",
                enum: [
                  { value: "0",
                    name: "Region locked",
                    desc: '''
                      Region can no longer be configured until next reset
                      '''
                  },
                  { value: "1",
                    name: "Region enabled",
                    desc: '''
                      Region can be configured
                      '''
                  },
                ]
              },
          ],
        },
      },

      { multireg: {
          cname: "FLASH_CTRL",
          name: "MP_REGION_CFG",
          desc: "Memory property configuration for data partition",
          count: "NumRegions",
          swaccess: "rw",
          hwaccess: "hro",
          regwen: "REGION_CFG_REGWEN",
          regwen_multi: true,
          update_err_alert: "recov_err",
          storage_err_alert: "fatal_err",
          fields: [
              { bits: "3:0",
                name: "EN",
                mubi: true,
                desc: '''
                  Region enabled, following fields apply.
                  If region is disabled, it is not matched against any incoming transaction.
                ''',
                resval: false
              },
              { bits: "7:4",
                name: "RD_EN",
                mubi: true,
                desc: '''
                  Region can be read
                ''',
                resval: false
              },
              { bits: "11:8",
                name: "PROG_EN",
                mubi: true,
                desc: '''
                  Region can be programmed
                ''',
                resval: false
              }
              { bits: "15:12",
                name: "ERASE_EN",
                mubi: true,
                desc: '''
                  Region can be erased
                ''',
                resval: false
              }
              { bits: "19:16",
                name: "SCRAMBLE_EN",
                mubi: true,
                desc: '''
                  Region is scramble enabled.
                ''',
                resval: false
              }
              { bits: "23:20",
                name: "ECC_EN",
                mubi: true,
                desc: '''
                  Region is integrity checked and reliability ECC enabled.
                ''',
                resval: false
              }
              { bits: "27:24",
                name: "HE_EN",
                mubi: true,
                desc: '''
                  Region is high endurance enabled.
                ''',
                resval: false
              }
          ],
        },
      },

      { multireg: {
          cname: "FLASH_CTRL",
          name: "MP_REGION",
          desc: "Memory base and size configuration for data partition",
          count: "NumRegions",
          swaccess: "rw",
          hwaccess: "hro",
          regwen: "REGION_CFG_REGWEN",
          regwen_multi: true,
          update_err_alert: "recov_err",
          storage_err_alert: "fatal_err",
          fields: [
            { bits: "${page_idx_width-1}:0",
              name: "BASE",
              desc: '''
                Region base page. Note the granularity is page, not byte or word
              ''',
              resval: "0"
            },
            { bits: "${page_num_width + page_idx_width - 1}:${page_idx_width}",
              name: "SIZE",
              desc: '''
                Region size in number of pages.
                For example, if base is 0 and size is 1, then the region is defined by page 0.
                If base is 0 and size is 2, then the region is defined by pages 0 and 1.
              ''',
              resval: "0"
            },
          ],
        },
      },

      // Default region properties for data partition
      { name: "DEFAULT_REGION",
        desc: "Default region properties",
        swaccess: "rw",
        hwaccess: "hro",
        update_err_alert: "recov_err",
        storage_err_alert: "fatal_err",
        fields: [
          { bits: "3:0",
            name: "RD_EN",
            mubi: true,
            desc: '''
              Region can be read
            ''',
            resval: false
          },
          { bits: "7:4",
            name: "PROG_EN",
            mubi: true,
            desc: '''
              Region can be programmed
            ''',
            resval: false
          }
          { bits: "11:8",
            name: "ERASE_EN",
            mubi: true,
            desc: '''
              Region can be erased
            ''',
            resval: false
          }
          { bits: "15:12",
            name: "SCRAMBLE_EN",
            mubi: true,
            desc: '''
              Region is scramble enabled.
            ''',
            resval: false
          }
          { bits: "19:16",
            name: "ECC_EN",
            mubi: true,
            desc: '''
              Region is ECC enabled (both integrity and reliability ECC).
            ''',
            resval: false
          }
          { bits: "23:20",
            name: "HE_EN",
            mubi: true,
            desc: '''
              Region is high endurance enabled.
            ''',
            resval: false
          }
        ]
      },

      // Info partition memory properties setup
      % for bank in range(cfg.banks):
      %   for idx in range(cfg.info_types):
      { multireg: {
          cname: "FLASH_CTRL",
          name: "BANK${bank}_INFO${idx}_REGWEN"
          desc: "Memory region registers configuration enable.",
          count: "NumInfos${idx}",
          swaccess: "rw0c",
          hwaccess: "none",
          compact: false,
          fields: [
              { bits: "0",
                name: "REGION",
                resval: "1"
                desc: "Info${idx} page write enable.  Once set to 0, it can longer be configured to 1",
                enum: [
                  { value: "0",
                    name: "Page locked",
                    desc: '''
                      Region can no longer be configured until next reset
                      '''
                  },
                  { value: "1",
                    name: "Page enabled",
                    desc: '''
                      Region can be configured
                      '''
                  },
                ]
              },
          ],
        },
      },

      { multireg: {
          cname: "FLASH_CTRL",
          name: "BANK${bank}_INFO${idx}_PAGE_CFG",
          desc: '''
                  Memory property configuration for info partition in bank${bank},
                  Unlike data partition, each page is individually configured.
                '''
          count: "NumInfos${idx}",
          swaccess: "rw",
          hwaccess: "hro",
          regwen: "BANK${bank}_INFO${idx}_REGWEN",
          regwen_multi: true,
          update_err_alert: "recov_err",
          storage_err_alert: "fatal_err",
          fields: [
            { bits: "3:0",
              name: "EN",
              mubi: true,
              desc: '''
                Region enabled, following fields apply
              ''',
              resval: false
            },
            { bits: "7:4",
              name: "RD_EN",
              mubi: true,
              desc: '''
                Region can be read
              ''',
              resval: false
            },
            { bits: "11:8",
              name: "PROG_EN",
              mubi: true,
              desc: '''
                Region can be programmed
              ''',
              resval: false
            }
            { bits: "15:12",
              name: "ERASE_EN",
              mubi: true,
              desc: '''
                Region can be erased
              ''',
              resval: false
            }
            { bits: "19:16",
              name: "SCRAMBLE_EN",
              mubi: true,
              desc: '''
                Region is scramble enabled.
              ''',
              resval: false
            }
            { bits: "23:20",
              name: "ECC_EN",
              mubi: true,
              desc: '''
                Region is ECC enabled (both integrity and reliability ECC).
              ''',
              resval: false
            }
            { bits: "27:24",
              name: "HE_EN",
              mubi: true,
              desc: '''
                Region is high endurance enabled.
              ''',
              resval: false
            }
          ],
        },
      },
      %   endfor
      % endfor

      { name: "HW_INFO_CFG_OVERRIDE",
        desc: "HW interface info configuration rule overrides",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "3:0",
            name: "SCRAMBLE_DIS",
            mubi: true,
            desc: '''
              The hardwired hardware info configuration rules for scramble enable are logically AND'd with
              this field.
              If the hardware rules hardwires scramble to enable, we can disable via software if needed.

              By default this field is false.
            ''',
            resval: false
          }
          { bits: "7:4",
            name: "ECC_DIS",
            mubi: true,
            desc: '''
              The hardwired hardware info configuration rules for ECC enable are logically AND'd with
              this field.
              If the hardware rules hardwires ECC to enable, we can disable via software if needed.

              By default this field is false.
            ''',
            resval: false
          }
        ]
      },

      { name: "BANK_CFG_REGWEN"
        desc: "Bank configuration registers configuration enable.",
        swaccess: "rw0c",
        hwaccess: "none",
        fields: [
            { bits: "0",
              name: "BANK",
              resval: "1"
              desc: "Bank register write enable.  Once set to 0, it can longer be configured to 1",
              enum: [
                { value: "0",
                  name: "Bank locked",
                  desc: '''
                    Bank can no longer be configured until next reset
                    '''
                },
                { value: "1",
                  name: "Bank enabled",
                  desc: '''
                    Bank can be configured
                    '''
                },
              ]
            },
        ],
      },

      { multireg: {
          cname: "FLASH_CTRL",
          name: "MP_BANK_CFG_SHADOWED",
          desc: "Memory properties bank configuration",
          count: "RegNumBanks",
          swaccess: "rw",
          hwaccess: "hro",
          regwen: "BANK_CFG_REGWEN",
          shadowed: "true",
          update_err_alert: "recov_err",
          storage_err_alert: "fatal_std_err",
          fields: [
              { bits: "0",
                name: "ERASE_EN",
                desc: '''
                  Bank wide erase enable
                ''',
                resval: "0"
              },
          ],
        },
      },

      { name: "OP_STATUS",
        desc: "Flash Operation Status",
        swaccess: "rw",
        hwaccess: "hwo",
        fields: [
          { bits: "0", name: "done",
            desc: "Flash operation done. Set by HW, cleared by SW" },
          { bits: "1", name: "err",
            desc: "Flash operation error. Set by HW, cleared by SW. See !!ERR_CODE for more details."},
        ]
      },

      { name: "STATUS",
        desc: "Flash Controller Status",
        swaccess: "ro",
        hwaccess: "hwo",
        fields: [
          { bits: "0",    name: "rd_full",    desc: "Flash read FIFO full, software must consume data"},
          { bits: "1",    name: "rd_empty",   desc: "Flash read FIFO empty", resval: "1"},
          { bits: "2",    name: "prog_full",  desc: "Flash program FIFO full"},
          { bits: "3",    name: "prog_empty", desc: "Flash program FIFO empty, software must provide data", resval: "1"},
          { bits: "4",    name: "init_wip",   desc: "Flash controller undergoing init, inclusive of phy init"
            tags: [ // Bit changes immediately after start from reset value to 1b1 due to initialization
            "excl:CsrAllTests:CsrExclAll"]
          }
          { bits: "5",    name: "initialized",desc: "Flash controller initialized"
            tags: [ // Bit changes immediately after start from reset value to 1b1 due to initialization
            "excl:CsrAllTests:CsrExclAll"]
          },
        ]
      },

      { name: "DEBUG_STATE",
        desc: "Current flash fsm state",
        swaccess: "ro",
        hwaccess: "hwo",
        hwext: "true"
        fields: [
          { bits: "10:0",
            name: "lcmgr_state",
            desc: "Current lcmgr interface staet ",
            tags: [ // Bit changes immediately after start from reset value to 1b1 due to initialization
            "excl:CsrAllTests:CsrExclAll"]
          }
        ]
      },

      { name: "ERR_CODE",
        desc: '''
          Flash error code register.
          This register tabulates detailed error status of the flash.
          This is separate from !!OP_STATUS, which is used to indicate the current state of the software initiated
          flash operation.

          Note, all errors in this register are considered recoverable errors, ie, errors that could have been
          generated by software.
        '''
        swaccess: "rw1c",
        hwaccess: "hwo",
        fields: [
          { bits: "0",
            name: "op_err",
            desc: '''
              Software has supplied an undefined operation.
              See !!CONTROL.OP for list of valid operations.
            '''
          },
          { bits: "1",
            name: "mp_err",
            desc: '''
              Flash access has encountered an access permission error.
              Please see !!ERR_ADDR for exact address.
              This is a synchronous error.
            '''
          },
          { bits: "2",
            name: "rd_err",
            desc: '''
              Flash read has an error.
              This could be a reliability ECC error or an storage integrity error
              encountered during a software issued controller read, see !!STD_FAULT_STATUS.
              See !!ERR_ADDR for exact address.
              This is a synchronous error.
            '''
          },
          { bits: "3",
            name: "prog_err",
            desc: '''
              Flash program has an error.
              This could be a program integrity error, see !!STD_FAULT_STATUS.
              This is a synchronous error.
            '''
          },
          { bits: "4",
            name: "prog_win_err",
            desc: '''
              Flash program has a window resolution error.  Ie, the start of program
              and end of program are in different windows.  Please check !!ERR_ADDR.
              This is a synchronous error.
            '''
          },
          { bits: "5",
            name: "prog_type_err",
            desc: '''
              Flash program selected unavailable type, see !!PROG_TYPE_EN.
              This is a synchronous error.
            '''
          },
          { bits: "6",
            name: "update_err",
            desc: '''
              A shadow register encountered an update error.
              This is an asynchronous error.
            '''
          },
          { bits: "7",
            name: "macro_err",
            desc: '''
              A recoverable error has been encountered in the flash macro.
              Please read the flash macro status registers for more details.
            '''
          },
        ]
      },

      { name: "STD_FAULT_STATUS",
        desc: '''
          This register tabulates standard fault status of the flash.

          These represent errors that occur in the standard structures of the design.
          For example fsm integrity, counter integrity and tlul integrity.
        '''
        swaccess: "ro",
        hwaccess: "hrw",
        fields: [
          { bits: "0",
            name: "reg_intg_err",
            desc: '''
              The flash controller encountered a register integrity error.
            '''
          },
          { bits: "1",
            name: "prog_intg_err",
            desc: '''
              The flash controller encountered a program data transmission integrity error.
            '''
          },
          { bits: "2",
            name: "lcmgr_err",
            desc: '''
              The life cycle management interface has encountered a fatal error.
              The error is either an FSM sparse encoding error or a count error.
              '''
          },
          { bits: "3",
            name: "lcmgr_intg_err",
            desc: '''
              The life cycle management interface has encountered a transmission
              integrity error.  This is an integrity error on the generated integrity
              during a life cycle management interface read.
            '''
          },
          { bits: "4",
            name: "arb_fsm_err",
            desc: '''
              The arbiter fsm has encountered a sparse encoding error.
              '''
          },
          { bits: "5",
            name: "storage_err",
            desc: '''
              A shadow register encountered a storage error.
            '''
          },
          { bits: "6",
            name: "phy_fsm_err",
            desc: '''
              A flash phy fsm has encountered a sparse encoding error.
            '''
          },
          { bits: "7",
            name: "ctrl_cnt_err",
            desc: '''
              Flash ctrl read/prog has encountered a count error.
            '''
          },
          { bits: "8",
            name: "fifo_err",
            desc: '''
              Flash primitive fifo's have encountered a count error.
            '''
          },
        ]
      },

      { name: "FAULT_STATUS",
        desc: '''
          This register tabulates customized fault status of the flash.

          These are errors that are impossible to have been caused by software or unrecoverable
          in nature.
        '''
        swaccess: "ro",
        hwaccess: "hrw",
        fields: [
          { bits: "0",
            name: "op_err",
            desc: '''
              The flash life cycle management interface has supplied an undefined operation.
              See !!CONTROL.OP for list of valid operations.
            '''
          },
          { bits: "1",
            name: "mp_err",
            desc: '''
              The flash life cycle management interface encountered a memory permission error.
            '''
          },
          { bits: "2",
            name: "rd_err",
            desc: '''
              The flash life cycle management interface encountered a read error.
              This could be a reliability ECC error or an integrity ECC error
              encountered during a read, see !!STD_FAULT_STATUS for more details.
            '''
          },
          { bits: "3",
            name: "prog_err",
            desc: '''
              The flash life cycle management interface encountered a program error.
              This could be a program integirty eror, see !!STD_FAULT_STATUS for more details.
            '''
          },
          { bits: "4",
            name: "prog_win_err",
            desc: '''
              The flash life cycle management interface encountered a program resolution error.
            '''
          },
          { bits: "5",
            name: "prog_type_err",
            desc: '''
              The flash life cycle management interface encountered a program type error.
              A program type not supported by the flash macro was issued.
            '''
          },
          { bits: "6",
            name: "seed_err",
            desc: '''
              The seed reading process encountered an unexpected error.
            '''
          },
          { bits: "7",
            name: "phy_relbl_err",
            desc: '''
              The flash macro encountered a storage reliability ECC error.
            '''
          },
          { bits: "8",
            name: "phy_storage_err",
            desc: '''
              The flash macro encountered a storage integrity ECC error.
            '''
          },
          { bits: "9",
            name: "spurious_ack",
            desc: '''
              The flash emitted an unexpected acknowledgement.
            '''
          },
          { bits: "10",
            name: "arb_err",
            desc: '''
              The phy arbiter encountered inconsistent results.
            '''
          },
          { bits: "11",
            name: "host_gnt_err",
            desc: '''
              A host transaction was granted with illegal properties.
            '''
          },
        ]
      },

      { name: "ERR_ADDR",
        desc: "Synchronous error address",
        swaccess: "ro",
        hwaccess: "hwo",
        fields: [
          { bits: "${total_byte_width-1}:0",
            resval: 0,
          },
        ]
      },

      { multireg: {
          cname: "ECC_SINGLE_ERR",
          name: "ECC_SINGLE_ERR_CNT",
          desc: "Total number of single bit ECC error count",
          count: "RegNumBanks",
          swaccess: "rw",
          hwaccess: "hrw",
          fields: [
            { bits: "7:0",
              desc: "This count will not wrap when saturated",
              resval: 0,
            },
          ]
        }
      },

      { multireg: {
          cname: "ECC_SINGLE_ERR",
          name: "ECC_SINGLE_ERR_ADDR",
          desc: "Latest address of ECC single err",
          count: "RegNumBanks",
          swaccess: "ro",
          hwaccess: "hwo",
          compact: false,
          fields: [
            { bits: "${total_byte_width-1}:0",
              desc: "Latest single error address for this bank",
              resval: 0,
            },
          ]
        }
      }

      { name: "PHY_ALERT_CFG",
        desc: "Phy alert configuration",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "0",
            name: "alert_ack",
            desc: "Acknowledge flash phy alert"
          },
          { bits: "1",
            name: "alert_trig",
            desc: "Trigger flash phy alert"
          }
        ]
        tags: [ // alert triggers should be tested by directed tests
               "excl:CsrAllTests:CsrExclWrite"]
      },

      { name: "PHY_STATUS",
        desc: "Flash Phy Status",
        swaccess: "ro",
        hwaccess: "hwo",
        fields: [
          { bits: "0",
            name: "init_wip",
            desc: "Flash phy controller initializing"
            tags: [ // Bit changes immediately after start from reset value to 1b1 due to initialization
            "excl:CsrAllTests:CsrExclAll"]
          },
          { bits: "1",
            name: "prog_normal_avail",
            resval: "0x1",
            desc: "Normal program supported"
          },
          { bits: "2",
            name: "prog_repair_avail",
            resval: "0x1",
            desc: "Program repair supported"
          },
        ]
      },

      { name: "Scratch",
        desc: "Flash Controller Scratch",
        swaccess: "rw",
        fields: [
          { bits: "31:0", name: "data",  desc: "Flash ctrl scratch register" },
        ]
      },

      { name: "FIFO_LVL",
        desc: "Programmable depth where FIFOs should generate interrupts",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "${max_fifo_width-1}:0",
            name: "PROG",
            desc: '''
              When the program FIFO drains to this level, trigger an interrupt.
              Default value is set such that interrupt does not trigger at reset.
              '''
            resval: "0xF"
          },
          { bits: "${8 + max_fifo_width - 1}:8",
            name: "RD",
            desc: '''
              When the read FIFO fills to this level, trigger an interrupt.
              Default value is set such that interrupt does not trigger at reset.
              '''
            resval: "0xF"
          },
        ]
      }

      { name: "FIFO_RST",
        desc: "Reset for flash controller FIFOs",
        swaccess: "rw",
        hwaccess: "hro",
        resval: "0",
        fields: [
          { bits: "0",
            name: "EN",
            desc: '''
              Active high resets for both program and read FIFOs.  This is especially useful after the controller
              encounters an error of some kind.
              This bit will hold the FIFO in reset as long as it is set.
              '''
            resval: "0"
          },
        ]
      },

      { name: "CURR_FIFO_LVL",
        desc: "Current program and read fifo depth",
        swaccess: "ro",
        hwaccess: "hwo",
        hwext: "true",
        fields: [
          { bits: "${max_fifo_width-1}:0",
            name: "PROG",
            desc: '''
              Current program fifo depth
              '''
            resval: "0x0"
          },
          { bits: "${8 + max_fifo_width - 1}:8",
            name: "RD",
            desc: '''
              Current read fifo depth
              '''
            resval: "0x0"
          },
        ]
      }

      { window: {
          name: "prog_fifo",
          items: "1",
          validbits: "32",
          data-intg-passthru: "true",
          byte-write: "false",
          unusual: "false"
          swaccess: "wo",
          desc: '''
            Flash program FIFO.

            The FIFO is 16 entries of 4B flash words. This FIFO can only be programmed
            by software after a program operation has been initiated via the !!CONTROL register.
            This ensures accidental programming of the program FIFO cannot lock up the system.
            '''
        },
      },

      { window: {
          name: "rd_fifo",
          items: "1",
          validbits: "32",
          data-intg-passthru: "true",
          byte-write: "false",
          unusual: "false"
          swaccess: "ro",
          desc: '''
            Flash read FIFO.

            The FIFO is 16 entries of 4B flash words
            '''
        },
      },
    ],

    prim: [
      {
        name: "CSR0_REGWEN",
        desc: "",
        fields: [
          {
            bits: "0",
            name: "field0",
            swaccess: "rw0c",
            hwaccess: "none",
            resval: "1",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False"
      },
      {
        name: "CSR1",
        desc: "",
        fields: [
          {
            bits: "7:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "12:8",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR2",
        desc: "",
        fields: [
          {
            bits: "0",
            name: "field0",
            swaccess: "rw1c",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "1",
            name: "field1",
            swaccess: "rw1c",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "2",
            name: "field2",
            swaccess: "rw1c",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "3",
            name: "field3",
            swaccess: "rw",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "4",
            name: "field4",
            swaccess: "rw1c",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "5",
            name: "field5",
            swaccess: "rw1c",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "6",
            name: "field6",
            swaccess: "rw1c",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "7",
            name: "field7",
            swaccess: "rw",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False"
      },
      {
        name: "CSR3",
        desc: "",
        fields: [
          {
            bits: "3:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "7:4",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "10:8",
            name: "field2",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "13:11",
            name: "field3",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "16:14",
            name: "field4",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "19:17",
            name: "field5",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "20",
            name: "field6",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "23:21",
            name: "field7",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "25:24",
            name: "field8",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "27:26",
            name: "field9",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR4",
        desc: "",
        fields: [
          {
            bits: "2:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "5:3",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "8:6",
            name: "field2",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "11:9",
            name: "field3",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR5",
        desc: "",
        fields: [
          {
            bits: "2:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "4:3",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "13:5",
            name: "field2",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "18:14",
            name: "field3",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "22:19",
            name: "field4",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR6",
        desc: "",
        fields: [
          {
            bits: "2:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "5:3",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "13:6",
            name: "field2",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "16:14",
            name: "field3",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "18:17",
            name: "field4",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "20:19",
            name: "field5",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "22:21",
            name: "field6",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "23",
            name: "field7",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "24",
            name: "field8",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR7",
        desc: "",
        fields: [
          {
            bits: "7:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "16:8",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR8",
        desc: "",
        fields: [
          {
            bits: "31:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR9",
        desc: "",
        fields: [
          {
            bits: "31:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR10",
        desc: "",
        fields: [
          {
            bits: "31:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR11",
        desc: "",
        fields: [
          {
            bits: "31:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR12",
        desc: "",
        fields: [
          {
            bits: "9:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR13",
        desc: "",
        fields: [
          {
            bits: "19:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "20",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR14",
        desc: "",
        fields: [
          {
            bits: "7:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "8",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR15",
        desc: "",
        fields: [
          {
            bits: "7:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "8",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR16",
        desc: "",
        fields: [
          {
            bits: "7:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "8",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR17",
        desc: "",
        fields: [
          {
            bits: "7:0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "8",
            name: "field1",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR18",
        desc: "",
        fields: [
          {
            bits: "0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR19",
        desc: "",
        fields: [
          {
            bits: "0",
            name: "field0",
            swaccess: "rw",
            hwaccess: "hro",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False",
        regwen: "CSR0_REGWEN"
      },
      {
        name: "CSR20",
        desc: "",
        fields: [
          {
            bits: "0",
            name: "field0",
            swaccess: "rw1c",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "1",
            name: "field1",
            swaccess: "rw1c",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          },
          {
            bits: "2",
            name: "field2",
            swaccess: "ro",
            hwaccess: "hrw",
            resval: "0",
            tags: [],
            desc: "",
            enum: []
          }
        ],
        hwext: "False",
        hwqe: "False",
        hwre: "False",
        tags: [],
        shadowed: "False"
      }
    ],
    mem: []
  }
}
