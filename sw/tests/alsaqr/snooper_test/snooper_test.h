// Generated register defines for cfg_regs

#ifndef _CFG_REGS_REG_DEFS_
#define _CFG_REGS_REG_DEFS_

#ifdef __cplusplus
extern "C" {
#endif
// Register width
#define CFG_REGS_PARAM_REG_WIDTH 32

// Snooper configuration register.
#define CFG_REGS_CTRL_REG_OFFSET 0x0
#define CFG_REGS_CTRL_U_MODE_BIT 0
#define CFG_REGS_CTRL_S_MODE_BIT 1
#define CFG_REGS_CTRL_M_MODE_BIT 2
#define CFG_REGS_CTRL_PC_RANGE_0_BIT 3
#define CFG_REGS_CTRL_PC_RANGE_1_BIT 4
#define CFG_REGS_CTRL_PC_RANGE_2_BIT 5
#define CFG_REGS_CTRL_PC_RANGE_3_BIT 6
#define CFG_REGS_CTRL_TRIG_PC_0_BIT 7
#define CFG_REGS_CTRL_TRIG_PC_1_BIT 8
#define CFG_REGS_CTRL_TRIG_PC_2_BIT 9
#define CFG_REGS_CTRL_TRIG_PC_3_BIT 10
#define CFG_REGS_CTRL_TRACE_MODE_MASK 0x3
#define CFG_REGS_CTRL_TRACE_MODE_OFFSET 11
#define CFG_REGS_CTRL_TRACE_MODE_FIELD \
  ((bitfield_field32_t) { .mask = CFG_REGS_CTRL_TRACE_MODE_MASK, .index = CFG_REGS_CTRL_TRACE_MODE_OFFSET })
#define CFG_REGS_CTRL_TEST_MODE_BIT 13
#define CFG_REGS_CTRL_CNT_RST_BIT 14
#define CFG_REGS_CTRL_EXCINH_BIT 15
#define CFG_REGS_CTRL_INTRINH_BIT 16
#define CFG_REGS_CTRL_TRETINH_BIT 17
#define CFG_REGS_CTRL_NTBREN_BIT 18
#define CFG_REGS_CTRL_TKBRINH_BIT 19
#define CFG_REGS_CTRL_INDCALLINH_BIT 20
#define CFG_REGS_CTRL_DIRCALLINH_BIT 21
#define CFG_REGS_CTRL_INDJMPINH_BIT 22
#define CFG_REGS_CTRL_DIRJMPINH_BIT 23
#define CFG_REGS_CTRL_CORSWAPINH_BIT 24
#define CFG_REGS_CTRL_RETINH_BIT 25
#define CFG_REGS_CTRL_INDLJMPINH_BIT 26
#define CFG_REGS_CTRL_DIRLJMPINH_BIT 27
#define CFG_REGS_CTRL_CORE_SELECT_BIT 28
#define CFG_REGS_CTRL_UNUSED_MASK 0x7
#define CFG_REGS_CTRL_UNUSED_OFFSET 29
#define CFG_REGS_CTRL_UNUSED_FIELD \
  ((bitfield_field32_t) { .mask = CFG_REGS_CTRL_UNUSED_MASK, .index = CFG_REGS_CTRL_UNUSED_OFFSET })

// First valid entry in buffer
#define CFG_REGS_BASE_REG_OFFSET 0x4

// Last valid entry in buffer
#define CFG_REGS_LAST_REG_OFFSET 0x8

// MSBs of Base PC for Range 0
#define CFG_REGS_RANGE_0_BASE_H_REG_OFFSET 0xc

// LSBs of Base PC for Range 0
#define CFG_REGS_RANGE_0_BASE_L_REG_OFFSET 0x10

// MSBs of Last PC for Range 0
#define CFG_REGS_RANGE_0_LAST_H_REG_OFFSET 0x14

// LSBs of Last PC for Range 0
#define CFG_REGS_RANGE_0_LAST_L_REG_OFFSET 0x18

// MSBs of Base PC for Range 1
#define CFG_REGS_RANGE_1_BASE_H_REG_OFFSET 0x1c

// LSBs of Base PC for Range 1
#define CFG_REGS_RANGE_1_BASE_L_REG_OFFSET 0x20

// MSBs of Last PC for Range 1
#define CFG_REGS_RANGE_1_LAST_H_REG_OFFSET 0x24

// LSBs of Last PC for Range 1
#define CFG_REGS_RANGE_1_LAST_L_REG_OFFSET 0x28

// MSBs of Base PC for Range 2
#define CFG_REGS_RANGE_2_BASE_H_REG_OFFSET 0x2c

// LSBs of Base PC for Range 2
#define CFG_REGS_RANGE_2_BASE_L_REG_OFFSET 0x30

// MSBs of Last PC for Range 2
#define CFG_REGS_RANGE_2_LAST_H_REG_OFFSET 0x34

// LSBs of Last PC for Range 2
#define CFG_REGS_RANGE_2_LAST_L_REG_OFFSET 0x38

// MSBs of Base PC for Range 3
#define CFG_REGS_RANGE_3_BASE_H_REG_OFFSET 0x3c

// LSBs of Base PC for Range 3
#define CFG_REGS_RANGE_3_BASE_L_REG_OFFSET 0x40

// MSBs of Last PC for Range 3
#define CFG_REGS_RANGE_3_LAST_H_REG_OFFSET 0x44

// LSBs of Last PC for Range 3
#define CFG_REGS_RANGE_3_LAST_L_REG_OFFSET 0x48

// PC trigger 0 MSB
#define CFG_REGS_TRIG_PC0_H_REG_OFFSET 0x4c

// PC trigger 0 LSB
#define CFG_REGS_TRIG_PC0_L_REG_OFFSET 0x50

// PC trigger 1 MSB
#define CFG_REGS_TRIG_PC1_H_REG_OFFSET 0x54

// PC trigger 1 LSB
#define CFG_REGS_TRIG_PC1_L_REG_OFFSET 0x58

// PC trigger 2 MSB
#define CFG_REGS_TRIG_PC2_H_REG_OFFSET 0x5c

// PC trigger 2 LSB
#define CFG_REGS_TRIG_PC2_L_REG_OFFSET 0x60

// PC trigger 3 MSB
#define CFG_REGS_TRIG_PC3_H_REG_OFFSET 0x64

// PC trigger 3 LSB
#define CFG_REGS_TRIG_PC3_L_REG_OFFSET 0x68

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _CFG_REGS_REG_DEFS_
// End generated register defines for cfg_regs